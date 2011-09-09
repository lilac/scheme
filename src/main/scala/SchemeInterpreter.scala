import scala.util.parsing.combinator._
import scala.collection.immutable.StringOps
import scala.collection.immutable.List
import java.io.File
import scala.util.parsing.combinator.Parsers
import scala.collection.mutable.Map
import scala.Nothing
import scala.io.Source
import java.io.FileReader
import java.io.Reader
import java.io.BufferedReader
import java.io._
import java.util.Scanner

object Utils {
  def intersperse[a] (a: => a)(xs: => List[a]): List[a] = xs match {
    case List(_) => xs
    case x :: xs => x :: a :: (intersperse(a)(xs))
    case _ => Nil
  } 
}

object SchemeInterpreter {

  object SchemeParser extends RegexParsers {
    def symbols = Set() ++ "!$%&|*+-/:<=>?@^_~#"
    def spaces = """\s+""".r
    def symbol : Parser[Char] = elem("symbol", {s => symbols contains s})
    
    def string : Parser[LispVal] = "\""~> """[^"]*""".r <~ "\"" ^^ {s => new LString(s)}
    /** Note: because the regex contains special characters([\^$.|?*+(){}),
     * \Q...\E are inserted to supress the meaning of these special characters.
     */
    def atom : Parser[LispVal] = """[a-zA-Z\Q!$%&|*+-/:<=>?@^_~#\E][a-zA-Z\Q!$%&|*+-/:<=>?@^_~#\E0-9]*""".r ^^ {id => id match {
      case "#t" => new Bool(true)
      case "#f" => new Bool(false)
      case _ => new Atom(id)
    }
    }
    def number : Parser[LispVal] = """\d+""".r ^^ {ds => Number(Integer.parseInt(ds)) }
    def list : Parser[LispVal] = /*rep1sep(expression, spaces)*/rep(expression) ^^ { exprs => LList(exprs) }
    //def dottedList : Parser[LispVal] = repsep(expression, spaces)~(spaces~>"."<~spaces)~expression ^^ { case head~"."~tail => new DottedList(head, tail) }
    /** Note: We don't need to use repsep because RegexParsers will automatically
     * skip whitespace as defined by skipWhitespace at the beginning of a literal
     * and regex.
     */
    def dottedList : Parser[LispVal] = rep(expression)~"."~expression ^^ { case head~"."~tail => new DottedList(head, tail) }
    def quote : Parser[LispVal] = "'"~>expression^^ {expr => new LList(List(new Atom("quote"), expr)) }
    
    def expression : Parser[LispVal] = (atom |
    					string |
    					number |
    					quote |
    					"("~>(dottedList | list)<~")")
    
    def run[A](p: Parser[A], input: Reader): A = {
      val res = parse(p, input)
      res match {
        case Success(v, rest) => v
        case f @ Failure(msg, in) => throw ParserError(f)
      }
    }
    
    def readExpr(input: Reader): LispVal = try {
      run[LispVal](expression,input)
    } catch {
    	case e: ParserError => e
    }
    def readExprList = run(rep(expression),_: Reader)
    def load(filename: String) = {
      val content = new FileReader(filename)
      readExprList(content)
    }
    
    def readAll(v: List[LispVal]) = {
      v match {case List(LString(fn)) => new LList(load(fn))}
    }
  }
  
  
  trait LispVal {
    def eval(e: Env):LispVal = this
  }
  trait LispError extends Exception with LispVal
  type LispValOrError = Either[LispError, LispVal]
  
  type Env = Map[String, LispVal]
  type ParseError = SchemeParser.Failure
  
  val ioPrimitives: List[(String, Op)] = List(
      ("apply", applyProc _),
      ("open-input-file", makePort _),
      ("open-output-file", makePort _),
      ("close-input-port", closePort _),
      ("close-output-port", closePort _),
      ("read", readProc _),
      ("write", writeProc _),
      ("read-contents", readContents _),
      ("read-all", SchemeParser.readAll)
      )
  	
  val primitives: List[(String, Op)] = List(
      ("+", numericBinop(_ + _)),
      ("-", numericBinop(_ - _)),
      ("*", numericBinop(_ * _)),
      ("/", numericBinop(_ / _)),
      ("mod", numericBinop(_ % _)),
      ("quotient", numericBinop(_ / _)),
      ("remainder", numericBinop(_ % _)),
      ("=", numBoolBinop(_ == _)),
      ("<", numBoolBinop(_ < _)),
      (">", numBoolBinop(_ > _)),
      ("/=", numBoolBinop(_ != _)),
      (">=", numBoolBinop(_ >= _)),
      ("<=", numBoolBinop(_ <= _)),
      ("&&", boolBoolBinop(_ && _)),
      ("||", boolBoolBinop(_ || _)),
      ("string=?", strBoolBinop(_ == _)),
      ("string?", strBoolBinop(_ > _)),
      ("string<=?", strBoolBinop(_ <= _)),
      ("string>=?", strBoolBinop(_ >= _)),
      ("car", car),
      ("cdr", cdr),
      ("cons", cons),
      ("eq?", eqv),
      ("eqv?", eqv),
      ("equal?", equal)
      )
      
  var primitiveBindings = {
    def makeFunc(constr: Op => LispVal)(t: (String, Op))/*(v: String, func: Op)*/= { 
      t match {case (v, func) => (v, constr(func))}
    }
    val binds:List[(String, LispVal)] = (ioPrimitives map makeFunc(IOFunc)) ++ (primitives map makeFunc(PrimitiveFunc))
    /*case (s,func) => makeFunc(IOFunc)(s,func)*/
    bindVars(Map(), binds)
  }
  
  def foldl1[A](xs: List[A])(op: (A, A) => A):A = xs match {
    case Nil => throw new RuntimeException("empty list")
    case List(x) => x
    case x::rest => rest.foldLeft(x)(op)
  }

  def numericBinop(op : (Int,Int)=> Int): Op = vs => vs match {
      case v@ List(_) => throw NumArgs(2, v)
      case params => Number(foldl1(params map unpackNum)(op))
  }

  def boolBinop[A](unpacker: LispVal => A)(op: (A,A)=>Boolean)(args: List[LispVal]): LispVal = {
      if (args.length != 2) throw new NumArgs(2, args)
      else {
          val left = unpacker(args.head)
          val right = unpacker(args.last)
          Bool(op(left, right))
      }
  }

  def numBoolBinop = boolBinop(unpackNum) _
  def strBoolBinop = boolBinop(unpackStr) _
  def boolBoolBinop = boolBinop(unpackBool) _

  def unpackNum(v: LispVal):Int = v match {
      case Number(n) => n
      case LString(s) => Integer.parseInt(s)
      case LList(List(n)) => unpackNum(n)
      case notNum => throw TypeMismatch("number", notNum)
  }
  
  def unpackStr(v: LispVal):String = v match {
      case LString(s) => s
      case Number(n) => n.toString
      case Bool(n) => n.toString
      case notString => throw new TypeMismatch("string", notString)
  }
  def unpackBool(v: LispVal):Boolean = v match {
      case Bool(b) => b
      case notBool => throw new TypeMismatch("bool", notBool)
  }

  
  def car :Op = args => args match {
    case List(LList(x :: xs)) => x
    case List(DottedList(x::xs, _)) => x
    case List(badarg) => throw new TypeMismatch("pair", badarg)
    case badArgList => throw new NumArgs(1, badArgList)
  }
  def cdr :Op = args => args match {
    case List(LList(x::xs)) => LList(xs)
    case List(DottedList(_::xs, x)) => DottedList(xs, x)
    case List(DottedList(_, x)) => x
    case List(badArg) => throw new TypeMismatch("pair", badArg)
    case badArgList => throw new NumArgs(1, badArgList)
  }
  def cons :Op = args => args match {
      case List(x, LList(Nil)) => LList(List(x))
      case List(x, LList(xs)) => LList(x :: xs)
      case List(x, DottedList(xs, xlast)) => DottedList(x::xs, xlast)
      case List(x1, x2) => DottedList(List(x1), x2)
      case badArgList => throw new NumArgs(2, badArgList)
  }
  def eqv :Op = args => args match {
      case List(Bool(a), Bool(b)) => Bool(a == b)
      case List(Number(a), Number(b)) => Bool(a == b)
      case List(LString(a), LString(b)) => Bool(a==b)
      case List(Atom(a), Atom(b)) => Bool(a==b)
      case List(DottedList(xs,x), DottedList(ys,y)) => Bool(xs == ys && x == y)
      case List(LList(a), LList(b)) => {
          val eqLen = a.length == b.length
          def and(bs: List[Boolean]):Boolean = bs forall (x => x)
          val eqs = a zip b map { case ((a,b)) => eqv(List(a, b))}
          Bool(eqLen && and(eqs map {case Bool(b) => b}))
      }
      case List(_,_) => Bool(false)
      case badArgList => throw new NumArgs(2,badArgList)
  }

  def equal :Op = eqv // Todo
  def makeFunc (varargs : Option[String])(e : Env, params : List[LispVal], body: List[LispVal]):LispVal = {
    return new Func(params map {_.toString}, varargs, body, e)
  }
  def makeNormalFunc = makeFunc(None)_
  def makeVarargs(v : LispVal) = makeFunc(Some(v.toString))_
  
  def setVar(e: Env, varname: String, v: LispVal):LispVal = {
    if (e contains varname) {
      e put (varname, v)
      v
    }
    else throw new UnboundVar("Setting an unbound variable", varname)
  }

  def defineVar(e: Env, varname: String, v: LispVal): LispVal = {
    e put (varname, v)
    v
  }
  case class Atom(s:String) extends LispVal {
    override def toString = s
    override def eval(e: Env) = this match {
    case Atom(id) => e.get(id) match {
      case None => UnboundVar("Unbounded var", id)
      case v => v.get
    }
    }
  }
  case class LList(vl : List[LispVal]) extends LispVal {
    override def toString = vl.mkString("(", ",", ")")
    override def eval(e : Env) = this match{
      case LList(List(Atom("quote"), v)) => v
      case LList(List(Atom("if"), pred, conseq, alt)) => {
        val res = pred eval e
        res match {
          case Bool(true) => conseq eval e
          case _ => alt eval e
        }
      }
      case LList(List(Atom("set!"), Atom(varname), form)) => {
        val res = form eval e
        e += ((varname, res))
        res
      }
      case LList(List(Atom("define"), Atom(varname), form)) => {
        val res = form eval e
        /*if (e contains varname)	e += ((varname, res))
        else e += ((varname, null))*/
        defineVar(e, varname, res)
      }
      case LList(Atom("define") :: LList(Atom(varname) :: params) :: body) => {
        val res = makeNormalFunc(e, params, body)
        defineVar(e, varname, res)
      }
      case LList(Atom("define") :: DottedList(Atom(varname) :: params, varargs) :: body) => {
        val f = makeVarargs(varargs)(e, params, body)
        defineVar(e, varname, f)
      }
      case LList(Atom("lambda") :: LList(params) :: body) => {
        makeNormalFunc(e, params, body)
      }
      case LList(Atom("lambda") :: DottedList(params, varargs) :: body) => {
        makeVarargs(varargs)(e, params, body)
      }
      case LList(Atom("lambda") :: (varargs@ Atom(_)) :: body) => {
        makeVarargs(varargs)(e, List(), body)
      }
      case LList(List(Atom("load"), LString(filename))) => {
        val vs = SchemeParser.load(filename)
        val res = vs map { _ eval e }
        res.last
      }
      case LList(function :: args) => {
        val func = function eval e
        val argvs = args map {_ eval e}
        func match {
          case func: Func => applyFunc(func, argvs)
          case func: PrimitiveFunc => applyFunc(func, argvs)
          case _ => LList(func :: argvs)
        }
      }
      case other => other
    } 
  }
  type Op = List[LispVal] => LispVal
  
  def applyFunc(func: LispVal, args: List[LispVal]) = {
    func match {
      case PrimitiveFunc(f) => f(args)
      case Func(params, varargs, body, closure) => {
        val plen = params.length
        val remArgs = args drop plen
        if (params.length != args.length && varargs == None)
          throw new NumArgs(params.length, args)
        else {
          val e = bindVars(closure, params zip args)
          val env = varargs match {
            case Some(argname) => bindVars(e, List((argname, LList(remArgs))))
            case _ => e
          }
          body map {_ eval env} last
        }
      }
    }
  }
  
  def bindVars(e: Env, bindings: List[(String, LispVal)]) = {
    e ++= bindings
  }
  case class DottedList(head : List[LispVal], tail : LispVal) extends LispVal {
    override def toString = "(" + head.mkString(",") + " . " + tail + ")"
  }
  case class Number(n : Int) extends LispVal {
	override def toString = n.toString
  }
  case class LString(s : String) extends LispVal {
  }
  case class Bool (v : Boolean) extends LispVal {
    override def toString = v match {
      case true => "#t"
      case _ => "#f"
    }
  }
  case class Port (p : File) extends LispVal
  case class PrimitiveFunc (fun : List[LispVal] => LispVal) extends LispVal
  case class IOFunc (fun : Op) extends LispVal
  
  case class Func (params : List[String], vararg : Option[String], body: List[LispVal], closure : Env) extends LispVal {
    override def toString = "func(" + params + ")"
  }
  
  case class NumArgs (n : Integer, vals : List[LispVal]) extends LispError {
    override def toString = "Expected " + n + "args; found values " + vals
  }
  case class TypeMismatch (t : String, v : LispVal) extends LispError {
    override def toString = "Invalid type: expected " + t + ", found " + v
  }
  case class ParserError (e : ParseError) extends LispError {
    override def toString = "Parse error at " + e
  }
  case class BadSpecialForm (msg : String, v : LispVal) extends LispError {
    override def toString = msg + ": " + v
  }
  case class NotFunction (msg : String, func : String) extends LispError {
    override def toString = msg + ": " + func
  }
  case class UnboundVar (msg : String, varname : String) extends LispError {
    override def toString = msg + ": " + varname
  }
  case class Default (msg : String) extends LispError {
    override def toString = msg
  }
  
  def applyProc(v: List[LispVal]) = v match {
    case List(func, LList(args)) => applyFunc(func, args)
    case func :: args => applyFunc(func, args)
  }
  
  def makePort(v: List[LispVal]) = {
    v match {
      case List(LString(name)) => new Port(new File(name))
      case List(s) => throw new TypeMismatch("string", s)
    }
  }
  
  def closePort(v: List[LispVal]) = v match {
    case List(Port(p)) => {
      // TODO: how to close a file.
      new Bool(true)
    }
    case _ => new Bool(false)
  }
  
  def readProc(v: List[LispVal]) = v match {
    case List(Port(p)) => {
      val reader = new FileReader(p)
      val br = new BufferedReader(reader)
      SchemeParser.readExpr(br)
    }
  }
  
  def writeProc(v: List[LispVal]) = v match {
    case List(obj, Port(p)) => {
      val writer = new FileWriter(p)
      writer.write(obj.toString)
      Bool(true)
    }
    case List(obj) => {
      println(obj)
      Bool(true)
    }
  }
  
  def readContents(v: List[LispVal]) = v match {
    case List(LString(fn)) => {
      LString(Source.fromFile(fn).mkString)
    }
  }

  def runOne(args: List[String]) = {
      val env = bindVars(primitiveBindings, List(("args", LList(args.tail map LString))))
      val v = LList(List(Atom("load"), LString(args.head))) eval env
      println(v)
  }

  def until[A](pred: A => Boolean)(prompt: => A)(action: A => Unit): Unit = {
      val res = prompt
      if (pred(res)) return ()
      else {
          action(res)
          until(pred)(prompt)(action)
      }
  }
  def runRepl = {
    until[String](_ == "quit")(readPrompt("Lisp>>>"))(evalAndPrint(primitiveBindings))
  }

  def readPrompt(s: String): String = {
      print(s)
      def getLine = new Scanner(System.in).nextLine()
      getLine
  }

  def evalAndPrint(e: Env)(expr: String):Unit = {
      val res = (SchemeParser.readExpr(new StringReader(expr))).eval(e)
      println(res)
  }
  
  def main(args: Array[String]) = {
    if (args.isEmpty) runRepl
    else runOne(args.toList)
  }
}

