open Camlp4.PreCast


(* http://www.cs.nyu.edu/pipermail/smt-lib/2010/000387.html *)
                                          
type token =
  | LPAREN | RPAREN | UNDERSCORE | EXCLAMATION
  | AS | LET | FORALL | EXISTS
  | SETLOGIC | SETOPTION | SETINFO
  | DECLARESORT | DEFINESORT | DECLAREFUN | DEFINEFUN
  | PUSH | POP  | ASSERT | CHECKSAT
  | GETASSERT | GETPROOF | GETUNSATCORE
  | GETVALUE | GETASSIGN | GETOPTION | GETINFO
  | EXIT
  | EOF 


module type SongbirdToken = Camlp4.Sig.Token with type t = token

module Token = struct
  open Format
  module Loc = Loc
  type t = token
  type token = t

  let sf = Printf.sprintf

  let to_string k = match k with
    | HEXA_LIT (_, s) -> s
    | STRING_LIT (_, s) -> s
    | NUMERAL_LIT (_, s) -> s
    | DECIMAL_LIT (_, s) -> s
    | LPAREN -> "("
    | RPAREN -> ")"
    | UNDERSCORE -> "_"
    | EXCLAMATION -> "!"
    | AS -> "as"
    | LET -> "let"
    | FORALL -> "forall"
    | EXISTS -> "exists"
    | SETLOGIC -> "set-logic"
    | SETOPTION -> "set-option"
    | SETINFO -> "set-info"
    | DECLARESORT -> "declare-sort"
    | DEFINESORT -> "define-sort"
    | DECLAREFUN -> "declare-fun"
    | DEFINEFUN -> "define-fun"
    | PUSH -> "push"
    | POP -> "pop"
    | ASSERT -> "assert"
    | CHECKSAT -> "check-sat"
    | GETASSERT -> "get-assertions"
    | GETPROOF -> "get-proof"
    | GETUNSATCORE -> "get-unsat-core"
    | GETVALUE -> "get-value"
    | GETASSIGN -> "get-assignment"
    | GETOPTION -> "get-option"
    | GETINFO -> "get-info"
    | EXIT -> "exit"
    | EOF -> ""

  let print ppf x = pp_print_string ppf (to_string x)

  let match_keyword kwd _ = false 

  let extract_string t = match t with
    | ID s | INT_LITER (_,s) | STRING (_,s) -> s
    | _ -> ""

  module Error = struct
    type t = string
    exception E of string
    let print = pp_print_string
    let to_string x = x
  end

  module Filter = struct
    type token_filter = (t, Loc.t) Camlp4.Sig.stream_filter

    type t =
      { is_kwd : string -> bool;
        mutable filter : token_filter }

    let mk is_kwd =
      { is_kwd = is_kwd;
        filter = (fun s -> s) }

    let filter x = fun strm -> x.filter strm

    let define_filter x f = x.filter <- f x.filter

    let keyword_added _ _ _ = ()
    let keyword_removed _ _ = ()
  end

end

module Error = Camlp4.Struct.EmptyError
