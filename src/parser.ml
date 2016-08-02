(*
 *  Written by Ta Quang Trung - Jun 2016 
 *)

open Token
open Camlp4
open Debug
open Globals
open Iast

module Lex = Lexer.Make(Token)
module Gram = Camlp4.Struct.Grammar.Static.Make(Lex)

(* compute the position by adding the location return by camlp4 *)
let get_pos l =
  let sp = Camlp4.PreCast.Loc.start_pos l in
  let ep = Camlp4.PreCast.Loc.stop_pos l in
  { pos_begin = sp;
    pos_end = ep; }

let un_option x default = match x with
  | Some y -> y
  | None -> default

let program = Gram.Entry.mk "program"

EXTEND Gram
GLOBAL: program;

(* program = list of declarations, commands and procedures *)

program:
  [
    [ `EOF -> mk_program ()
    | `DATA; d = data_decl; p = program -> {p with prog_datas = d::p.prog_datas}
    | `PRED; v = pred_decl; p = program -> {p with prog_preds = v::p.prog_preds}
    | `LEMMA; lm = lemma; p = program -> {p with prog_lemmas = lm::p.prog_lemmas}
    | c = command; p = program -> {p with prog_commands = c::p.prog_commands} ]
  ];

(*********************************************************)
(************             command             ************)

command:
  [
    [ `CHECKENTAIL; e = entailment; `SEMICOLON -> CheckEntail e
    | `CHECKSAT; f = formula; `SEMICOLON -> CheckSat f
    | `CHECKUNSAT; f = formula; `SEMICOLON -> CheckUnsat f
    ]
  ];

(****************************************************************)
(************             data structure             ************)

data_decl: [[
    `ID name; body = data_body ->
    mk_data_defn name body (get_pos _loc)
  ]];

data_body:
  [
    [ `OBRACE; ps = data_params; `SEMICOLON; `CBRACE -> ps
    | `OBRACE; ps = data_params; `CBRACE -> ps
    | `OBRACE; `CBRACE -> [] ]
  ];

data_params:
  [
    [ p = data_param -> [p]
    | p = data_param; `SEMICOLON -> [p]
    | p = data_param; `SEMICOLON; ps = SELF -> p::ps
    ]
  ];

data_param:
  [
    [ t = typ; `ID n -> (t,n) ]
  ];

(****************************************************************)
(************             heap predicate             ************)

pred_decl:
  [
    [ vh = pred_header; `EQEQ; vb = pred_defn_cases; `SEMICOLON ->
      mk_pred_defn (fst vh) (snd vh) vb (get_pos _loc) ]
  ];

pred_header:
  [
    [ `ID vn; `OPAREN; ps = pred_params; `CPAREN -> (vn, ps)
    | `ID vn; `OPAREN; `CPAREN -> (vn, []) ]
  ];

pred_params:
  [
    [ p = pred_param -> [p]
    | p = pred_param; `COMMA; ps = SELF -> p::ps ]
  ];

pred_param:
  [
    [ `ID n -> (TUnk,n) ]
  ];

pred_defn_cases:
  [
    [ fs = LIST1 formula SEP `ORWORD -> fs ]
  ];

(*******************************************************)
(************             lemma             ************)

lemma:
  [
    [ `ID name; `COLON; a = formula; `DERIVE; b = formula; `SEMICOLON ->
      mk_lemma name LmkSafe a b (get_pos _loc)
    | `ID name; `AT_U; `COLON; a = formula; `DERIVE; b = formula; `SEMICOLON ->
      mk_lemma name LmkSafe a b (get_pos _loc)
    | `ID name; `AT_S; `COLON; a = formula; `DERIVE; b = formula; `SEMICOLON ->
      mk_lemma name LmkUnsafe a b (get_pos _loc)]
  ];


(*********************************************************)
(************             formula             ************)


entailment:
  [
    [ a = formula; `DERIVE; b = formula -> mk_entailment a b (get_pos _loc) ]
  ];

formula:
  [ "addictive"
    [ f1 = SELF; `AND; f2 = SELF -> mk_conj f1 f2 (get_pos _loc)
    | f1 = SELF; `OR; f2 = SELF -> mk_disj f1 f2 (get_pos _loc) ]
  | "multiplicative"
    [ f1 = SELF; `STAR; f2 = SELF -> mk_star f1 f2 (get_pos _loc)
    | f1 = SELF; `WAND; f2 = SELF -> mk_wand f1 f2 (get_pos _loc) ]
  | "not"
    [ `NOT; f = SELF -> mk_neg f (get_pos _loc) ]
  | "simple"
    [ `OPAREN; f = SELF; `CPAREN -> f
    | `OPAREN; `EXISTS; vs = var_list; `DOT; f = SELF; `CPAREN ->
      let vars = List.map (mk_var TUnk) vs in
      mk_exists vars f (get_pos _loc)
    | `OPAREN; `FORALL; vs = var_list; `DOT; f = SELF; `CPAREN ->
      let vars = List.map (mk_var TUnk) vs in
      mk_forall vars f (get_pos _loc) ]
  | [ f = formula_atomic -> f ]
  ];

formula_atomic:
  [
    [ `ID pn; `OPAREN; args = LIST0 exp SEP `COMMA; `CPAREN ->
      mk_pred pn args (get_pos _loc) ]
  | "addictive"
    [ t1 = exp; `LT; t2 = exp -> mk_bin_rel Lt t1 t2 (get_pos _loc)
    | t1 = exp; `LE; t2 = exp -> mk_bin_rel Le t1 t2 (get_pos _loc)
    | t1 = exp; `GT; t2 = exp -> mk_bin_rel Gt t1 t2 (get_pos _loc)
    | t1 = exp; `GE; t2 = exp -> mk_bin_rel Ge t1 t2 (get_pos _loc)
    | t1 = exp; `EQ; t2 = exp -> mk_bin_rel Eq t1 t2 (get_pos _loc)
    | t1 = exp; `NE; t2 = exp -> mk_bin_rel Ne t1 t2 (get_pos _loc)
    | root = exp; `COLONCOLON; `ID dn; `LT; args = LIST0 exp SEP `COMMA; `GT ->
      mk_data root dn args (get_pos _loc) ]
  | "simple"
    [ `TRUE -> mk_bconst true (get_pos _loc)
    | `FALSE -> mk_bconst false (get_pos _loc)
    | `EMP -> mk_emp (get_pos _loc) ]
  ];

exp:
  [ "addictive"
    [ t1 = SELF; `PLUS; t2 = SELF -> mk_bin_op Add t1 t2 (get_pos _loc)
    | t1 = SELF; `MINUS; t2 = SELF -> mk_bin_op Sub t1 t2 (get_pos _loc) ]
  | "simple"
    [ `NULL -> mk_null (get_pos _loc)
    | `INT_LITER (i, _) -> mk_iconst i (get_pos _loc)
    | `ID v -> mk_exp_var (mk_var TUnk v) (get_pos _loc)
    | `OPAREN; t = SELF; `CPAREN -> t ]
  ];

var_list:
  [
    [ `ID v -> [v];
    | vs = var_list; `COMMA; `ID v -> vs@[v] ]
  ];


typ:
  [
    [ `VOID               -> TVoid
    | `INT                -> TInt
    | `BOOL               -> TBool
    | `ID id      -> TData id ]
  ];

END;;

(* parsing commands *)

let parse_program n s =
  try 
    Gram.parse program (PreCast.Loc.mk n) s
  with
  | Lex.Loc.Exc_located (l,t) ->
    let pos = get_pos l in
    let filename = pos.pos_begin.Lexing.pos_fname in
    let location = pr_pos pos in
    let spos = "Location: File: " ^ filename ^ ". Line/Column: " ^ location in
    let msg = "Message: " ^ (Printexc.to_string t) in
    error ("Syntax error!\n" ^ msg ^ "\n" ^ spos)
  | e -> raise e
