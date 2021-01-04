Require Import Strings.String.
Local Open Scope string_scope. 
Local Open Scope list_scope.
Scheme Equality for string.

Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import Coq.Strings.Byte.
Import Nat.
Require Import ZArith.

Require Import Omega.
Set Nested Proofs Allowed.

Require Import List.
Local Open Scope list_scope.
Scheme Equality for list.
Import ListNotations.

Inductive types : Set :=
| typeNat : nat -> types
| typeBool : bool -> types.

Inductive ErrorNat :=
  | error_nat : ErrorNat
  | num : nat -> ErrorNat.

Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.

Inductive ErrorChars :=
  | error_char : ErrorChars
  | chars : string -> ErrorChars.

Check (chars "aaa").

Coercion num: nat>->ErrorNat.
Coercion boolean : bool >-> ErrorBool.
Coercion chars : string >-> ErrorChars.

Check (typeNat 3).

Coercion typeNat: nat>->types.
Coercion typeBool : bool >-> types.

(*Nat and Bool List*)

Inductive list (T : Type) : Type :=
| nil : list T
| node : T -> list T -> list T.

Check (node nat 3 (nil nat)).
Check (node bool false (node bool true (nil bool))).

Notation "'listNat' [ x ,, y ,, .. ,, z ]" :=(node nat x (node nat y ..(node nat z (nil nat)) ..)).
Check (listNat [3,,4,,5]).

Notation "'listBool' [ x ,, y ,, .. ,, z ]" :=(node bool x (node bool y ..(node bool z (nil bool)) ..)).
Check (listBool [true,,true,,true]).

(*Vectors*)


Inductive Vector :=
  | vectorNat: list nat -> Vector
  | vectorBool : list bool -> Vector.


(*Refolosesc notatiile listelor pentru vectori*)

Notation "'vectorNat' L" := (vectorNat L) (at level 20).
Notation "'vectorBool' L" := (vectorBool L) (at level 20).

Check (vectorNat listNat [3 ,, 4 ,, 5]).
Check (vectorBool listBool [true ,, false ,, false ,, true]).

Inductive ErrorVector:=
  | errorVector : ErrorVector
  | vector : Vector -> ErrorVector.

Check (errorVector).

Check (vector (vectorNat listNat [3 ,, 4 ,, 5])).
Check (vector (vectorBool listBool [false ,, false ,, true])).

(*Stack*)

Inductive natStack:=
  | stackBottomNat : natStack
  | stackElementNat  : nat -> natStack -> natStack.

Inductive boolStack:=
  | stackBottomBool : boolStack
  | stackElementBool  : bool -> boolStack -> boolStack.

Inductive Stack :=
  | NatStack : natStack -> Stack 
  | BoolStack : boolStack -> Stack.

Check (NatStack stackBottomNat).
Check (NatStack (stackElementNat 3 stackBottomNat)).

Check (NatStack (stackElementNat 3 (stackElementNat 5 stackBottomNat))).

Notation "'NatStack' [ x >> y >> .. >> z ]" :=(NatStack (stackElementNat x (stackElementNat y .. ( stackElementNat z (stackBottomNat) ) ..))).
Notation "'BoolStack' [ x >> y >> .. >> z ]" :=(BoolStack (stackElementBool x (stackElementBool y .. ( stackElementBool z (stackBottomBool) ) ..))).

Check (NatStack [3 >> 4 >> 5]).
Check (BoolStack [true >> true >> false >> true >> false]).

Inductive ErrorStack :=
  | errorStack : ErrorStack
  | stack: Stack -> ErrorStack.

Check (stack (NatStack [3 >> 4 >> 5])).
Check (stack (BoolStack [true >> true >> false >> true >> false])).


(*Queue*)

Inductive natQueue:=
  | queueBottomNat : natQueue
  | queueElementNat  : nat -> natQueue -> natQueue.

Inductive boolQueue:=
  | queueBottomBool : boolQueue
  | queueElementBool  : bool -> boolQueue -> boolQueue.

Inductive Queue :=
  | NatQueue : natQueue -> Queue 
  | BoolQueue : boolQueue -> Queue.

Check (NatQueue queueBottomNat).
Check (NatQueue (queueElementNat 3 queueBottomNat)).

Check (NatQueue (queueElementNat 3 (queueElementNat 5 queueBottomNat))).

Notation "'NatQueue' [ x << y << .. << z ]" :=(NatQueue (queueElementNat x (queueElementNat y .. ( queueElementNat z (queueBottomNat) ) ..))).
Notation "'BoolQueue' [ x << y << .. << z ]" :=(BoolQueue (queueElementBool x (queueElementBool y .. ( queueElementBool z (queueBottomBool) ) ..))).

Check (NatQueue [3 << 4 << 5]).
Check (BoolQueue [true << true << false << true << false]).

Inductive ErrorQueue :=
  | errorQueue : ErrorQueue
  | queue: Queue -> ErrorQueue.

Check (queue (NatQueue [3 << 4 << 5])).
Check (queue (BoolQueue [true << true << false << true << false])).

(*Map*)

Inductive MapElement : Type :=
| mapElement : string -> nat -> MapElement.



Inductive Map : Type :=
| mapEl : string -> list MapElement -> Map. 


Inductive ErrorMap :=
| errorMap : ErrorMap
| map : Map -> ErrorMap.

Coercion map : Map >-> ErrorMap.

Notation "[( E1 , E2 )]" := (mapElement E1 E2) (at level 0).

Check (mapElement "S1" 1).
Check [("S1" , 1)].

Check (mapEl "map" ( node MapElement (mapElement "S1" 1 )(nil MapElement ) ) ) .
 
Notation "{ x , y , .. , z }" :=  (node MapElement x (node  MapElement y .. (node  MapElement z (nil MapElement) ) ..) ) .



Check { [("S1", 1)] , [("S2" , 2)] }.
Check mapEl "Map" { [("S1", 1)] , [("S2" , 2)] }. 


Inductive returnType :=
  | errorUndeclared : returnType
  | errorAssignment : returnType
  | default : returnType
  | returnNat : ErrorNat -> returnType
  | returnBool : ErrorBool -> returnType
  | returnChars : ErrorChars -> returnType
  | returnVector : ErrorVector -> returnType
  | returnStack : ErrorStack -> returnType
  | returnQueue : ErrorQueue -> returnType
  | returnMap : ErrorMap -> returnType.


Definition Env := string -> returnType.

Definition env : Env := fun x => errorUndeclared.

Definition check_eq_over_types (t1 : returnType) (t2 : returnType) : bool :=
  match t1 with
    | errorUndeclared => match t2 with 
                     | errorUndeclared => true
                     | _ => false
                     end
    | errorAssignment => match t2 with 
                     | errorAssignment => true
                     | _ => false
                     end
    | default => match t2 with 
                     | default => true
                     | _ => false
                     end
    | returnNat a => match t2 with 
                     | returnNat b => true
                     | _ => false
                     end
    | returnBool a => match t2 with 
                     | returnBool b => true
                     | _ => false
                     end
    | returnChars a => match t2 with 
                     | returnChars b => true
                     | _ => false
                     end
    | returnVector a => match t2 with 
                     | returnVector b => true
                     | _ => false
                     end
    | returnStack a => match t2 with 
                     | returnStack b => true
                     | _ => false
                     end
    | returnQueue a =>  match t2 with 
                     | returnQueue b => true
                     | _ => false
                     end
    | returnMap a =>  match t2 with 
                     | returnMap b => true
                     | _ => false
                     end
  end.

Compute (check_eq_over_types (returnBool true) (returnBool false) ).

Compute (check_eq_over_types (returnChars "aaa") (returnChars "bbb") ).

Compute (check_eq_over_types (returnNat 3) (returnStack (stack (NatStack [3 >> 4 >> 5]) ) ) ).

Definition update (env : Env) (x : string) (v : returnType) : Env :=
  fun y =>
    if (string_beq y x) 
        then 
        if (andb (bool_beq (check_eq_over_types v default) true) (bool_beq (check_eq_over_types (env x) errorUndeclared) true)) then v
            else if (bool_beq (check_eq_over_types (env x) default) true)  then v
                     else if (bool_beq (check_eq_over_types (env x) errorUndeclared) true) then (env x)
                              else if (bool_beq (check_eq_over_types (env x) v) true) then v
                                       else errorAssignment
    else (env y).

Notation "S [ V /' X ]" := (update S X V) (at level 0).

Compute (env "y"). 
Compute (update (update env "y" (default)) "y" (returnBool true) "y").
Compute ((update (update (update env "y" default) "y" (returnNat 10)) "y" (returnBool true)) "y"). 


(*EXP*)



(*vector exp*)

Inductive VExp :=
| vvar : string -> VExp
| vconst : ErrorVector -> VExp.

Coercion vvar: string >-> VExp.
Coercion vconst : ErrorVector >-> VExp.

(*stack exp*)

Inductive SExp :=
| svar : string -> SExp
| sconst : ErrorStack -> SExp
| popS : SExp -> SExp
| pushSNat : SExp -> nat -> SExp
| pushSBool : SExp -> bool -> SExp .

Coercion svar: string >-> SExp.
Coercion sconst : ErrorStack >-> SExp.

(*queue exp*)

Inductive QExp :=
| qvar : string -> QExp
| qconst : ErrorQueue -> QExp
| popQ : QExp -> QExp
| pushQNat : QExp -> nat -> QExp
| pushQBool : QExp -> bool -> QExp.

Coercion qvar: string >-> QExp.
Coercion qconst : ErrorQueue >-> QExp.

(*MExp*)

Inductive MExp :=
| mvar : string -> MExp
| mconst : ErrorMap -> MExp.

(*chars exp*)

Inductive CExp :=
| cvar : string -> CExp
| cconst : ErrorChars -> CExp
| mapFindCh : MExp -> nat -> CExp
| strcat : CExp -> CExp -> CExp
| strcpy : CExp -> CExp -> CExp.

Coercion cvar: string >-> CExp.
Coercion cconst : ErrorChars >-> CExp.

(*AEXP*)


Inductive AExp :=
| avar: string -> AExp 
| anum: ErrorNat -> AExp
| aplus: AExp -> AExp -> AExp
| aminus: AExp -> AExp -> AExp
| amul: AExp -> AExp -> AExp 
| adiv: AExp -> AExp -> AExp
| amod: AExp -> AExp -> AExp
| index : VExp -> nat -> AExp
| topS : SExp -> AExp
| topQ : QExp -> AExp
| mFind : MExp -> string -> AExp
| strstr : CExp -> CExp -> AExp.

Coercion anum: ErrorNat >-> AExp.
Coercion avar: string >-> AExp.

Notation "A +' B" := (aplus A B)(at level 50, left associativity).
Notation "A -' B" := (aminus A B)(at level 50, left associativity).
Notation "A *' B" := (amul A B)(at level 48, left associativity).
Notation "A /' B" := (adiv A B)(at level 48, left associativity).
Notation "A %' B" := (amod A B)(at level 45, left associativity).

Check (3 +' 4).

Check (popQ (queue(NatQueue [3 << 4 << 5]))).

Check (topS (stack(BoolStack [true >> false >> true >> true]))).

Check (index (vector (vectorNat listNat [3 ,, 4 ,, 5])) 2).

Check (mFind (mconst (mapEl "Map" { [("S1", 1)] , [("S2" , 2)] })) "maria").


(*BEXP*)

Inductive BExp :=
| berror
| btrue
| bfalse
| bvar: string -> BExp 
| ble : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| beq : AExp -> AExp -> BExp
| bor : BExp -> BExp -> BExp
| strcmp : CExp -> CExp -> BExp
| strncmp : CExp -> CExp -> AExp -> BExp.

Notation "A <' B" := (ble A B) (at level 70).
Notation "!' A" := (bnot A)(at level 51, left associativity).
Notation "A &&' B" := (band A B)(at level 52, left associativity).
Notation "A ||' B" := (bor A B)(at level 53, left associativity).
Notation "A ==' B" := (beq A B)(at level 53, left associativity).

(*STMT*)

Inductive Stmt :=
  | nDecl: string -> AExp -> Stmt 
  | bDecl: string -> BExp -> Stmt 
  | vDecl : string -> VExp -> Stmt
  | chDecl : string -> CExp -> Stmt
  | mDecl : string -> MExp -> Stmt
  | sDecl : string -> SExp -> Stmt
  | qDecl : string -> QExp -> Stmt
  | sAssign : string -> SExp -> Stmt
  | qAssign : string -> QExp -> Stmt
  | nAssign : string -> AExp -> Stmt 
  | bAssign : string -> BExp -> Stmt 
  | chAssign : string -> CExp -> Stmt
  | sequence : Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt
  | break : Stmt
  | continue : Stmt
  | switch :  AExp -> Datatypes.list (AExp * Stmt)  -> Stmt
  | ifthenelse : BExp -> Stmt -> Stmt -> Stmt
  | ifthen : BExp -> Stmt -> Stmt
  | vIndex : Vector -> types -> Stmt
  | qOperation : QExp -> Stmt
  | sOperation : SExp -> Stmt
  | chOperation : CExp -> Stmt
  | aOperation : AExp -> Stmt
  | bOperation : BExp -> Stmt.

Notation "'int' X ::= A" := (nDecl X A)(at level 90).
Notation "X :n= A" := (nAssign X A)(at level 90).
Notation "X :b= A" := (bAssign X A)(at level 90).
(*Notation "X :s= A" := (stringAssign X A)(at level 90). *)
Notation "'vDecl' X ::= A" := (vDecl X A)(at level 90).
Notation "'qDecl' X ::= A" := (qDecl X A)(at level 90).
Notation "'bool' X ::= A" := (bDecl X A)(at level 90).
(*Notation "'strings' X ::= A" := (string_decl X A)(at level 90).*)
Notation "'sDecl' X ::= A" := (sDecl X A)(at level 90).
Notation "'mapp' X ::= A" := (mDecl X A)(at level 90).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 93).



Definition pgm :=
  int "var" ::= 2;;                                                (*declarare variabila de tipul intreg*)
  "var" :n= 3;;                                                    (*schimbare valoare variabila de tipul intreg*)
  vDecl "vector" ::= (vector (vectorNat listNat [3 ,, 4 ,, 5]));;  (*declarare vector*)
  sDecl "stiva" ::= (stack (NatStack [3 >> 4 >> 5]));;             (*declarare stiva*)
  vIndex (vectorNat listNat [3 ,, 4 ,, 5]) 2;;                     (*accesare element din vector*)
  sOperation (pushSNat (stack (NatStack [3 >> 4 >> 5])) 3);;       (*adaugare element pe stiva*)
  qOperation (popQ (queue (BoolQueue [true << true <<false])));;   (*elimare element din coada*)
  aOperation (strstr "aaa" "bbb");;                                (*cautarea unui sir in alt sir, returnand pozitia pe care se gaseste*)
  bOperation (strcmp "aaa" "bbb");;                                (*comparare a doua siruri*)
  chOperation (mapFindCh (mconst (mapEl "Map" { [("S1", 1)] , [("S2" , 2)] })) 1).  (*cauta cheia valorii date ca parametru in map*)































