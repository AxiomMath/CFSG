module

public import CFSG.GH74.GLS.C3.Layer2.L5C4b
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0
public meta import CFSG.GH74.GLS.C3.Layer2.L5C4a
public meta import CFSG.GH74.GLS.C3.Layer2.L5C4b

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.Rec1

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
@[expose] def tm (b : Bool) (m : Nat) : Nat := cond b m 0

@[expose] def redF (B : List (Nat × Nat)) (m : Nat) : Nat :=
  B.foldl (fun m pr => cond (m.testBit pr.1) (m ^^^ pr.2) m) m

@[expose] def addRow (B : List (Nat × Nat)) (e : Nat) : List (Nat × Nat) :=
  cond (redF B e == 0) B
    ((Nat.log2 (redF B e), redF B e) ::
      B.map fun pr =>
        cond (pr.2.testBit (Nat.log2 (redF B e))) (pr.1, pr.2 ^^^ redF B e) pr)

@[expose] def basisOf (E : List Nat) : List (Nat × Nat) := E.foldl addRow []

@[expose] def vi (j k c : Nat) : Nat := (j * 8 + k) * 4 + c

@[expose] def Mj (j : Fin 8) (c c' : Nat) : Bool :=
  ((Dg j) ⟨2 ^ c' % 16, Nat.mod_lt _ (by norm_num)⟩).val.testBit c

@[expose] def dF (j k l : Fin 8) (c : Nat) : Nat :=
  tm (Mj j c 0) (2 ^ vi k.val l.val 0) ^^^ tm (Mj j c 1) (2 ^ vi k.val l.val 1) ^^^
    tm (Mj j c 2) (2 ^ vi k.val l.val 2) ^^^ tm (Mj j c 3) (2 ^ vi k.val l.val 3)

@[expose] def cocEq (j k l : Fin 8) (c : Nat) : Nat :=
  2 ^ vi j.val k.val c ^^^ 2 ^ vi (mulIdx j k).val l.val c ^^^ dF j k l c ^^^
    2 ^ vi j.val (mulIdx k l).val c

@[expose] def cocEqs : List Nat :=
  ((List.finRange 8).flatMap fun j => (List.finRange 8).flatMap fun k =>
    (List.finRange 8).flatMap fun l => (List.finRange 4).map fun c => cocEq j k l c.val) ++
  ((List.finRange 8).flatMap fun k => (List.finRange 4).flatMap fun c =>
    [2 ^ vi 0 k.val c.val, 2 ^ vi k.val 0 c.val])

@[expose] def cocBasis : List (Nat × Nat) := basisOf cocEqs

@[expose] def rhsForm (c1 : Fin 8 → Fin 8 → Fin 16) (eF : Nat) (bF : List Nat) (j k : Fin 8)
    (c : Nat) : Nat :=
  tm ((c1 j k).val.testBit c) eF ^^^ bF.getD (j.val * 4 + c) 0 ^^^
    (tm (Mj j c 0) (bF.getD (k.val * 4 + 0) 0) ^^^ tm (Mj j c 1) (bF.getD (k.val * 4 + 1) 0) ^^^
      tm (Mj j c 2) (bF.getD (k.val * 4 + 2) 0) ^^^ tm (Mj j c 3) (bF.getD (k.val * 4 + 3) 0)) ^^^
    bF.getD ((mulIdx j k).val * 4 + c) 0

@[expose] def fsCheck (c1 : Fin 8 → Fin 8 → Fin 16) (eF : Nat) (bF : List Nat) : Bool :=
  (List.finRange 8).all fun j => (List.finRange 8).all fun k => (List.finRange 4).all fun c =>
    redF cocBasis (2 ^ vi j.val k.val c.val ^^^ rhsForm c1 eF bF j k c.val) == 0

@[expose] def eFdata : Nat := 89208425311993227582787282961483852406587392

@[expose] def bFdata : List Nat :=
  [0, 0, 0, 0,
    89202980794122492575815460277416466589941760, 89208425311993227582787282961483921126064128, 21778071482940061661656032296597133983744, 89208425311993227582787282961483577528680448,
    5444517870735026296927000156558032109568, 89208425311993227582787578109390199990517760, 370227215209981048248446774835513084870656, 89202980794122492575814279685791076254220288,
    20365205462116988878848, 89208425311993227582787578109392330294296576, 89551429937849533562401070430586327504257024, 5444517870735026315816466096557828079616,
    370227215209981053084150000376459284185088, 89202980794122492566142873090593446023921664, 89230203383476167644448938990402474942136320, 2252074691592192,
    370227215209981063983371881120197270044672, 89202980794122492568561019877729051957264384, 89230203383476167644448938939736979134218240, 89208425311993227582787282997512374547644416,
    89578652527203208645541658965714026562060288, 5444517870735016644409871453425055563776, 0, 0,
    370227215209981056730702373374605207273472, 5444517870735019062556667033142851272704, 0, 0]

end CFSG.GH74.GLS.C3.Layer2.L5.Rec1
