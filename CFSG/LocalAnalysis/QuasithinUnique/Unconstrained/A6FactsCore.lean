module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsData

public section

namespace CFSG.QuasithinUnique.A6Facts.Core

@[expose] def cmul (a b : List Nat) : List Nat := b.map fun j => a.getD j 0

@[expose] def cid : List Nat := List.range 10

@[expose] def cid6 : List Nat := List.range 6

@[expose] def cpow (a : List Nat) : Nat → List Nat
  | 0 => List.range a.length
  | n + 1 => cmul (cpow a n) a

@[expose] def buildCodes (e : List Nat) (gc : List (List Nat)) (tree : List (Nat × Nat)) :
    List (List Nat) :=
  tree.foldl (fun acc pk => acc ++ [cmul (acc.getD pk.1 e) (gc.getD pk.2 e)]) [e]

@[expose] def tblCheckC (e : List Nat) (gc E : List (List Nat)) (T : List (List Nat)) : Bool :=
  (List.range E.length).all fun i => (List.range gc.length).all fun k =>
    decide ((T.getD i []).getD k 0 < E.length) &&
      (cmul (E.getD i e) (gc.getD k e) == E.getD ((T.getD i []).getD k 0) e)

theorem psl_build : pslLit = buildCodes cid pslGenC pslTree := by decide +kernel

theorem psl_tbl : tblCheckC cid pslGenC pslLit pslTbl = true := by decide +kernel

theorem psl_nodup : pslLit.Nodup := by decide +kernel

theorem psl_length : pslLit.length = 360 := by decide +kernel

theorem p0_build : p0Lit = buildCodes cid p0GenC p0Tree := by decide +kernel

theorem p0_tbl : tblCheckC cid p0GenC p0Lit p0Tbl = true := by decide +kernel

theorem p0_nodup : p0Lit.Nodup := by decide +kernel

theorem p0_length : p0Lit.length = 32 := by decide +kernel

@[expose] def cosetCheck (E reps repsInv gens : List (List Nat)) : Bool :=
  reps.all fun r => gens.all fun g => repsInv.any fun rinv => E.contains (cmul (cmul r g) rinv)

@[expose] def invListCheck (l inv : List (List Nat)) : Bool :=
  (l.length == inv.length) && (l.zip inv).all fun p => cmul p.1 p.2 == cid

theorem aut_cosets : cosetCheck pslLit autReps autRepsInv autGenC = true := by decide +kernel

theorem aut_repsInv : invListCheck autReps autRepsInv = true := by decide +kernel

theorem aut_reps_one : autReps.contains cid = true := by decide +kernel

theorem s6_cosets : cosetCheck pslLit s6Reps s6RepsInv s6GenC = true := by decide +kernel

theorem s6_repsInv : invListCheck s6Reps s6RepsInv = true := by decide +kernel

theorem s6_reps_one : s6Reps.contains cid = true := by decide +kernel

@[expose] def autL : List (List Nat) := pslLit.flatMap fun y => autReps.map (cmul y)

theorem cent_psl : autL.all
    (fun y => !(pslGenC.all fun x => cmul y x == cmul x y) || y == cid) = true := by
  decide +kernel

theorem p0Gen_aut : p0GenC.all
    (fun g => autRepsInv.any fun rinv => pslLit.contains (cmul g rinv)) = true := by
  decide +kernel

theorem d_eq : dLit = p0Lit.filter (fun c => pslLit.contains c) := by decide +kernel

@[expose] def inS6 (c : List Nat) : Bool :=
  s6RepsInv.any fun rinv => pslLit.contains (cmul c rinv)

@[expose] def cpslList (c : List Nat) : List (List Nat) :=
  pslLit.filter fun y => cmul y c == cmul c y

theorem inv_classification : autL.all (fun c =>
    cmul c c != cid || c == cid || pslLit.contains c || inS6 c || (cpslList c).length == 10) =
      true := by
  decide +kernel

theorem p0_exp8 : p0Lit.all (fun a => cpow a 8 == cid) = true := by decide +kernel

theorem p0_noQ16 : p0Lit.all (fun a => p0Lit.all (fun b =>
    !(cpow a 4 != cid && cmul b b == cpow a 4 && cmul (cmul a b) a == b))) = true := by
  decide +kernel

theorem p0_cent_d : p0Lit.all (fun c =>
    !(dLit.all fun d => cmul c d == cmul d c) || cmul c c == cid) = true := by
  decide +kernel

end CFSG.QuasithinUnique.A6Facts.Core
