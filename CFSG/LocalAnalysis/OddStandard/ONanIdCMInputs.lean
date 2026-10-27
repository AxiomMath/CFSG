module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverCertInputs

public section

namespace CFSG.OddStandard.ONanRec.IdCM

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] def relData : List (FreeGroup (Fin 6) × ℕ × ℕ × ℕ) :=
  let a := FreeGroup.of (0 : Fin 6); let b := FreeGroup.of (1 : Fin 6)
  let c := FreeGroup.of (2 : Fin 6); let d := FreeGroup.of (3 : Fin 6)
  let f := FreeGroup.of (4 : Fin 6); let g := FreeGroup.of (5 : Fin 6)
  [(a ^ 2, 0, 0, 1),
    (b ^ 2, 0, 0, 1),
    (c ^ 2, 0, 0, 0),
    (d ^ 2, 0, 0, 0),
    (f ^ 2, 2, 0, 2),
    ((a * b) ^ 3, 2, 0, 0),
    ((b * c) ^ 3, 2, 0, 0),
    ((c * d) ^ 8, 2, 0, 0),
    ((a * c) ^ 2, 2, 0, 1),
    ((a * d) ^ 2, 0, 0, 1),
    ((a * f) ^ 2, 2, 0, 0),
    ((b * d) ^ 2, 0, 0, 1),
    ((b * f) ^ 2, 2, 0, 0),
    ((c * f) ^ 2, 2, 0, 2),
    ((d * f) ^ 2, 0, 0, 2),
    (g ^ 4, 0, 0, 2),
    ((a * f)⁻¹ * g ^ 2, 3, 2, 1),
    ((a * f)⁻¹ * (c * d) ^ 4, 2, 0, 0),
    (c * ((d * g * d * g)⁻¹ * c * (d * g * d * g)), 2, 0, 0),
    (d * ((c * g * c * g)⁻¹ * d * (c * g * c * g)), 1, 2, 0),
    ((b * c * d * g) ^ 5, 2, 0, 1),
    (g * b * (c⁻¹ * g * c) * (b⁻¹ * g * b) * (c⁻¹ * g * c), 1, 2, 0),
    (f⁻¹ * (d * g) ^ 4, 1, 2, 1)]

@[expose] def genStr : List (String × Bool) :=
  [("BaBBaBBaBabbabbabba", false),
    ("BababaBBababaBaBabaBa", false),
    ("BBaBBaBBabaBBaBBa", false),
    ("", true),
    ("bbabbabbabbabbabbabba", false),
    ("BaBababbabaBaBabaBa", true)]

@[expose] def genW (i : ℕ) : List (Fin 2 × Bool) × Bool :=
  ((parseWord (genStr.getD i ("", false)).1), (genStr.getD i ("", false)).2)

@[expose] def alphaIf (e : Bool) (w : List (Fin 2 × Bool)) : List (Fin 2 × Bool) :=
  if e then alphaU w else w

@[expose] def nfStep (p : List (Fin 2 × Bool) × Bool) (x : Fin 6 × Bool) :
    List (Fin 2 × Bool) × Bool :=
  if x.2 then (p.1 ++ alphaIf p.2 (genW x.1.val).1, xor p.2 (genW x.1.val).2)
  else (p.1 ++ alphaIf (xor p.2 (genW x.1.val).2) (FreeGroup.invRev (genW x.1.val).1),
    xor p.2 (genW x.1.val).2)

@[expose] def nfOf (L : List (Fin 6 × Bool)) : List (Fin 2 × Bool) × Bool :=
  L.foldl nfStep ([], false)

@[expose] def invA : List (Fin 6 × Bool) :=
  [(3, true), (2, true), (5, true), (1, true), (5, true), (2, true), (3, true), (1, true),
    (2, true), (3, true), (5, false), (1, true), (2, true)]

@[expose] def invB : List (Fin 6 × Bool) :=
  [(5, false), (3, true), (1, true), (5, true), (2, true), (1, true), (5, false), (2, true),
    (3, true), (2, true), (1, true), (5, true), (1, true)]

@[expose] def invU : List (Fin 6 × Bool) := [(3, true)]

@[expose] def cmSpecs : List (List (Fin 2 × Bool) × ℕ × ℕ × ℕ) :=
  relData.map (fun d => ((nfOf d.1.toWord).1, d.2)) ++
    [((nfOf invA).1 ++ [(0, false)], 0, 0, 1), ((nfOf invB).1 ++ [(1, false)], 1, 2, 0),
      ((nfOf invU).1, 0, 0, 0)]

end CFSG.OddStandard.ONanRec.IdCM
