module

public import CFSG.ClassicalInvolution.Phan.Phan3B3Data
public import Certificates.Data.CFSGNative.CosetTable.Enum

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.CosetTable

@[expose] def b3Sp4Rels : List (List (Fin 4 × Bool)) :=
  b3SpCodes.map fun c => decodeWord 4 (c.map (· - 4))

@[expose] def b3Su2Codes : List (List Nat) :=
  [[], [0], [1], [2], [3], [0, 0], [0, 2], [0, 3], [1, 2], [1, 3], [2, 0], [2, 1], [3, 0], [3, 1],
    [0, 0, 2], [0, 0, 3], [0, 2, 0], [0, 2, 1], [0, 3, 0], [0, 3, 1], [2, 0, 3], [2, 1, 3],
    [3, 0, 2], [3, 1, 2]]

@[expose] def twIdx : Fin 2 → Fin 6 := ![2, 3]

@[expose] def twWord (k : Fin 24) : List (Fin 6 × Bool) :=
  (decodeWord 2 (b3Su2Codes.getD k.val [])).map fun l => (twIdx l.1, l.2)

@[expose] def twSubst (k₁ k₂ : Fin 24) (l : Fin 4 × Bool) : List (Fin 6 × Bool) :=
  if l.1.val = 0 then (if l.2 then twWord k₁ else invWord (twWord k₁))
  else if l.1.val = 1 then (if l.2 then twWord k₂ else invWord (twWord k₂))
  else if l.1.val = 2 then [(4, l.2)] else [(5, l.2)]

@[expose] def b3TwistRels (k₁ k₂ : Fin 24) : List (List (Fin 6 × Bool)) :=
  su3Codes.map (decodeWord 6) ++ b3Sp4Rels.map (List.flatMap (twSubst k₁ k₂)) ++
    b3CommCodes.map (decodeWord 6)

@[expose] def b3BadPairs : List (Fin 24 × Fin 24) :=
  [(20, 3), (20, 7), (20, 8), (20, 19), (21, 4), (21, 11), (21, 12), (21, 17), (22, 3), (22, 11),
    (22, 12), (22, 19), (23, 4), (23, 7), (23, 8), (23, 17)]

end CFSG.ClassicalInvolution.Phan.Q3G
