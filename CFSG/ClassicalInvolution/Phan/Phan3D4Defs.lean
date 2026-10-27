module

public import CFSG.ClassicalInvolution.Phan.Phan3D4Data
public import CFSG.Certificates.CosetTablePresented
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.CosetTable

abbrev PhanD4Group : Type := PG 8 phanD4Rels

@[expose] def sl3EdgeRels (i j : Nat) : List (List (Fin 8 × Bool)) :=
  sl3Codes.map fun w => decodeWord 8 (w.map fun c =>
    2 * ([2 * i, 2 * i + 1, 2 * j, 2 * j + 1].getD (c / 2) 0) + c % 2)

@[expose] def ctCommRels (i j : Nat) : List (List (Fin 8 × Bool)) :=
  [(0, 0), (0, 1), (1, 0), (1, 1)].map fun uv =>
    decodeWord 8 [2 * (2 * i + uv.1), 2 * (2 * j + uv.2), 2 * (2 * i + uv.1) + 1,
      2 * (2 * j + uv.2) + 1]

@[expose] def sl3Rels : List (List (Fin 4 × Bool)) := sl3Codes.map (decodeWord 4)

@[expose] noncomputable def ctEltP (k : Fin 8) : PhanD4Group :=
  PresentedGroup.mk _ (FreeGroup.mk (decodeWord 8 ctInPhanCodes[k.val]!))

@[expose] def d4CtRels : List (List (Fin 8 × Bool)) :=
  sl3EdgeRels 0 1 ++ sl3EdgeRels 1 2 ++ sl3EdgeRels 1 3 ++ ctCommRels 0 2 ++ ctCommRels 0 3 ++
    ctCommRels 2 3

end CFSG.ClassicalInvolution.Phan.Q3G

end
