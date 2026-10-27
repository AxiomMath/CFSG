module

public import CFSG.LieType.Multipliers.L34Data
public import CFSG.Certificates.WordSubgroup

public section

namespace CFSG.LieType.Multipliers.L34Upper

open CFSG.Fischer CFSG.CosetTable CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

@[expose] def hopfWs : List (List (Fin 2 × Bool)) :=
  coverWords rels fun i => commWords (coverPairs i)

@[expose] def dMat : Mat3 := diagMat ⟨2⟩ 1 1

@[expose] def dInvMat : Mat3 := diagMat ⟨3⟩ 1 1

@[expose] def uA : List (Fin 2 × Bool) := parseWord "babbaBBaBababbaBBaB"

@[expose] def uB : List (Fin 2 × Bool) := parseWord "BababbaBBaBAbb"

@[expose] def deltaWs : List (List (Fin 2 × Bool)) :=
  [substWord [uA, uB] (commWords (coverPairs 0)), substWord [uA, uB] (commWords (coverPairs 1))]

@[expose] def deltaWalks : List (List (Fin 2 × Bool) × ℕ) :=
  [(substWord deltaWs zOne ++ FreeGroup.invRev zTwo, 1),
    (substWord deltaWs zTwo ++ zOne ++ zTwo, 1)]

end CFSG.LieType.Multipliers.L34Upper
