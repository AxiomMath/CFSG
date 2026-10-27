module

public import CFSG.LieType.HighestRoot.CentChevalleyThree
public import CFSG.LieType.HighestRoot.CentChevalleyData
public import CFSG.ClassicalInvolution.ModelFacts.Families
public import CFSG.LieType.Steinberg.Adjoint.Presentation

public section

namespace CFSG.LieType.HighestRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.ClassicalInvolution.ModelFacts

variable {K : Type} [Field K] [Finite K]

theorem highestRootCZ_F4
    (hK : ringChar K ≠ 2) : HighestRootCZ (f4Datum K) K :=
  highestRootCZ_adjDatum noG2_F4 hK symmetrizer_le_F4 isolatedCheck_F4
    (isLongest_single_F4 rfl _ (k := idx0 .F4) (by decide)).2

theorem highestRootCZ_E8
    (hK : ringChar K ≠ 2) : HighestRootCZ (e8Datum K) K :=
  highestRootCZ_adjDatum noG2_E8 hK (symmetrizer_le_one .E8 rfl _) isolatedCheck_E8
    (isLongest_single_E8 rfl _ (idx0 .E8)).2

end CFSG.LieType.HighestRoot
