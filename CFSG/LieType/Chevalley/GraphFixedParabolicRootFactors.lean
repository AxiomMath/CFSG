module

public import CFSG.LieType.Chevalley.ParabolicRootFactorData
public import CFSG.LieType.Chevalley.GraphFixedOrbitParametrization

public noncomputable section

namespace CFSG.Blueprint.Chevalley.TwistTag

variable (t : TwistTag)

@[expose] def orbitUnion (J : Set (Fin t.foldedTag.rank)) : Set (Fin t.tag.rank) :=
  ⋃ a ∈ J, (t.orbit a : Set (Fin t.tag.rank))

theorem mem_orbitUnion {J : Set (Fin t.foldedTag.rank)} {i : Fin t.tag.rank} :
    i ∈ t.orbitUnion J ↔ ∃ a ∈ J, i ∈ t.orbit a := by
  simp [orbitUnion]

end CFSG.Blueprint.Chevalley.TwistTag

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

variable (t : TwistTag) (K : Type) [Field K] (σ : K →+* K)

@[expose] def graphFixedParabolicRadical
    (J : Set (Fin t.foldedTag.rank)) :
    Subgroup (ModGL t.tag K) :=
  parabolicRadical t.tag K (t.orbitUnion J) ⊓ twistedFixedGroup t K σ

@[expose] def graphFixedParabolicLevi
    (J : Set (Fin t.foldedTag.rank)) :
    Subgroup (ModGL t.tag K) :=
  parabolicLevi t.tag K (t.orbitUnion J) ⊓ graphFixedRootGroup t K σ

@[expose] def graphFixedParabolicLeviUnipotent
    (J : Set (Fin t.foldedTag.rank)) :
    Subgroup (ModGL t.tag K) :=
  parabolicLeviUnipotent t.tag K (t.orbitUnion J) ⊓ twistedFixedGroup t K σ

@[expose] def graphFixedParabolicRadicalGe
    (J : Set (Fin t.foldedTag.rank)) (h : ℤ) :
    Subgroup (ModGL t.tag K) :=
  parabolicRadicalGe t.tag K (t.orbitUnion J) h ⊓ twistedFixedGroup t K σ

variable (J : Set (Fin t.foldedTag.rank))

theorem graphFixedParabolicRadical_le :
    graphFixedParabolicRadical t K σ J ≤ graphFixedPosUnipotent t K σ :=
  inf_le_inf_right _ (rootSpan_mono fun _ h => h.1)

theorem graphFixedParabolicLeviUnipotent_le :
    graphFixedParabolicLeviUnipotent t K σ J ≤ graphFixedPosUnipotent t K σ :=
  inf_le_inf_right _ (rootSpan_mono fun _ h => h.2)

theorem graphFixedParabolicRadicalGe_le
    (h : ℤ) :
    graphFixedParabolicRadicalGe t K σ J h ≤ graphFixedParabolicRadical t K σ J :=
  inf_le_inf_right _ (rootSpan_mono fun _ h => h.1)

theorem graphFixedParabolicRadical_le_graphFixedRootGroup :
    graphFixedParabolicRadical t K σ J ≤ graphFixedRootGroup t K σ :=
  (graphFixedParabolicRadical_le t K σ J).trans
    (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ)

theorem graphFixedParabolicLeviUnipotent_le_graphFixedRootGroup :
    graphFixedParabolicLeviUnipotent t K σ J ≤ graphFixedRootGroup t K σ :=
  (graphFixedParabolicLeviUnipotent_le t K σ J).trans
    (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ)

theorem graphFixedParabolicRadicalGe_le_graphFixedRootGroup
    (h : ℤ) :
    graphFixedParabolicRadicalGe t K σ J h ≤ graphFixedRootGroup t K σ :=
  (graphFixedParabolicRadicalGe_le t K σ J h).trans
    (graphFixedParabolicRadical_le_graphFixedRootGroup t K σ J)

theorem graphFixedParabolicLevi_le
    : graphFixedParabolicLevi t K σ J ≤ graphFixedRootGroup t K σ :=
  inf_le_right

end CFSG.LieType.Chevalley
