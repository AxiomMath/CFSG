module

public import CFSG.LieType.Chevalley.OddToralInvolutionComponents
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.QPlusModel
public import CFSG.Quasithin.Background.G2URoots
public import CFSG.RankThree.PartOne.KE.EDualStabilizer

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.Chevalley CFSG.Quasithin.G2U
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KE

@[expose] def refl (α δ : Fin Tag.G2.rank → ℤ) : Fin Tag.G2.rank → ℤ :=
  δ - (2 * iform α δ / iform α α) • α

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂]
  {σ : K₂ ≃+* K₂}

namespace QPlusModel

abbrev R (M : QPlusModel K σ) (β : Fin Tag.G2.rank → ℤ) : Subgroup (ModGL .G2 K₂) :=
  rootRankOneGroup .G2 K₂ β ⊓ M.gamma

theorem R_le_centralizer (M : QPlusModel K σ) {β : Fin Tag.G2.rank → ℤ} (hβ : IsRoot .G2 β)
    {a : Fin Tag.G2.rank → K₂ˣ} (ha : rootChar a β = 1) :
    M.R β ≤ M.gamma ⊓ Subgroup.centralizer {rootDiagUnit .G2 a} := by
  have hβ' : β ∈ rootCharKernel a := ⟨hβ, ha⟩
  have hnβ : -β ∈ rootCharKernel a :=
    ⟨IsRoot.neg hβ, by rw [rootChar_neg_eq_inv, ha, inv_one]⟩
  have hle : rootRankOneGroup .G2 K₂ β ≤ toralCentralizer .G2 K₂ a := by
    rw [(exceptional_Lang_root_rank_one_torus_transport .G2 K₂ hβ).1]
    exact sup_le
      ((rootSubgroup_le_rootSpan hβ').trans (rootSpan_rootCharKernel_le_toralCentralizer a))
      ((rootSubgroup_le_rootSpan hnβ).trans (rootSpan_rootCharKernel_le_toralCentralizer a))
  exact fun x hx => ⟨hx.2, (hle hx.1).2⟩

theorem rootReflection_smul_eq_refl (L : Type) [Field L] {α δ : Fin Tag.G2.rank → ℤ}
    (hα : IsRoot .G2 α) : rootReflection α • δ = refl α δ :=
  ((exceptional_Lang_root_rank_one_torus_transport .G2 L hα).2.2.2.1 δ).1

variable [Finite K₂]

end QPlusModel

end CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding
