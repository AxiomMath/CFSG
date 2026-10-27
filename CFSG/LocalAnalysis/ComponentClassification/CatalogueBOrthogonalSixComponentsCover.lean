module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixKernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBCentralQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsDomain

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSix

open CatalogueBOrthogonalFourNonsplit

universe u

variable {K : Type u} [Field K] (delta : K) [Fact (¬ IsSquare delta)]

@[expose] def sixSpecialCover (h2 : (2 : K) ≠ 0) :
    sixSpecialUnitary delta →* (sixSpecialKappa delta h2).range :=
  (sixSpecialKappa delta h2).rangeRestrict

theorem sixSpecialCover_surjective (h2 : (2 : K) ≠ 0) :
    Function.Surjective (sixSpecialCover delta h2) :=
  (sixSpecialKappa delta h2).rangeRestrict_surjective

theorem sixSpecialCover_kernel_iff (h2 : (2 : K) ≠ 0) (g : sixSpecialUnitary delta) :
    g ∈ (sixSpecialCover delta h2).ker ↔ g = 1 ∨ g = sixSpecialNegIdentity delta := by
  constructor
  · intro hg
    apply (sixSpecialKappa_kernel_iff delta h2 g).mp
    exact congrArg Subtype.val (show sixSpecialCover delta h2 g = 1 from hg)
  · intro hg
    apply (sixSpecialCover delta h2).mem_ker.mpr
    apply Subtype.ext
    exact (sixSpecialKappa_kernel_iff delta h2 g).mpr hg

theorem sixSpecialCover_kernel_central (h2 : (2 : K) ≠ 0) :
    (sixSpecialCover delta h2).ker ≤ Subgroup.center (sixSpecialUnitary delta) := by
  intro g hg
  apply sixSpecialKappa_kernel_central delta h2
  exact congrArg Subtype.val (show sixSpecialCover delta h2 g = 1 from hg)

variable [Finite K]

theorem sixSpecialCover_pComponent_lift (h2 : (2 : K) ≠ 0) (p : ℕ) [Fact p.Prime]
    (L : Subgroup (sixSpecialKappa delta h2).range) (hL : CFSG.IsPComponent p L) :
    ∃ J : Subgroup (sixSpecialUnitary delta), CFSG.IsPComponent p J ∧
      J.map (sixSpecialCover delta h2) = L ∧
      (CFSG.IsQuasisimple J ↔ CFSG.IsQuasisimple L) := by
  let f := sixSpecialCover delta h2
  obtain ⟨J, hJ, hmap, _⟩ := CatalogueBCentralQuotient.pComponent_exists_lift p f
    (sixSpecialCover_surjective delta h2) (sixSpecialCover_kernel_central delta h2) L hL
  refine ⟨J, hJ, hmap, ?_⟩
  have hi := CatalogueBCentralQuotient.pComponent_quasisimple_iff f
    (sixSpecialCover_kernel_central delta h2) p J hJ
  rwa [hmap] at hi

end CFSG.ComponentClassification.CatalogueBOrthogonalSix
