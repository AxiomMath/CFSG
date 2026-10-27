module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevRadicalSimple
public import CFSG.Blueprint.Catalog
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevRadicalOfChar
import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharStated
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.OrthPlus
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.OrthMinus
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.OrthCharTwo

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Blueprint

theorem chevParabolicRadicalSimple_of_statedClassicalModel {K : Type} [Group K] [Finite K]
    {t : StatedLieTag} {n f : ℕ} (hK : IsSimpleGroup K) (ht : t ∈ classicalTags)
    (h : StatedClassicalModel K t n 2 f) : ChevParabolicRadicalSimple K := by
  cases t <;> first | exact absurd ht (by decide) | skip
  case PSL =>
    exact chevParabolicRadicalSimple_of_ggNormalizerOvergroupsChar hK
      (StandardType.ggNormalizerOvergroupsChar_of_statedClassicalModel_psl h)
  case PSU =>
    exact chevParabolicRadicalSimple_of_ggNormalizerOvergroupsChar hK
      (StandardType.ggNormalizerOvergroupsChar_of_statedClassicalModel_psu h)
  case PSp =>
    exact chevParabolicRadicalSimple_of_ggNormalizerOvergroupsChar hK
      (StandardType.ggNormalizerOvergroupsChar_of_statedClassicalModel_psp h)
  case POmegaOdd => exact absurd rfl h.1.2.2.2
  case POmegaPlus =>
    exact chevParabolicRadicalSimple_of_overgroups hK
      ((Quasithin.LieOver.asLieTwoAt_pOmegaPlus_of_gaps Quasithin.LieOver.pOmegaPlusCover_holds
        Quasithin.LieOver.pOmegaPlusCharTwo_holds Quasithin.LieOver.pOmegaPlusCoatom_holds)
        n f K hK h.1 (Or.inl ⟨ht, h⟩)).1
  case POmegaMinus =>
    exact chevParabolicRadicalSimple_of_overgroups hK
      ((Quasithin.LieOver.asLieTwoAt_pOmegaMinus_of_gaps Quasithin.LieOver.pOmegaMinusCover_holds
        Quasithin.LieOver.pOmegaMinusCharTwo_holds Quasithin.LieOver.pOmegaMinusCoatom_holds)
        n f K hK h.1 (Or.inl ⟨ht, h⟩)).1

end CFSG.GroupTheory
