module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsUnitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryComponents

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSix

open Matrix CatalogueBOrthogonalFourNonsplit

universe u

variable {K : Type u} [Field K] [Finite K] (delta : K)

instance sixExtensionFinite : Finite (extension delta) :=
  Finite.of_equiv (K × K) (QuadraticAlgebra.equivProd delta 0).symm

instance sixSpecialUnitaryFinite : Finite (sixSpecialUnitary delta) :=
  Finite.of_injective (fun g : sixSpecialUnitary delta => g.val.val)
    (Units.val_injective.comp Subtype.val_injective)

instance sixIsometriesFinite : Finite (SixIsometries delta) := by
  apply Finite.of_injective
    (fun g : SixIsometries delta => (g.val : sixSubmodule delta → sixSubmodule delta))
  intro g h heq
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  exact congrFun heq X

variable [Fact (¬ IsSquare delta)]

theorem sixSpecialUnitary_pComponent_eq_top (h2 : (2 : K) ≠ 0)
    (p : ℕ) (L : Subgroup (sixSpecialUnitary delta)) (hL : CFSG.IsPComponent p L) :
    L = ⊤ :=
  CatalogueBAlternatingIsometry.pComponent_eq_top_of_quasisimple
    (sixSpecialUnitary_quasisimple delta h2) p L hL

theorem sixSpecialUnitary_pComponent_quasisimple (h2 : (2 : K) ≠ 0)
    (p : ℕ) (L : Subgroup (sixSpecialUnitary delta)) (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple L := by
  have htop := sixSpecialUnitary_pComponent_eq_top delta h2 p L hL
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)
      (CatalogueBAlternating.quasisimple_iff_native.mp
        (sixSpecialUnitary_quasisimple delta h2)))

end CFSG.ComponentClassification.CatalogueBOrthogonalSix
