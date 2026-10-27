module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionProductComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionComponentsTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinear

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBProjectiveInvolutionProduct

variable {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]

theorem pComponent_quasisimple_product (p : ℕ) [Fact p.Prime]
    (hX : ∀ J : Subgroup X, CFSG.IsPComponent p J → CFSG.IsQuasisimple J)
    (hY : ∀ J : Subgroup Y, CFSG.IsPComponent p J → CFSG.IsQuasisimple J)
    (L : Subgroup (X × Y)) (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  rcases pComponent_eq_left_or_right_factor p L hL with hleft | hright
  · let N := (⊤ : Subgroup X).prod (⊥ : Subgroup Y)
    let : N.Normal := Subgroup.prod_normal _ _
    have hLN : L ≤ N := hleft.le.trans (Subgroup.prod_mono le_top le_rfl)
    let e : N ≃* X := (leftFactorEquiv (⊤ : Subgroup X)).trans Subgroup.topEquiv
    have hrestricted := CatalogueBFixedCentralQuotient.pComponent_restrict_normal p N L hLN hL
    have hquasi := CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p e hX
      (L.subgroupOf N) hrestricted
    exact CatalogueBAlternating.quasisimple_iff_native.mpr
      (Components.quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe hLN).symm
        (CatalogueBAlternating.quasisimple_iff_native.mp hquasi))
  · let N := (⊥ : Subgroup X).prod (⊤ : Subgroup Y)
    let : N.Normal := Subgroup.prod_normal _ _
    have hLN : L ≤ N := hright.le.trans (Subgroup.prod_mono le_rfl le_top)
    let e : N ≃* Y := (rightFactorEquiv (⊤ : Subgroup Y)).trans Subgroup.topEquiv
    have hrestricted := CatalogueBFixedCentralQuotient.pComponent_restrict_normal p N L hLN hL
    have hquasi := CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p e hY
      (L.subgroupOf N) hrestricted
    exact CatalogueBAlternating.quasisimple_iff_native.mpr
      (Components.quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe hLN).symm
        (CatalogueBAlternating.quasisimple_iff_native.mp hquasi))

theorem generalLinear_product_pComponent_quasisimple
    (r s : ℕ) (K : Type*) [Field K] [Finite K] (hr : 1 ≤ r) (hs : 1 ≤ s)
    (p : ℕ) (hp : p.Prime)
    (L : Subgroup (Matrix.GeneralLinearGroup (Fin r) K × Matrix.GeneralLinearGroup (Fin s) K))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let : Fact p.Prime := ⟨hp⟩
  exact pComponent_quasisimple_product p
    (CatalogueBGeneralLinear.pComponent_quasisimple r K hr p)
    (CatalogueBGeneralLinear.pComponent_quasisimple s K hs p) L hL

end CFSG.ComponentClassification.CatalogueBProjectiveInvolutionProduct
