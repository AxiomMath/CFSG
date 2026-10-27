module

public import CFSG.RankThree.Literature.FSmithForm
public import CFSG.Assembly.LowTwoRankDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open Subgroup CFSG.RankThree.Literature.FSmith

theorem compat_central {C C' : Type} [Group C] [Group C'] {Q : Subgroup C} {Q' : Subgroup C'}
    [hQn : Q.Normal] [hQn' : Q'.Normal]
    [Module (ZMod 2) (Additive (Abelianization Q))] [Module (ZMod 2) (Additive (Abelianization Q'))]
    (hE' : IsExtraspecialPGroup 2 Q')
    (a : Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q')) (φ₀ : ↥Q ≃* ↥Q')
    (hφ : ∀ x : ↥Q, a (Additive.ofMul (Abelianization.of x)) =
      Additive.ofMul (Abelianization.of (φ₀ x)))
    (l : C) (l' : C')
    (hint : ∀ v, a (conjLinEquiv hQn l v) = conjLinEquiv hQn' l' (a v)) (x : ↥Q) :
    φ₀ (conjAut hQn l x) * (conjAut hQn' l' (φ₀ x))⁻¹ ∈ Subgroup.center ↥Q' := by
  have hclass : Additive.ofMul (Abelianization.of (φ₀ (conjAut hQn l x))) =
      Additive.ofMul (Abelianization.of (conjAut hQn' l' (φ₀ x))) := by
    calc Additive.ofMul (Abelianization.of (φ₀ (conjAut hQn l x)))
        = a (Additive.ofMul (Abelianization.of (conjAut hQn l x))) :=
            (hφ (conjAut hQn l x)).symm
      _ = a (conjLinEquiv hQn l (Additive.ofMul (Abelianization.of x))) :=
            congrArg a (conjLinEquiv_apply hQn l x).symm
      _ = conjLinEquiv hQn' l' (a (Additive.ofMul (Abelianization.of x))) :=
            hint _
      _ = conjLinEquiv hQn' l' (Additive.ofMul (Abelianization.of (φ₀ x))) := by
            rw [hφ x]
      _ = Additive.ofMul (Abelianization.of (conjAut hQn' l' (φ₀ x))) :=
            conjLinEquiv_apply hQn' l' (φ₀ x)
  have h0 : Additive.ofMul (Abelianization.of
      (φ₀ (conjAut hQn l x) * (conjAut hQn' l' (φ₀ x))⁻¹)) = 0 := by
    rw [ofMul_of_mul, map_inv, ofMul_inv, hclass, add_neg_cancel]
  exact (ofMul_of_eq_zero_iff hE' _).mp h0

end CFSG.EvenSporadicStandard.HNRecog.ML1
