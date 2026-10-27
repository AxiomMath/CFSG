module

public import CFSG.GH74.Generic.S45.LOddG
public import CFSG.GH74.Generic.S45.LPsl2Lin
public import CFSG.GH74.Generic.S45.LPsl2Cover
public import CFSG.GH74.Generic.S45.LPsl2Field

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.GH74.GLS Subgroup
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.AutL2Facts CFSG.GorensteinWalter
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.LieType.Steinberg

theorem oddRow_psl2
    {K : Type} [Group K] [Finite K] {y : MulAut K} {L : Subgroup K} (hyp : Hyp1310 K y L)
    {r f : ℕ} (hr2 : r ≠ 2) (hmodel : StatedClassicalModel (K ⧸ center K) .PSL 2 r f) : False := by
  by_cases hZ : Subgroup.center K = ⊥
  swap
  · exact hyp.false_of_center_ne_bot_psl2 hr2 hmodel hZ
  obtain ⟨yb, Lb, q, hyb, hQ, -⟩ := hyp.quot_data
  obtain ⟨⟨hp, hf, -, -, -⟩, F, _, _, hF, ⟨e₀⟩⟩ := hmodel
  have hodd : IsOddPrimePower (Nat.card F) := isOddPrimePower_of hp hr2 hf hF
  have hk : ringChar F ≠ 2 := ringChar_ne_two_of_card_eq_pow hp hr2 hF
  let e : K ⧸ center K ≃* PSL2 F :=
    e₀.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have hg : orderOf (autEquiv e yb) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [pow_two]; exact hQ.sq) hQ.ne
  by_cases hfield : (autEquiv e yb).right = 1
  ·
    have hgl : autEquiv e yb = SemidirectProduct.inl (autEquiv e yb).left := by
      have h := SemidirectProduct.inl_left_mul_inr_right (autEquiv e yb)
      rw [hfield, map_one, mul_one] at h
      exact h.symm
    exact psl2_linear_false hodd e hQ hgl
  ·
    obtain ⟨x, hx, hx4⟩ := exists_fixed_order_four_of_field hodd hk (autEquiv e yb) hg hfield
    have hxS : yb (e.symm x) = e.symm x := by
      have h := semilinearAction_autEquiv_apply e yb (e.symm x)
      rw [MulEquiv.apply_symm_apply, hx] at h
      apply e.injective
      rw [← h, MulEquiv.apply_symm_apply]
    have h4 : 4 ∣ orderOf (e.symm x) := by
      rw [MulEquiv.orderOf_eq, hx4]
    exact hyp.false_of_fixed_order_four_of_center_bot hZ hyb hxS h4

theorem oddRowG_PSL2 : OddRowG_PSL2 :=
  fun _ _ _ _ _ hypg _ _ hr2 hmodel => oddRow_psl2 hypg.2 hr2 hmodel

end CFSG.GH74.Generic.S45
