module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem exists_conj_of_order_three {G : Type*} [Group G] [Finite G] {W : Subgroup G}
    (hW : Nat.card W = 1920) {a b : G} (ha : a ∈ W) (hb : b ∈ W) (ha3 : orderOf a = 3)
    (hb3 : orderOf b = 3) : ∃ w ∈ W, w * a * w⁻¹ = b ∨ w * a * w⁻¹ = b⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let a' : W := ⟨a, ha⟩
  let b' : W := ⟨b, hb⟩
  have ha'3 : orderOf a' = 3 := by rw [← Subgroup.orderOf_coe]; exact ha3
  have hb'3 : orderOf b' = 3 := by rw [← Subgroup.orderOf_coe]; exact hb3
  have hcard : ∀ x : W, orderOf x = 3 → Nat.card (zpowers x) = 3 := fun x hx => by
    rw [Nat.card_zpowers, hx]
  have hp : ∀ x : W, orderOf x = 3 → IsPGroup 3 (zpowers x) := fun x hx =>
    IsPGroup.of_card (n := 1) (by rw [hcard x hx]; norm_num)
  have hidx : ∀ x : W, orderOf x = 3 → ¬ 3 ∣ (zpowers x).index := fun x hx => by
    have h1 := Subgroup.index_mul_card (H := zpowers x)
    rw [hcard x hx, hW] at h1
    have : (zpowers x).index = 640 := by omega
    rw [this]; norm_num
  let SA : Sylow 3 W := (hp a' ha'3).toSylow (hidx a' ha'3)
  let SB : Sylow 3 W := (hp b' hb'3).toSylow (hidx b' hb'3)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W SA SB
  have hmem : g * a' * g⁻¹ ∈ zpowers b' := by
    have h2 : g * a' * g⁻¹ ∈ ((g • SA : Sylow 3 W) : Subgroup W) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨a', mem_zpowers a', by rw [MulAut.smul_def, MulAut.conj_apply]⟩
    rw [hg] at h2
    exact h2
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
  have hord : orderOf (g * a' * g⁻¹) = 3 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g) a'
    rw [MulAut.conj_apply] at this
    rw [this, ha'3]
  have hb3' : b' ^ 3 = 1 := by rw [← hb'3]; exact pow_orderOf_eq_one b'
  have hk' : b' ^ (k % 3) = g * a' * g⁻¹ := by
    rw [← hk, ← zpow_mod_orderOf b' k, hb'3]
    norm_cast
  refine ⟨g, g.2, ?_⟩
  have hkm : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hkm with h0 | h1 | h2
  · exfalso
    rw [h0, zpow_zero] at hk'
    rw [← hk', orderOf_one] at hord
    omega
  · rw [h1, zpow_one] at hk'
    left
    have := congrArg Subtype.val hk'
    simpa using this.symm
  · rw [h2] at hk'
    right
    have h3 : b' ^ (2 : ℤ) = b'⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [zpow_two, ← pow_two, ← pow_succ]
      exact hb3'
    rw [h3] at hk'
    have := congrArg Subtype.val hk'
    simpa using this.symm

end CFSG.EvenSporadicStandard.Fin76b
