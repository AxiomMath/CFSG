module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.TwoFi22

open scoped Pointwise

theorem exists_conj_mem_of_odd_index {G : Type*} [Group G] [Finite G] {N T : Subgroup G}
    (hT : IsPGroup 2 T) (hidx : ¬ 2 ∣ (T.subgroupOf N).index) {x : G} (hx : x ∈ N)
    (hxp : ∃ n : ℕ, x ^ 2 ^ n = 1) : ∃ c ∈ N, c * x * c⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsPGroup 2 (T.subgroupOf N) := hT.comap_subtype
  obtain ⟨n, hn⟩ := hxp
  have hxn : (⟨x, hx⟩ : N) ^ 2 ^ n = 1 := Subtype.ext hn
  have hE : IsPGroup 2 (Subgroup.zpowers (⟨x, hx⟩ : N)) :=
    IsPGroup.of_card_dvd_pow (n := n) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hxn)
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq N Q (hT'.toSylow hidx)
  refine ⟨(c : G), c.2, ?_⟩
  have h1 : MulAut.conj c • (⟨x, hx⟩ : N) ∈ MulAut.conj c • (Q : Subgroup N) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ (hQ (Subgroup.mem_zpowers _))
  rw [← Sylow.coe_subgroup_smul, hc, IsPGroup.toSylow_coe, MulAut.smul_def,
    MulAut.conj_apply] at h1
  exact h1

theorem exists_conj_mem_of_card {G : Type*} [Group G] [Finite G] {N T : Subgroup G}
    (hTN : T ≤ N) {e m : ℕ} (hT : Nat.card T = 2 ^ e) (hN : Nat.card N = 2 ^ e * m)
    (hm : ¬ 2 ∣ m) {x : G} (hx : x ∈ N) (hxp : ∃ n : ℕ, x ^ 2 ^ n = 1) :
    ∃ c ∈ N, c * x * c⁻¹ ∈ T := by
  refine exists_conj_mem_of_odd_index (IsPGroup.of_card hT) ?_ hx hxp
  have h1 := (T.subgroupOf N).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv, hT, hN] at h1
  have h2 : (T.subgroupOf N).index = m := by
    have h3 : (T.subgroupOf N).index * 2 ^ e = m * 2 ^ e := by rw [h1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) e) h3
  rw [h2]
  exact hm

end CFSG.EvenSporadicStandard.TwoFi22
