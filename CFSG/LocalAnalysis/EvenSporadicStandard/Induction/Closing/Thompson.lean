module

public import CFSG.GroupTheory.ThompsonIndexTwo

public section

namespace CFSG.EvenSporadicStandard.Induction.Closing

open CFSG.GH74.GLS.Bg.Thompson CFSG.ThompsonIndexTwo

variable {G : Type*} [Group G] [Finite G]

theorem exists_normal_cyclic_two_quotient_of_thompson {T U : Subgroup G} (hT : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index) (hUT : U ≤ T) (hUidx : U.relIndex T = 2) {x : G} (hxT : x ∈ T)
    (hxU : x ∉ U) (hmin : ∀ y ∈ T, y ∉ U → orderOf x ≤ orderOf y)
    (hconj : ∀ g : G, g⁻¹ * x * g ∉ U) :
    ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ IsPGroup 2 (G ⧸ N) ∧ x ∉ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (U.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hUidx
  have hQn : ∀ t ∈ T, ∀ q ∈ U, t * q * t⁻¹ ∈ U := fun t ht q hq =>
    Subgroup.mem_subgroupOf.1
      (hn.conj_mem ⟨q, hUT hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨t, ht⟩)
  have hcyc : ∃ b ∈ T, ∀ t ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ U := by
    refine ⟨x, hxT, fun t ht => ?_⟩
    by_cases htU : t ∈ U
    · exact ⟨0, by simpa using htU⟩
    · exact ⟨1, by simpa using inv_mul_mem_of_not_mem hUidx hxT ht hxU htU⟩
  have hord2 : 2 ∣ orderOf x := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hT (⟨x, hxT⟩ : T)
    have hk' : orderOf x = 2 ^ k := (Subgroup.orderOf_coe (⟨x, hxT⟩ : T)).trans hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      have hx1 : x = 1 := orderOf_eq_one_iff.1 (hk'.trans (pow_zero 2))
      exact hxU (by rw [hx1]; exact U.one_mem)
    rw [hk']
    exact dvd_pow_self 2 hk0
  have hb : ∀ (g : G) (k : ℕ), g⁻¹ * x ^ (2 * k) * g ∈ T → g⁻¹ * x ^ (2 * k) * g ∈ U := by
    intro g k hgT
    by_contra hgU
    have hle := hmin _ hgT hgU
    have hpow : (x ^ (2 * k)) ^ orderOf (x ^ 2) = 1 := by
      rw [pow_mul x 2 k, pow_right_comm (x ^ 2) k, pow_orderOf_eq_one, one_pow]
    have hdvd : orderOf (g⁻¹ * x ^ (2 * k) * g) ∣ orderOf (x ^ 2) := by
      apply orderOf_dvd_of_pow_eq_one
      have hc := conj_pow (a := g⁻¹) (b := x ^ (2 * k)) (i := orderOf (x ^ 2))
      rw [inv_inv] at hc
      rw [hc, hpow]
      group
    have h2 : orderOf (x ^ 2) = orderOf x / 2 := orderOf_pow_of_dvd (by norm_num) hord2
    have h3 : orderOf (g⁻¹ * x ^ (2 * k) * g) ≤ orderOf (x ^ 2) :=
      Nat.le_of_dvd (orderOf_pos _) hdvd
    have h4 := orderOf_pos x
    omega
  have hc : ∀ g : G, g⁻¹ * x * g ∈ T → IsExtremalIn 2 T (g⁻¹ * x * g) →
      g⁻¹ * x * g ∈ U ∨ x⁻¹ * (g⁻¹ * x * g) ∈ U := by
    intro g hgT _
    by_cases hgU : g⁻¹ * x * g ∈ U
    · exact Or.inl hgU
    · exact Or.inr (inv_mul_mem_of_not_mem hUidx hxT hgT hxU hgU)
  rcases thompson_transfer_1515 (p := 2) hT hTidx hQn hcyc hxT hxU hb hc with
    ⟨N, hN, hNc, hNp, hxN⟩ | ⟨g, hg, -, -⟩
  · exact ⟨N, hN, hNc, hNp, hxN⟩
  · exact absurd hg (hconj g)

end CFSG.EvenSporadicStandard.Induction.Closing
