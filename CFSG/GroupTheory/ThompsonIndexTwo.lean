module

public import CFSG.GH74.GLS.Bg.Local.Transfer1515
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.ThompsonIndexTwo

open CFSG.GH74.GLS.Bg.Thompson

variable {G : Type*} [Group G]

theorem inv_mul_mem_of_not_mem {T U : Subgroup G} (hUidx : U.relIndex T = 2) {a b : G}
    (haT : a ∈ T) (hbT : b ∈ T) (haU : a ∉ U) (hbU : b ∉ U) : a⁻¹ * b ∈ U := by
  have key := (Subgroup.mul_mem_iff_of_index_two (H := U.subgroupOf T) hUidx
    (a := (⟨a, haT⟩ : T)⁻¹) (b := ⟨b, hbT⟩)).2 (by
      rw [inv_mem_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact iff_of_false haU hbU)
  exact Subgroup.mem_subgroupOf.1 key

variable [Finite G]

theorem exists_normal_index_two_of_thompson {T U : Subgroup G} (hT : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index) (hUT : U ≤ T) (hUidx : U.relIndex T = 2) {x : G} (hxT : x ∈ T)
    (hxU : x ∉ U) (hmin : ∀ y ∈ T, y ∉ U → orderOf x ≤ orderOf y)
    (hconj : ∀ g : G, g⁻¹ * x * g ∉ U) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
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
    ⟨N, hN, -, hNp, hxN⟩ | ⟨g, hg, -, -⟩
  · have := hN
    have : Group.IsNilpotent (G ⧸ N) := hNp.isNilpotent
    have hbt : (⊥ : Subgroup (G ⧸ N)) ≠ ⊤ := by
      intro h
      apply hxN
      have h1 : (QuotientGroup.mk x : G ⧸ N) ∈ (⊥ : Subgroup (G ⧸ N)) := by
        rw [h]
        exact Subgroup.mem_top _
      exact (QuotientGroup.eq_one_iff x).1 (Subgroup.mem_bot.1 h1)
    obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subgroup (G ⧸ N))).resolve_left hbt
    have hMidx : M.index = 2 := (IsPGroup.isCoatom_iff_index_eq_prime hNp).1 hM
    refine ⟨M.comap (QuotientGroup.mk' N), (Subgroup.normal_of_index_eq_two hMidx).comap _, ?_⟩
    exact (Subgroup.index_comap_of_surjective M (f := QuotientGroup.mk' N)
      QuotientGroup.mk_surjective).trans hMidx
  · exact absurd hg (hconj g)

end CFSG.ThompsonIndexTwo
