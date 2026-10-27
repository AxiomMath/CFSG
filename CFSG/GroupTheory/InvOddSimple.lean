module

public import CFSG.Quasithin.Vol2.Ch3E213MP3C

public section

namespace CFSG.GroupTheory

open Subgroup

theorem inv_odd_of_simple {G : Type} [Group G] [Finite G] {K : Subgroup G}
    [IsSimpleGroup K] (hK : ¬ IsPGroup 2 K) {t : G}
    (ht : t * t = 1) (htN : t ∈ Subgroup.normalizer (K : Set G))
    (htC : t ∉ Subgroup.centralizer (K : Set G)) :
    ∃ x ∈ K, x ≠ 1 ∧ Odd (orderOf x) ∧ t * x * t⁻¹ = x⁻¹ := by
  obtain ⟨x, hxK, ℓ, b, hℓ, hℓ2, hb, hord, hinv⟩ :=
    CFSG.Quasithin.Ch3E213M.P3.exists_inverted (Y := G) (K₁ := K) hK ht htN htC
  refine ⟨x, hxK, ?_, ?_, ?_⟩
  · intro hx1
    have h1 : orderOf x = 1 := by rw [hx1, orderOf_one]
    rw [hord] at h1
    have hb0 : b ≠ 0 := by omega
    have h2 : 1 < ℓ ^ b := Nat.one_lt_pow hb0 hℓ.one_lt
    omega
  · rw [hord]
    exact (hℓ.odd_of_ne_two hℓ2).pow (n := b)
  · rw [inv_eq_of_mul_eq_one_right ht]
    exact hinv

end CFSG.GroupTheory
