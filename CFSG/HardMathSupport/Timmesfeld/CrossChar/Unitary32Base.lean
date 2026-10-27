module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open

section Aut

variable {K : Type} [Field K] [CharP K 2] [Fintype K]

theorem ringEquiv_mul_self_of_card_four (hK : Fintype.card K = 4) (σ : K ≃+* K) :
    σ * σ = 1 := by
  have hpow : ∀ a : K, a ^ 4 = a := fun a => by
    simpa [hK] using FiniteField.pow_card a
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hroot : ∀ a : K, a ≠ 0 → a ≠ 1 → a ^ 2 + a + 1 = 0 := by
    intro a ha0 ha1
    have h1 : a * ((a - 1) * (a ^ 2 + a + 1)) = 0 := by
      have := hpow a
      linear_combination this
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h ha0
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (sub_eq_zero.1 h) ha1
    · exact h
  ext a
  by_cases ha0 : a = 0
  · simp [ha0]
  by_cases ha1 : a = 1
  · simp [ha1]
  have hb0 : σ a ≠ 0 := fun h => ha0 (σ.injective (by rw [h, map_zero]))
  have hb1 : σ a ≠ 1 := fun h => ha1 (σ.injective (by rw [h, map_one]))
  have hra := hroot a ha0 ha1
  have hrb := hroot (σ a) hb0 hb1
  have hfac : (σ a - a) * (σ a - a - 1) = 0 := by
    linear_combination hrb - hra + (a - σ a) * (a + 1) * h2
  change σ (σ a) = a
  rcases mul_eq_zero.1 hfac with h | h
  · rw [sub_eq_zero.1 h]
    exact sub_eq_zero.1 h
  · have e : σ a = a + 1 := by linear_combination h
    calc σ (σ a) = σ (a + 1) := by rw [← e]
      _ = σ a + 1 := by rw [map_add, map_one]
      _ = a := by rw [e]; linear_combination h2

theorem ringEquiv_eq_one_of_pow_three (hK : Fintype.card K = 4) {σ : K ≃+* K} (h3 : σ ^ 3 = 1) :
    σ = 1 := by
  have h2 := ringEquiv_mul_self_of_card_four hK σ
  calc σ = σ ^ 3 * (σ * σ)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; simp

end Aut

section Plane

variable {G : Type*} [Group G]

theorem exists_plane_containing {D : Subgroup G} (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 27) {x : G} (hx : x ∈ D) (hx1 : x ≠ 1) :
    ∃ E : Subgroup G, E ≤ D ∧ x ∈ E ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  set x' : D := ⟨x, hx⟩ with hx'
  have hx'1 : x' ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hx'3 : orderOf x' = 3 :=
    orderOf_eq_prime (Subtype.ext (hD.2 x hx)) hx'1
  set N : Subgroup D := Subgroup.zpowers x' with hN
  have hNnorm : N.Normal := ⟨fun y hy g => by
    rw [show g * y * g⁻¹ = y from by
      have := hD.1.is_comm.comm g y
      rw [this, mul_inv_cancel_right]]
    exact hy⟩
  have hNc : Nat.card N = 3 := by rw [hN, Nat.card_zpowers, hx'3]
  have hQc : Nat.card (D ⧸ N) = 9 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hcard, hNc] at h1
    omega
  have : Finite (D ⧸ N) := Nat.finite_of_card_ne_zero (by rw [hQc]; norm_num)
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := D ⧸ N) 3 (by rw [hQc]; norm_num)
  set Z : Subgroup (D ⧸ N) := Subgroup.zpowers q with hZ
  have hZc : Nat.card Z = 3 := by rw [hZ, Nat.card_zpowers, hq]
  set E' : Subgroup D := Z.comap (QuotientGroup.mk' N) with hE'
  have hind : E'.index = 3 := by
    rw [hE', Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)]
    have h1 := Subgroup.card_mul_index Z
    rw [hQc, hZc] at h1
    omega
  have hE'c : Nat.card E' = 9 := by
    have h1 := Subgroup.card_mul_index E'
    rw [hcard, hind] at h1
    omega
  refine ⟨E'.map D.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · refine ⟨x', ?_, rfl⟩
    change x' ∈ E'
    rw [hE', Subgroup.mem_comap]
    have : QuotientGroup.mk' N x' = 1 := (QuotientGroup.eq_one_iff x').2 (Subgroup.mem_zpowers x')
    rw [this]
    exact Z.one_mem
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨a', -, ha⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨b', -, hb⟩ := Subgroup.mem_map.1 b.2
      apply Subtype.ext
      change (a : G) * b = b * a
      rw [← ha, ← hb]
      exact congrArg Subtype.val (hD.1.is_comm.comm a' b')
    · obtain ⟨y', -, rfl⟩ := Subgroup.mem_map.1 hy
      exact hD.2 y' y'.2
  · rw [Subgroup.card_map_of_injective D.subtype_injective, hE'c]

end Plane

end CFSG.HardMathSupport.Timmesfeld.CrossChar
