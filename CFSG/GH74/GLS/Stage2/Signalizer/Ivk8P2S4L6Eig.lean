module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup

theorem ka6eig_exists_fixed {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {U : Subgroup G}
    (hU : IsPGroup p ↥U) (hU1 : U ≠ ⊥) {e : G} (he : e ∈ normalizer (U : Set G))
    (hep : e ^ p = 1) : ∃ b ∈ U, b ≠ 1 ∧ e * b = b * e := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype ↥U := Fintype.ofFinite _
  let σ : Equiv.Perm ↥U := MulAut.toPerm ↥U (U.normalizerMonoidHom ⟨e, he⟩)
  have hσ : σ ^ p ^ 1 = 1 := by
    have h1 : (⟨e, he⟩ : normalizer (U : Set G)) ^ p = 1 := Subtype.ext (by simpa using hep)
    rw [pow_one, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hdvd : p ∣ Fintype.card ↥U := by
    rcases hU.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq U h) hU1
    · rwa [Nat.card_eq_fintype_card] at h
  have hfix : σ 1 = 1 := map_one (U.normalizerMonoidHom ⟨e, he⟩)
  obtain ⟨b, hb, hb1⟩ := Equiv.Perm.exists_fixed_point_of_prime' hdvd hσ hfix
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h), ?_⟩
  have h : e * (b : G) * e⁻¹ = b := congrArg Subtype.val hb
  exact mul_inv_eq_iff_eq_mul.1 h

theorem exists_fixed_eigen {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {U : Subgroup G}
    (hU : IsPGroup p ↥U) (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hU1 : U ≠ ⊥) {e z : G}
    (he : e ∈ normalizer (U : Set G)) (hz : z ∈ normalizer (U : Set G)) (hez : e * z = z * e)
    (hz2 : z * z = 1) (hep : e ^ p = 1) (_hp2 : p ≠ 2) :
    ∃ u ∈ U, u ≠ 1 ∧ e * u = u * e ∧ (z * u * z⁻¹ = u ∨ z * u * z⁻¹ = u⁻¹) := by
  obtain ⟨a, haU, ha1, hea⟩ := ka6eig_exists_fixed hp hU hU1 he hep
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have ha'U : z * a * z⁻¹ ∈ U := (hz a).1 haU
  have hez' : Commute e z := hez
  have hea' : Commute e a := hea
  have hc : Commute e (z * a * z⁻¹) := (hez'.mul_right hea').mul_right hez'.inv_right
  by_cases hcase : a * (z * a * z⁻¹) = 1
  · exact ⟨a, haU, ha1, hea, Or.inr (eq_inv_of_mul_eq_one_right hcase)⟩
  · refine ⟨a * (z * a * z⁻¹), U.mul_mem haU ha'U, hcase, hea'.mul_right hc, Or.inl ?_⟩
    calc z * (a * (z * a * z⁻¹)) * z⁻¹ = (z * a * z⁻¹) * a := by
          rw [hzinv]; simp only [mul_assoc, hz2, mul_one]
      _ = a * (z * a * z⁻¹) := hUab _ ha'U a haU

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
