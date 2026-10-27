module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCensus

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.HN

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open scoped commutatorElement

variable {G : Type*} [Group G] {H : Subgroup G}

theorem yWitness_of_root {X E : Subgroup ↥H} {r b w : ↥H} (hr : r ∈ E) (hr1 : r ≠ 1)
    (hb : b ∈ E) (hw : w ∈ closure {y | ∃ c ∈ centDer X r, y = ⁅b, c⁆})
    (h4 : 4 ∣ orderOf w) : YWitness X E := by
  refine Or.inl ⟨w, ?_, h4⟩
  have hle : centDer X r ≤ gammaE X E := le_iSup₂_of_le r hr (le_iSup_of_le hr1 le_rfl)
  refine (closure_le _).mpr ?_ hw
  rintro _ ⟨c, hc, rfl⟩
  exact commutator_mem_commutator hb (hle hc)

theorem yWitness_of_map_conj {X E : Subgroup ↥H} (hX : X.Normal) (g : ↥H)
    (h : YWitness X (E.map (MulAut.conj g).toMonoidHom)) : YWitness X E := by
  rwa [← map_conj_eq_of_normal hX g,
    yWitness_map_iff (MulAut.conj g).toMonoidHom (MulAut.conj g).injective] at h

theorem yWitness_of_root_conj {X E : Subgroup ↥H} (hX : X.Normal) {r b g w : ↥H} (hr : r ∈ E)
    (hr1 : r ≠ 1) (hb : b ∈ E) (hg : g * r = r * g)
    (hw : w ∈ closure {y | ∃ c ∈ centDer X r, y = ⁅g * b * g⁻¹, c⁆}) (h4 : 4 ∣ orderOf w) :
    YWitness X E := by
  refine yWitness_of_map_conj hX g ?_
  refine yWitness_of_root (r := r) (b := g * b * g⁻¹) ?_ hr1 ?_ hw h4
  · refine ⟨r, hr, ?_⟩
    show g * r * g⁻¹ = r
    rw [hg, mul_inv_cancel_right]
  · exact ⟨b, hb, rfl⟩

theorem exists_mem_not_mem_zpowers [Finite G] {E : Subgroup ↥H} {r : ↥H} (hr : orderOf r = 2)
    (hE4 : 4 ≤ Nat.card E) : ∃ b ∈ E, b ∉ zpowers r := by
  by_contra hcon
  push Not at hcon
  have hcard := card_le_of_le (show E ≤ zpowers r from hcon)
  rw [Nat.card_zpowers, hr] at hcard
  omega

theorem eq_one_or_eq_of_mem_zpowers {r x : ↥H} (hr : orderOf r = 2) (hx : x ∈ zpowers r) :
    x = 1 ∨ x = r := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hr]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
  · right
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]

theorem orderOf_eq_four {M : Type*} [Monoid M] {x : M} (h2 : x ^ 2 ≠ 1) (h4 : x ^ 4 = 1) :
    orderOf x = 4 :=
  orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using h2) (by simpa using h4)

theorem coe_commutatorElement {K : Subgroup ↥H} (g h : ↥K) :
    ((⁅g, h⁆ : ↥K) : ↥H) = ⁅(g : ↥H), (h : ↥H)⁆ := by
  simp [commutatorElement_def]

end CFSG.ComponentClassification.RankTwoSporadic.HN
