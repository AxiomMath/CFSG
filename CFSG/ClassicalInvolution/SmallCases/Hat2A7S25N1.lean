module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7M3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S.N

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Hat2A7M.Asc77.T7F2 (Hyp25T)
open scoped commutatorElement

section Setup

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem t'_comm_z (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') : t' * z = z * t' :=
  h.hyp.hzS t' h.ht'S

theorem cz_conj_K (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') {g : G}
    (hg : g * z = z * g) : conjSub g K = K ∨ conjSub g K = K' := by
  have hx : g⁻¹⁻¹ * z * g⁻¹ = z := by
    rw [inv_inv]
    calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [hg]
      _ = z := by group
  simpa only [inv_inv] using h.conj_twin hx (J := K) (Or.inl rfl)

theorem cz_conj_K' (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') {g : G}
    (hg : g * z = z * g) : conjSub g K' = K ∨ conjSub g K' = K' := by
  have hx : g⁻¹⁻¹ * z * g⁻¹ = z := by
    rw [inv_inv]
    calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [hg]
      _ = z := by group
  simpa only [inv_inv] using h.conj_twin hx (J := K') (Or.inr rfl)

theorem cz_fix_iff (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') {g : G}
    (hg : g * z = z * g) : conjSub g K = K ↔ conjSub g K' = K' := by
  constructor
  · intro h1
    rcases cz_conj_K' h hg with h2 | h2
    · exact absurd (conjSub_injective g (h2.trans h1.symm)) h.hs.hne
    · exact h2
  · intro h1
    rcases cz_conj_K h hg with h2 | h2
    · exact h2
    · exact absurd (conjSub_injective g (h2.trans h1.symm)) h.hs.hne.symm

theorem conjSub_t'_K (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') :
    conjSub t' K = K' := by
  rcases cz_conj_K h (t'_comm_z h) with h1 | h1
  · exfalso
    have hR'K : R' ≤ K := by
      rw [← h.ht'R, ← h1]
      exact conjSub_mono h.hRsyl.1
    have := h.hΩ.eq_of_le_of_le h.hK' h.hK h.hR'syl.2.1
      (by have := h.hqR'.eight_le; omega) h.hR'syl.1 hR'K
    exact h.hs.hne this
  · exact h1

theorem conjSub_t'_K' (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') :
    conjSub t' K' = K := by
  have h1 : conjSub (t' * t') K = K := by rw [h.ht'2, conjSub_one]
  rwa [conjSub_mul, conjSub_t'_K h] at h1

theorem cz_cover (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') {g : G}
    (hg : g * z = z * g) : conjSub g K = K ∨ conjSub (g * t') K = K := by
  rcases cz_conj_K h hg with h1 | h1
  · exact Or.inl h1
  · right
    rw [conjSub_mul, conjSub_t'_K h]
    rcases cz_conj_K' h hg with h2 | h2
    · exact h2
    · exact absurd (h1.symm.trans ((cz_fix_iff h hg).mpr h2)) h.hs.hne

theorem fix_of_isFAut (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') {a : G}
    (haS : a ∈ (S : Subgroup G)) (hF : IsFAut R' a) :
    conjSub a R = R ∧ conjSub a R' = R' ∧ conjSub a K = K ∧ conjSub a K' = K' := by
  have hR' : conjSub a R' = R' := mem_normalizer_iff_conjSub_eq.mp hF.1
  have hNa : a ∈ T7F2.Nsub S R := h.mem_N_of_conj_R' haS hR'
  have hR : conjSub a R = R := (T7F2.mem_Nsub.mp hNa).2
  have h4R : 4 ≤ Nat.card R := by have := h.hqR.eight_le; omega
  have h4R' : 4 ≤ Nat.card R' := by have := h.hqR'.eight_le; omega
  refine ⟨hR, hR', ?_, ?_⟩
  · exact h.hΩ.eq_of_le_of_le (h.hΩ.conjInvariant a K h.hK) h.hK h.hRsyl.2.1 h4R
      (by rw [← hR]; exact conjSub_mono h.hRsyl.1) h.hRsyl.1
  · exact h.hΩ.eq_of_le_of_le (h.hΩ.conjInvariant a K' h.hK') h.hK' h.hR'syl.2.1 h4R'
      (by rw [← hR']; exact conjSub_mono h.hR'syl.1) h.hR'syl.1

theorem exists_noncomm_of_swap (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') :
    ∃ x y : G, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  have h3 : conjSub t' K = K := by
    ext x
    rw [mem_conjSub_iff]
    have : t'⁻¹ * x * t' = x := by
      rw [mul_assoc, hcon x t', ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]
  exact h.hs.hne ((conjSub_t'_K h).symm.trans h3)

end Setup

end CFSG.ClassicalInvolution.Hat2A7S.N
