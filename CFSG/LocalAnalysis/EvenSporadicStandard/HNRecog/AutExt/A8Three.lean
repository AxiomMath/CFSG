module

public import CFSG.Holt.PermFactsInvolutions

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Equiv

private lemma three_of_conj {s t : Perm (Fin 8)} (g : Perm (Fin 8))
    (hg : g ∈ alternatingGroup (Fin 8)) (hconj : g * s * g⁻¹ = t) {ε₀ : Perm (Fin 8)}
    (h₀ : ε₀ ∈ alternatingGroup (Fin 8)) (h3 : ε₀ ^ 3 = 1) (h1 : ε₀ ≠ 1)
    (hc : ε₀ * t = t * ε₀) :
    ∃ ε ∈ alternatingGroup (Fin 8), ε ^ 3 = 1 ∧ ε ≠ 1 ∧ ε * s = s * ε := by
  have hs : s = g⁻¹ * t * g := by rw [← hconj]; group
  refine ⟨g⁻¹ * ε₀ * g, ?_, ?_, ?_, ?_⟩
  · exact mul_mem (mul_mem (inv_mem hg) h₀) hg
  · have h := conj_pow (a := g⁻¹) (b := ε₀) (i := 3)
    rw [inv_inv] at h
    rw [h, h3]
    group
  · intro h
    apply h1
    have h' : ε₀ = g * (g⁻¹ * ε₀ * g) * g⁻¹ := by group
    rw [h', h]
    group
  · calc (g⁻¹ * ε₀ * g) * s = g⁻¹ * (ε₀ * t) * g := by rw [hs]; group
      _ = g⁻¹ * (t * ε₀) * g := by rw [hc]
      _ = s * (g⁻¹ * ε₀ * g) := by rw [hs]; group

private lemma two_two_sq : (swap 0 1 * swap 2 3 : Perm (Fin 8)) ^ 2 = 1 := by decide

private lemma two_two_card : (swap 0 1 * swap 2 3 : Perm (Fin 8)).support.card = 4 := by decide

private lemma four_sq :
    (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 : Perm (Fin 8)) ^ 2 = 1 := by decide

private lemma four_card :
    (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 : Perm (Fin 8)).support.card = 8 := by decide

private lemma three_cycle_even :
    (swap 4 5 * swap 5 6 : Perm (Fin 8)) ∈ alternatingGroup (Fin 8) := by
  rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
    Perm.sign_swap (by decide)]
  decide

private lemma two_three_cycles_even :
    (swap 0 2 * swap 2 4 * (swap 1 3 * swap 3 5) : Perm (Fin 8)) ∈ alternatingGroup (Fin 8) := by
  rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_mul, Perm.sign_mul,
    Perm.sign_swap (by decide), Perm.sign_swap (by decide), Perm.sign_swap (by decide),
    Perm.sign_swap (by decide)]
  decide

theorem exists_three_cent_alt_eight {s : Perm (Fin 8)} (hs : s ∈ alternatingGroup (Fin 8))
    (hs2 : s ^ 2 = 1) :
    ∃ ε ∈ alternatingGroup (Fin 8), ε ^ 3 = 1 ∧ ε ≠ 1 ∧ ε * s = s * ε := by
  by_cases hs1 : s = 1
  · refine ⟨swap 4 5 * swap 5 6, three_cycle_even, by decide, by decide, ?_⟩
    rw [hs1, mul_one, one_mul]
  have hsign : s.sign = 1 := Perm.mem_alternatingGroup.mp hs
  have h4 : 4 ∣ s.support.card :=
    (CFSG.Holt.sign_eq_one_iff_four_dvd_card_support (Ψ := Fin 8) hs2).mp hsign
  have hpos : 0 < s.support.card := by
    rw [Finset.card_pos]
    exact Finset.nonempty_iff_ne_empty.mpr fun h =>
      hs1 (Equiv.Perm.support_eq_empty_iff.mp h)
  have hle : s.support.card ≤ 8 := by
    simpa using Finset.card_le_univ s.support
  obtain ⟨k, hk⟩ := h4
  have hcard : s.support.card = 4 ∨ s.support.card = 8 := by omega
  rcases hcard with hc | hc
  · obtain ⟨g, hg, hconj⟩ :=
      CFSG.Holt.exists_mem_alternatingGroup_conj_eq_of_card_support_eq (Ψ := Fin 8)
        hs2 two_two_sq (by rw [hc, two_two_card])
    exact three_of_conj g hg hconj three_cycle_even (by decide) (by decide) (by decide)
  · obtain ⟨g, hg, hconj⟩ :=
      CFSG.Holt.exists_mem_alternatingGroup_conj_eq_of_card_support_eq (Ψ := Fin 8)
        hs2 four_sq (by rw [hc, four_card])
    exact three_of_conj g hg hconj two_three_cycles_even (by decide) (by decide) (by decide)

end CFSG.EvenSporadicStandard.HNRecog.Section4
