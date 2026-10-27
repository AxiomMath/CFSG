module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.A8CentPerm2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.A8CentPerm4
public import CFSG.Holt.PermFactsInvolutions

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Equiv

private lemma reduce {s t : Perm (Fin 8)} (ht2 : t ^ 2 = 1) (g : Perm (Fin 8))
    (hg : g ∈ alternatingGroup (Fin 8)) (hconj : g * s * g⁻¹ = t)
    (P : ∀ σ' : Perm (Fin 8),
      (∀ h ∈ alternatingGroup (Fin 8), h * t = t * h → σ' * h = h * σ') →
      σ' = 1 ∨ σ' = t)
    (σ : Perm (Fin 8))
    (hσ : ∀ h ∈ alternatingGroup (Fin 8), h * s = s * h → σ * h = h * σ) :
    σ = 1 ∨ σ = s := by
  have hs_eq : s = g⁻¹ * t * g := by rw [← hconj]; group
  have hσ' : ∀ h ∈ alternatingGroup (Fin 8), h * t = t * h →
      (g * σ * g⁻¹) * h = h * (g * σ * g⁻¹) := by
    intro h hh hcomm
    have hh' : g⁻¹ * h * g ∈ alternatingGroup (Fin 8) :=
      mul_mem (mul_mem (inv_mem hg) hh) hg
    have h'comm : (g⁻¹ * h * g) * s = s * (g⁻¹ * h * g) := by
      calc (g⁻¹ * h * g) * s
          = g⁻¹ * h * (g * s * g⁻¹) * g := by group
        _ = g⁻¹ * h * t * g := by rw [hconj]
        _ = g⁻¹ * (h * t) * g := by group
        _ = g⁻¹ * (t * h) * g := by rw [hcomm]
        _ = g⁻¹ * t * h * g := by group
        _ = s * (g⁻¹ * h * g) := by rw [hs_eq]; group
    have hconjσ := hσ _ hh' h'comm
    calc (g * σ * g⁻¹) * h
        = g * (σ * (g⁻¹ * h * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * h * g) * σ) * g⁻¹ := by rw [hconjσ]
      _ = h * (g * σ * g⁻¹) := by group
  rcases P _ hσ' with h | h
  · left
    calc σ = g⁻¹ * (g * σ * g⁻¹) * g := by group
      _ = g⁻¹ * 1 * g := by rw [h]
      _ = 1 := by simp
  · right
    calc σ = g⁻¹ * (g * σ * g⁻¹) * g := by group
      _ = g⁻¹ * t * g := by rw [h]
      _ = s := hs_eq.symm

private lemma two_two_sq : (swap 0 1 * swap 2 3 : Perm (Fin 8)) ^ 2 = 1 := by decide

private lemma two_two_card : (swap 0 1 * swap 2 3 : Perm (Fin 8)).support.card = 4 := by decide

private lemma four_sq :
    (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 : Perm (Fin 8)) ^ 2 = 1 := by decide

private lemma four_card :
    (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 : Perm (Fin 8)).support.card = 8 := by decide

theorem perm_cent_alt_eight {s σ : Perm (Fin 8)} (hs : s ∈ alternatingGroup (Fin 8))
    (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1)
    (hσ : ∀ g ∈ alternatingGroup (Fin 8), g * s = s * g → σ * g = g * σ) :
    σ = 1 ∨ σ = s := by
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
    exact reduce two_two_sq g hg hconj (fun σ' h => cent_perm_two_two h) σ hσ
  · obtain ⟨g, hg, hconj⟩ :=
      CFSG.Holt.exists_mem_alternatingGroup_conj_eq_of_card_support_eq (Ψ := Fin 8)
        hs2 four_sq (by rw [hc, four_card])
    exact reduce four_sq g hg hconj (fun σ' h => cent_perm_four h) σ hσ

end CFSG.EvenSporadicStandard.HNRecog.Section4
