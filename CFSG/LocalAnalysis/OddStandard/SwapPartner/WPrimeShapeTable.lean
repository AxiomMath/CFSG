module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLPerm

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm

@[expose] noncomputable def altCentCard8 (σ : Perm (Fin 8)) : ℕ :=
  Nat.card (alternatingGroup (Fin 8) ⊓ centralizer ({σ} : Set (Perm (Fin 8))) :
    Subgroup (Perm (Fin 8)))

theorem card_cycleType_le_four {σ : Perm (Fin 8)} (hσ : σ * σ = 1) :
    Multiset.card σ.cycleType ≤ 4 := by
  have hcard := card_fixed_add_two_mul_card_cycleType (m := 8) hσ
  omega

private theorem wt_two_mul_altCentCard8 {σ : Perm (Fin 8)} (hσ : σ * σ = 1) (h1 : σ ≠ 1) :
    2 * altCentCard8 σ = (8 - 2 * Multiset.card σ.cycleType).factorial *
      2 ^ Multiset.card σ.cycleType * (Multiset.card σ.cycleType).factorial := by
  have h := two_mul_card_alt_inf_centralizer (m := 8) hσ h1
  have hf : Fintype.card {x : Fin 8 // σ x = x} = 8 - 2 * Multiset.card σ.cycleType := by
    have hcard := card_fixed_add_two_mul_card_cycleType (m := 8) hσ
    omega
  rw [hf] at h
  exact h

theorem altCentCard8_one : altCentCard8 1 = 20160 := by
  have hc : centralizer ({1} : Set (Perm (Fin 8))) = ⊤ := by
    ext g
    simp [Subgroup.mem_centralizer_singleton_iff]
  rw [altCentCard8, hc, inf_top_eq, nat_card_alternatingGroup, Nat.card_fin]
  norm_num [Nat.factorial]

theorem altCentCard8_eq_of_card_cycleType_eq_one {σ : Perm (Fin 8)} (hσ : σ * σ = 1)
    (hk : Multiset.card σ.cycleType = 1) : altCentCard8 σ = 720 := by
  have h1 : σ ≠ 1 := by
    intro h
    rw [h] at hk
    simp at hk
  have h := wt_two_mul_altCentCard8 hσ h1
  rw [hk] at h
  norm_num [Nat.factorial] at h
  omega

theorem altCentCard8_eq_of_card_cycleType_eq_two {σ : Perm (Fin 8)} (hσ : σ * σ = 1)
    (hk : Multiset.card σ.cycleType = 2) : altCentCard8 σ = 96 := by
  have h1 : σ ≠ 1 := by
    intro h
    rw [h] at hk
    simp at hk
  have h := wt_two_mul_altCentCard8 hσ h1
  rw [hk] at h
  norm_num [Nat.factorial] at h
  omega

theorem altCentCard8_eq_of_card_cycleType_eq_three {σ : Perm (Fin 8)} (hσ : σ * σ = 1)
    (hk : Multiset.card σ.cycleType = 3) : altCentCard8 σ = 48 := by
  have h1 : σ ≠ 1 := by
    intro h
    rw [h] at hk
    simp at hk
  have h := wt_two_mul_altCentCard8 hσ h1
  rw [hk] at h
  norm_num [Nat.factorial] at h
  omega

theorem altCentCard8_eq_of_card_cycleType_eq_four {σ : Perm (Fin 8)} (hσ : σ * σ = 1)
    (hk : Multiset.card σ.cycleType = 4) : altCentCard8 σ = 192 := by
  have h1 : σ ≠ 1 := by
    intro h
    rw [h] at hk
    simp at hk
  have h := wt_two_mul_altCentCard8 hσ h1
  rw [hk] at h
  norm_num [Nat.factorial] at h
  omega

theorem altCentCard8_mem {σ : Perm (Fin 8)} (hσ : σ * σ = 1) :
    altCentCard8 σ = 20160 ∨ altCentCard8 σ = 720 ∨ altCentCard8 σ = 96 ∨ altCentCard8 σ = 48 ∨
      altCentCard8 σ = 192 := by
  by_cases h1 : σ = 1
  · exact Or.inl (by rw [h1]; exact altCentCard8_one)
  · right
    set k := Multiset.card σ.cycleType with hk
    have hkpos : 0 < k := by
      rw [hk, Equiv.Perm.card_cycleType_pos]
      exact h1
    have hkle : k ≤ 4 := by
      rw [hk]
      exact card_cycleType_le_four hσ
    interval_cases k
    · exact Or.inl (altCentCard8_eq_of_card_cycleType_eq_one hσ hk.symm)
    · exact Or.inr (Or.inl (altCentCard8_eq_of_card_cycleType_eq_two hσ hk.symm))
    · exact Or.inr (Or.inr (Or.inl (altCentCard8_eq_of_card_cycleType_eq_three hσ hk.symm)))
    · exact Or.inr (Or.inr (Or.inr (altCentCard8_eq_of_card_cycleType_eq_four hσ hk.symm)))

theorem forty_eight_le_altCentCard8 {σ : Perm (Fin 8)} (hσ : σ * σ = 1) : 48 ≤ altCentCard8 σ := by
  rcases altCentCard8_mem hσ with h | h | h | h | h <;> omega

end CFSG.OddStandard.AltStdSec.SwapPartner
