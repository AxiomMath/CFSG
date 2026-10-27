module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWSurj
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWAut

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open scoped Pointwise

@[expose] def P32 (π : Equiv.Perm (Fin 128)) : Prop :=
  ((π ⟨32, by norm_num⟩ : Fin 128) : ℕ) = 32 ∨ ((π ⟨32, by norm_num⟩ : Fin 128) : ℕ) = 53

section Facts

theorem inv32 : ∀ x < 128, mulC 32 x = 0 → x = 53 := by decide +kernel

theorem inv53 : ∀ x < 128, mulC 53 x = 0 → x = 32 := by decide +kernel

theorem mulC_32_53 : mulC 32 53 = 0 := by decide +kernel

theorem mulC_32_32 : mulC 32 32 = tC := by decide +kernel

theorem sq_21_D : ∀ x < 128, (x = 0 ∨ x = 21 ∨ x = 32 ∨ x = 53 ∨ x = 64 ∨ x = 85 ∨ x = 96 ∨ x = 117) →
    mulC x x = tC → x = 32 ∨ x = 53 := by decide +kernel

end Facts


theorem P32_of_stab0 {s : ↥Pg} (hs : s ∈ Stab0) : P32 (s : Equiv.Perm (Fin 128)) := by
  have hsA : (s : Equiv.Perm (Fin 128)) ∈ AutC := pg_le_autC s.2
  have hx : (⟨32, by norm_num⟩ : Fin 128) ∈ omegaFin 0 := (mem_omega0 _).2 (by simp)
  have hmem : (s : Equiv.Perm (Fin 128)) ⟨32, by norm_num⟩ ∈ omegaFin 0 := by
    have h1 : s • (⟨32, by norm_num⟩ : Fin 128) ∈ s • omegaFin 0 :=
      Finset.smul_mem_smul_finset hx
    have h2 : s • omegaFin 0 = omegaFin 0 := hs
    rw [h2] at h1
    exact h1
  have hv := (mem_omega0 _).1 hmem
  have hlt : ((s : Equiv.Perm (Fin 128)) ⟨32, by norm_num⟩ : ℕ) < 128 := Fin.is_lt _
  have hsq : mulC ((s : Equiv.Perm (Fin 128)) ⟨32, by norm_num⟩ : ℕ)
      ((s : Equiv.Perm (Fin 128)) ⟨32, by norm_num⟩ : ℕ) = tC := by
    have h1 := permVal_mul hsA (a := 32) (b := 32) (by norm_num) (by norm_num)
    rw [mulC_32_32, permVal_tC hsA, permVal_eq _ (by norm_num : 32 < 128)] at h1
    exact h1.symm
  exact sq_21_D _ hlt (by simpa using hv) hsq

theorem P32_mul {π ρ : Equiv.Perm (Fin 128)} (hπ : π ∈ AutC) (h1 : P32 π) (h2 : P32 ρ) :
    P32 (π * ρ) := by
  have h53 : ((π ⟨53, by norm_num⟩ : Fin 128) : ℕ) = 32 ∨ ((π ⟨53, by norm_num⟩ : Fin 128) : ℕ) = 53 := by
    have h := permVal_mul hπ (a := 32) (b := 53) (by norm_num) (by norm_num)
    rw [mulC_32_53, permVal_zero hπ, permVal_eq _ (by norm_num : 32 < 128),
      permVal_eq _ (by norm_num : 53 < 128)] at h
    have hlt : ((π ⟨53, by norm_num⟩ : Fin 128) : ℕ) < 128 := Fin.is_lt _
    rcases h1 with h1 | h1
    · rw [h1] at h
      exact Or.inr (inv32 _ hlt h.symm)
    · rw [h1] at h
      exact Or.inl (inv53 _ hlt h.symm)
  unfold P32 at h2 ⊢
  rw [Equiv.Perm.mul_apply]
  rcases h2 with h2 | h2
  · have : ρ ⟨32, by norm_num⟩ = ⟨32, by norm_num⟩ := Fin.ext h2
    rw [this]
    exact h1
  · have : ρ ⟨32, by norm_num⟩ = ⟨53, by norm_num⟩ := Fin.ext h2
    rw [this]
    exact h53

theorem surj_of_gen (H : Subgroup ↥Pg) (h0 : Stab0 ≤ H) (γ : ↥Pg) (hγ : γ ∈ H)
    (hmove : ¬ P32 (γ : Equiv.Perm (Fin 128))) : H = ⊤ := by
  obtain ⟨j, hj, hγj⟩ := omega_closed γ
  obtain ⟨r, hr, s, hsG, hsr⟩ := omega_root hj
  have hgam := gamRep_smul hr
  have hsStab : s ∈ Stab0 := G0_le_Stab0 hsG
  have hsg : (s * gamRep r hr) • omegaFin 0 = omegaFin j := by rw [mul_smul, hgam, hsr]
  have ht' : (s * gamRep r hr)⁻¹ * γ ∈ Stab0 := by
    show ((s * gamRep r hr)⁻¹ * γ) • omegaFin 0 = omegaFin 0
    rw [mul_smul, hγj]
    exact inv_smul_eq_iff.2 hsg.symm
  have hdec : γ = s * gamRep r hr * ((s * gamRep r hr)⁻¹ * γ) := by group
  have hsH : s ∈ H := h0 hsStab
  have htH : (s * gamRep r hr)⁻¹ * γ ∈ H := h0 ht'
  have hgamH : gamRep r hr ∈ H := by
    have e : gamRep r hr = s⁻¹ * γ * ((s * gamRep r hr)⁻¹ * γ)⁻¹ := by group
    rw [e]
    exact H.mul_mem (H.mul_mem (H.inv_mem hsH) hγ) (H.inv_mem htH)
  have hmov : ¬ (gamReps[r]!)[32]! = 32 ∧ ¬ (gamReps[r]!)[32]! = 53 := by
    constructor <;> intro hc <;> apply hmove
    all_goals
      have hP : P32 ((gamRep r hr : ↥Pg) : Equiv.Perm (Fin 128)) := by
        unfold P32
        rw [gamRep_apply hr]
        simp [hc]
      have hP1 := P32_mul (pg_le_autC s.2) (P32_of_stab0 hsStab) hP
      have hP2 := P32_mul (pg_le_autC (Pg.mul_mem s.2 (gamRep r hr).2))
        (P32_mul (pg_le_autC s.2) (P32_of_stab0 hsStab) hP) (P32_of_stab0 ht')
      rw [hdec]
      exact hP2
  have hS0 : G0 ≤ H := G0_le_Stab0.trans h0
  have htrans := gamRep_trans hr (fun h => by tauto) H hS0 hgamH
  rw [eq_top_iff]
  intro δ _
  obtain ⟨j', hj', hδj⟩ := omega_closed δ
  obtain ⟨s', hs'H, hs'⟩ := htrans j' hj'
  have hst : s'⁻¹ * δ ∈ Stab0 := by
    show (s'⁻¹ * δ) • omegaFin 0 = omegaFin 0
    rw [mul_smul, hδj]
    exact inv_smul_eq_iff.2 hs'.symm
  have hδ : δ = s' * (s'⁻¹ * δ) := by group
  rw [hδ]
  exact H.mul_mem hs'H (h0 hst)

end CFSG.EvenSporadicStandard.Fin76b.W16
