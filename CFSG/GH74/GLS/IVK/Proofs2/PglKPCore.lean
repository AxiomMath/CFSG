module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG in
theorem pCore_eq_of_two_sylow {Γ : Type} [Group Γ] [Finite Γ] (hΓ : Nat.card Γ = 24)
    (V : Subgroup Γ) [V.Normal] (hV : Nat.card ↥V = 4) (P₁ P₂ : Subgroup Γ)
    (h1 : Nat.card ↥P₁ = 8) (h2 : Nat.card ↥P₂ = 8) (hne : P₁ ≠ P₂) (hV1 : V ≤ P₁) (hV2 : V ≤ P₂) :
    pCore 2 Γ = V := by
  have hfac : (Nat.card Γ).factorization 2 = 3 := by
    have h24 : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
    rw [hΓ, h24, Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 3 by norm_num)]
  have key : ∀ P : Subgroup Γ, Nat.card ↥P = 8 → pCore 2 Γ ≤ P := by
    intro P hP
    have hcard : Nat.card ↥P = 2 ^ (Nat.card Γ).factorization 2 := by rw [hP, hfac]; norm_num
    have hle := (pCore_isPGroup (p := 2) (G := Γ)).le_sylow_of_normal (Sylow.ofCard P hcard)
    rwa [Sylow.coe_ofCard] at hle
  have hVI : V = P₁ ⊓ P₂ := by
    have hle : V ≤ P₁ ⊓ P₂ := le_inf hV1 hV2
    have hdvd : Nat.card ↥(P₁ ⊓ P₂) ∣ 8 := h1 ▸ Subgroup.card_dvd_of_le inf_le_left
    have hge : 4 ≤ Nat.card ↥(P₁ ⊓ P₂) := hV ▸ Subgroup.card_le_of_le hle
    have hne8 : Nat.card ↥(P₁ ⊓ P₂) ≠ 8 := by
      intro h8
      apply hne
      have e1 : P₁ ⊓ P₂ = P₁ := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, h8])
      have e2 : P₁ ⊓ P₂ = P₂ := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h2, h8])
      exact e1.symm.trans e2
    have hcard : Nat.card ↥(P₁ ⊓ P₂) = 4 := by
      generalize Nat.card ↥(P₁ ⊓ P₂) = n at hdvd hge hne8
      have hle8 : n ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases n <;> omega
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hV])
  have hVQ : V ≤ pCore 2 Γ :=
    le_sSup ⟨inferInstance, IsPGroup.of_card (n := 2) (by rw [hV]; norm_num)⟩
  exact le_antisymm ((le_inf (key P₁ h1) (key P₂ h2)).trans hVI.ge) hVQ

end CFSG.GH74.GLS.IVK.Proofs2
