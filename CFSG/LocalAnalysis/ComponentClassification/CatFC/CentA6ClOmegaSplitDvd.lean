module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaSmallOrder

public section

namespace CFSG.ComponentClassification.CatFC.OmegaSmall

open Module

@[expose] def omegaTwoLb : ℕ → ℕ
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 5
  | 5 => 8
  | 6 => 9
  | 7 => 11
  | _ => 0

theorem two_pow_dvd_card_orthogonalGroup {K W : Type} [Field K] [Finite K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (hK : Nat.card K = 3) {Q : QuadraticForm K W}
    (hQ : Q.polarBilin.Nondegenerate) {r : ℕ} (hr1 : 1 ≤ r) (hr7 : r ≤ 7)
    (hdim : finrank K W = r) :
    2 ^ omegaTwoLb r ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have h2 := ringChar_ne_two_of_card_three hK
  have hKz : (Nat.card K : ℤ) = 3 := by rw [hK]; rfl
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, (ε = 1 ∧ CFSG.GroupTheory.WeirSylow.IsPlusType Q) ∨
      (ε = -1 ∧ ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) := by
    by_cases hP : CFSG.GroupTheory.WeirSylow.IsPlusType Q
    · exact ⟨1, Or.inl ⟨rfl, hP⟩⟩
    · exact ⟨-1, Or.inr ⟨rfl, hP⟩⟩
  have hε' : ε = 1 ∨ ε = -1 := by rcases hε with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  interval_cases r
  · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd h2 hQ (n := 0) hdim
    rw [hKz] at h
    have : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) = 2 := by
      rw [h]; decide
    have h' : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 := by exact_mod_cast this
    rw [h']
    decide
  · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hQ (m := 0)
      (by simpa using hdim) hε
    rw [hKz] at h
    simp only [omegaTwoLb]
    generalize Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = c at h ⊢
    rcases hε' with rfl | rfl <;> (norm_num at h; omega)
  · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd h2 hQ (n := 1) hdim
    rw [hKz] at h
    have : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) = 48 := by
      rw [h]; decide
    have h' : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 48 := by exact_mod_cast this
    rw [h']
    decide
  · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hQ (m := 1)
      (by simpa using hdim) hε
    rw [hKz] at h
    simp only [omegaTwoLb]
    generalize Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = c at h ⊢
    rcases hε' with rfl | rfl <;> (norm_num at h; omega)
  · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd h2 hQ (n := 2) hdim
    rw [hKz] at h
    have : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) = 103680 := by
      rw [h]; decide
    have h' : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 103680 := by exact_mod_cast this
    rw [h']
    decide
  · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hQ (m := 2)
      (by simpa using hdim) hε
    rw [hKz] at h
    simp only [omegaTwoLb]
    generalize Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = c at h ⊢
    rcases hε' with rfl | rfl <;> (norm_num [Finset.prod_Icc_succ_top] at h; omega)
  · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd h2 hQ (n := 3) hdim
    rw [hKz] at h
    have : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) = 18341406720 := by
      rw [h]; decide
    have h' : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 18341406720 := by
      exact_mod_cast this
    rw [h']
    decide

theorem nine_le_omegaTwoLb_add {d₁ d₂ : ℕ} (h₁ : 1 ≤ d₁) (h₂ : 1 ≤ d₂)
    (hd : d₁ + d₂ = 7 ∨ d₁ + d₂ = 8) : 9 ≤ omegaTwoLb d₁ + omegaTwoLb d₂ := by
  have h₁' : d₁ ≤ 7 := by omega
  have h₂' : d₂ ≤ 7 := by omega
  interval_cases d₁ <;> interval_cases d₂ <;> first | omega | decide

theorem omega_split_two_pow_nine_dvd {K W₁ W₂ : Type} [Field K] [Finite K] [AddCommGroup W₁]
    [Module K W₁] [FiniteDimensional K W₁] [AddCommGroup W₂] [Module K W₂]
    [FiniteDimensional K W₂] (hK : Nat.card K = 3) {Q₁ : QuadraticForm K W₁}
    {Q₂ : QuadraticForm K W₂} (hQ₁ : Q₁.polarBilin.Nondegenerate)
    (hQ₂ : Q₂.polarBilin.Nondegenerate) (h₁ : 1 ≤ finrank K W₁) (h₂ : 1 ≤ finrank K W₂)
    (hd : finrank K W₁ + finrank K W₂ = 7 ∨ finrank K W₁ + finrank K W₂ = 8) :
    2 ^ 9 ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q₁) *
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q₂) := by
  have h₁7 : finrank K W₁ ≤ 7 := by omega
  have h₂7 : finrank K W₂ ≤ 7 := by omega
  have e₁ := two_pow_dvd_card_orthogonalGroup hK hQ₁ h₁ h₁7 rfl
  have e₂ := two_pow_dvd_card_orthogonalGroup hK hQ₂ h₂ h₂7 rfl
  have hle := nine_le_omegaTwoLb_add h₁ h₂ hd
  calc 2 ^ 9 ∣ 2 ^ (omegaTwoLb (finrank K W₁) + omegaTwoLb (finrank K W₂)) :=
        pow_dvd_pow 2 hle
    _ = 2 ^ omegaTwoLb (finrank K W₁) * 2 ^ omegaTwoLb (finrank K W₂) := pow_add _ _ _
    _ ∣ _ := Nat.mul_dvd_mul e₁ e₂

theorem two_pow_nine_dvd_card_of_mulEquiv_orthogonalGroup_prod {K W₁ W₂ : Type} [Field K]
    [Finite K] [AddCommGroup W₁] [Module K W₁] [FiniteDimensional K W₁] [AddCommGroup W₂]
    [Module K W₂] [FiniteDimensional K W₂] (hK : Nat.card K = 3) {Q₁ : QuadraticForm K W₁}
    {Q₂ : QuadraticForm K W₂} (hQ₁ : Q₁.polarBilin.Nondegenerate)
    (hQ₂ : Q₂.polarBilin.Nondegenerate) (h₁ : 1 ≤ finrank K W₁) (h₂ : 1 ≤ finrank K W₂)
    (hd : finrank K W₁ + finrank K W₂ = 7 ∨ finrank K W₁ + finrank K W₂ = 8) {C : Type*}
    [Group C]
    (e : C ≃* TauCeti.QuadraticMap.orthogonalGroup Q₁ × TauCeti.QuadraticMap.orthogonalGroup Q₂) :
    2 ^ 9 ∣ Nat.card C := by
  rw [Nat.card_congr e.toEquiv, Nat.card_prod]
  exact omega_split_two_pow_nine_dvd hK hQ₁ hQ₂ h₁ h₂ hd

end CFSG.ComponentClassification.CatFC.OmegaSmall
