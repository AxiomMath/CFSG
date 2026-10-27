module

public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.ComponentClassification.CatFC.OmegaSmall

open Module

@[expose] def omegaLb : ℕ → ℕ
  | 1 => 2
  | 2 => 4
  | 3 => 48
  | 4 => 1152
  | 5 => 103680
  | 6 => 24261120
  | 7 => 18341406720
  | _ => 1

theorem ringChar_ne_two_of_card_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) :
    ringChar K ≠ 2 := by
  have h := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq Nat.prime_three le_rfl
    (by simpa using hK : Nat.card K = 3 ^ 1)
  rw [h]
  norm_num

theorem omega_card_orthogonalGroup_ge {K W : Type} [Field K] [Finite K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (hK : Nat.card K = 3) {Q : QuadraticForm K W}
    (hQ : Q.polarBilin.Nondegenerate) {r : ℕ} (hr1 : 1 ≤ r) (hr7 : r ≤ 7)
    (hdim : finrank K W = r) :
    omegaLb r ≤ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
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
    simp only [omegaLb]
    omega
  · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hQ (m := 0)
      (by simpa using hdim) hε
    rw [hKz] at h
    simp only [omegaLb]
    generalize Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = c at h ⊢
    rcases hε' with rfl | rfl <;> (norm_num at h; omega)
  · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd h2 hQ (n := 1) hdim
    rw [hKz] at h
    have : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) = 48 := by
      rw [h]; decide
    simp only [omegaLb]
    omega
  · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hQ (m := 1)
      (by simpa using hdim) hε
    rw [hKz] at h
    simp only [omegaLb]
    generalize Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = c at h ⊢
    rcases hε' with rfl | rfl <;> (norm_num at h; omega)
  · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd h2 hQ (n := 2) hdim
    rw [hKz] at h
    have : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) = 103680 := by
      rw [h]; decide
    simp only [omegaLb]
    omega
  · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hQ (m := 2)
      (by simpa using hdim) hε
    rw [hKz] at h
    simp only [omegaLb]
    generalize Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = c at h ⊢
    rcases hε' with rfl | rfl <;> (norm_num [Finset.prod_Icc_succ_top] at h; omega)
  · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd h2 hQ (n := 3) hdim
    rw [hKz] at h
    have : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) = 18341406720 := by
      rw [h]; decide
    simp only [omegaLb]
    omega

end CFSG.ComponentClassification.CatFC.OmegaSmall
