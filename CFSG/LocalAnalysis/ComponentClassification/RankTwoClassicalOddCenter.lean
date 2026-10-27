module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalEvenMultiplier
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticOrthogonalCoverOddKernel

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

section Kernel

variable {A : Type} [Group A] [Finite A]

theorem odd_card_center_of_psu (hA : commutator A = ⊤) {n m : ℕ} (hn : 4 ≤ n)
    (hS : StatedClassicalModel (A ⧸ center A) .PSU n 2 m) (h41 : ¬(n = 4 ∧ m = 1))
    (h61 : ¬(n = 6 ∧ m = 1)) : Odd (Nat.card (center A)) := by
  have : Group.IsPerfect A := Group.isPerfect_def.2 hA
  have hm : 1 ≤ m := hS.1.2.1
  have h := even_higher_linear_unitary_perfect_central_kernel_odd_off_five_boundaries
    (QuotientGroup.mk' (center A)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) (Or.inr rfl) (by omega) hm hS
    (by intro h; simp at h; omega)
  rwa [QuotientGroup.ker_mk'] at h

theorem odd_card_center_of_psp_pomega (hA : commutator A = ⊤) {τ : StatedLieTag}
    (hτ : τ = .PSp ∨ τ = .POmegaPlus ∨ τ = .POmegaMinus) {n m : ℕ}
    (hS : StatedClassicalModel (A ⧸ center A) τ n 2 m)
    (hoff : (τ, n, m) ∉ [(.PSp, 3, 1), (.POmegaPlus, 4, 1)]) : Odd (Nat.card (center A)) := by
  have : Group.IsPerfect A := Group.isPerfect_def.2 hA
  have h := even_symplectic_orthogonal_perfect_central_kernel_odd_off_two_boundaries
    (QuotientGroup.mk' (center A)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) hτ hS hoff
  rwa [QuotientGroup.ker_mk'] at h

end Kernel

theorem classicalEvenMultiplierRest : ClassicalEvenMultiplierRest := by
  intro A _ _ hA heven hfam _ _
  have hodd : ¬ Odd (Nat.card (center A)) := Nat.not_odd_iff_even.mpr heven
  rcases hfam with ⟨n, m, hn, hU⟩ | ⟨n, m, -, hS⟩ | ⟨n, m, -, hP | hM⟩
  · by_cases h41 : n = 4 ∧ m = 1
    · obtain ⟨rfl, rfl⟩ := h41
      exact Or.inl hU
    by_cases h61 : n = 6 ∧ m = 1
    · obtain ⟨rfl, rfl⟩ := h61
      exact Or.inr (Or.inl hU)
    exact (hodd (odd_card_center_of_psu hA hn hU h41 h61)).elim
  · by_cases h31 : n = 3 ∧ m = 1
    · obtain ⟨rfl, rfl⟩ := h31
      exact Or.inr (Or.inr (Or.inl hS))
    exact (hodd (odd_card_center_of_psp_pomega hA (Or.inl rfl) hS
      (by intro h; simp at h; omega))).elim
  · by_cases h41 : n = 4 ∧ m = 1
    · obtain ⟨rfl, rfl⟩ := h41
      exact Or.inr (Or.inr (Or.inr hP))
    exact (hodd (odd_card_center_of_psp_pomega hA (Or.inr (Or.inl rfl)) hP
      (by intro h; simp at h; omega))).elim
  · exact (hodd (odd_card_center_of_psp_pomega hA (Or.inr (Or.inr rfl)) hM
      (by simp))).elim

theorem classicalEvenMultiplier : ClassicalEvenMultiplier :=
  classicalEvenMultiplier_of_rest classicalEvenMultiplierRest

theorem ClassicalModel.odd_card_center_of_linear {G : Type} [Group G] [Finite G]
    {A : Subgroup G} (D : ClassicalModel A) (hfam : D.family = .linear)
    (hA : CFSG.Open.IsQuasisimple ↥A) : Odd (Nat.card (center ↥A)) := by
  cases D with
  | linear n m hn hm hnm K hK e =>
    refine odd_card_center_of_psl hA.1 hn ?_ ⟨⟨Nat.prime_two, hm, by omega, ?_, ?_⟩, K,
      inferInstance, inferInstance, hK, ⟨e⟩⟩
    · rintro ⟨rfl, rfl⟩
      exact hnm rfl
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
  | unitary => simp [ClassicalModel.family] at hfam
  | symplectic => simp [ClassicalModel.family] at hfam
  | orthPlus => simp [ClassicalModel.family] at hfam
  | orthMinus => simp [ClassicalModel.family] at hfam

theorem ClassicalModel.odd_card_center {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (D : ClassicalModel A) (hA : CFSG.Open.IsQuasisimple ↥A) (hq : 4 ≤ D.q) :
    Odd (Nat.card (center ↥A)) := by
  have hm2 : ∀ m : ℕ, 4 ≤ 2 ^ m → 2 ≤ m := fun m h =>
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using h)
  have hA' : commutator ↥A = ⊤ := hA.1
  cases D with
  | linear n m hn hm hnm K hK e =>
    have hm' := hm2 m hq
    refine odd_card_center_of_psl hA' hn (by omega) ⟨⟨Nat.prime_two, hm, by omega, ?_, ?_⟩,
      K, inferInstance, inferInstance, hK, ⟨e⟩⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
  | unitary n m hn hm K hK e =>
    have hm' := hm2 m hq
    refine odd_card_center_of_psu hA' hn ⟨⟨Nat.prime_two, hm, by omega, ?_⟩, K, inferInstance,
      inferInstance, hK, ⟨e⟩⟩ (by omega) (by omega)
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  | symplectic n m hn hm hnm K hK e =>
    have hm' := hm2 m hq
    refine odd_card_center_of_psp_pomega hA' (Or.inl rfl)
      ⟨⟨Nat.prime_two, hm, hn, hnm⟩, K, inferInstance, inferInstance, hK, ⟨e⟩⟩
      (by intro h; simp at h; omega)
  | orthPlus n m hn hm K hK e =>
    have hm' := hm2 m hq
    refine odd_card_center_of_psp_pomega hA' (Or.inr (Or.inl rfl))
      ⟨⟨Nat.prime_two, hm, hn⟩, K, inferInstance, inferInstance, hK, ⟨e⟩⟩
      (by intro h; simp at h; omega)
  | orthMinus n m hn hm K hK b c hbc e =>
    refine odd_card_center_of_psp_pomega hA' (Or.inr (Or.inr rfl))
      ⟨⟨Nat.prime_two, hm, hn⟩, K, inferInstance, inferInstance, hK, b, c, hbc, ⟨e⟩⟩
      (by simp)

end CFSG.ComponentClassification.RankTwoClassical
