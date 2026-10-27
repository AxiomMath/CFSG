module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4ExL5
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4ExSp4

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk94

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem e16_psp4 {K : Type} [Group K] [Finite K]
    (h : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ LieModel K .PSp 2 p f) :
    ∃ E : Subgroup K, (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 16 := by
  obtain ⟨p, f, hp, hp2, -, hL⟩ := h
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := statedClassicalModel_of_lieModel (by norm_num) hL
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hp2).pow
  exact exists_E16_of_equiv e (PSp4.exists_E16_sp4 hodd)

theorem e16_psl4 {K : Type} [Group K] [Finite K]
    (h : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 1 ∧ LieModel K .PSL 4 p f) :
    ∃ E : Subgroup K, (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 16 := by
  obtain ⟨p, f, hp, hp2, -, -, hL⟩ := h
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := statedClassicalModel_of_lieModel (by norm_num) hL
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hp2).pow
  refine exists_E16_of_equiv e
    (exists_E16_pauli (CFSG.GH74.GLS.neg_one_ne_one_of_odd_card F hodd) fun i => ?_)
  exact Subgroup.subset_closure (det_pauli i)

theorem e16_psu4 {K : Type} [Group K] [Finite K]
    (h : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 7 ∧ LieModel K .PSU 4 p f) :
    ∃ E : Subgroup K, (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 16 := by
  obtain ⟨p, f, hp, hp2, -, -, hL⟩ := h
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := statedClassicalModel_of_lieModel (by norm_num) hL
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    exact hq.pow
  refine exists_E16_of_equiv e
    (exists_E16_pauli (CFSG.GH74.GLS.neg_one_ne_one_of_odd_card F hodd) fun i => ?_)
  exact Subgroup.subset_closure ⟨det_pauli i, pauli_unitary hq i⟩

theorem e16_psl5 {K : Type} [Group K] [Finite K]
    (h : ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧ LieModel K .PSL 5 p f) :
    ∃ E : Subgroup K, (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 16 := by
  obtain ⟨p, f, -, -, h4, hL⟩ := h
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := statedClassicalModel_of_lieModel (by norm_num) hL
  have hodd : Odd (Nat.card F) := by
    rw [hcard, Nat.odd_iff]
    omega
  refine exists_E16_of_equiv e
    (exists_E16_diag5GL (CFSG.GH74.GLS.neg_one_ne_one_of_odd_card F hodd) fun i => ?_)
  exact Subgroup.subset_closure (det_diag5GL i)

theorem e16_psu5 {K : Type} [Group K] [Finite K]
    (h : ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧ LieModel K .PSU 5 p f) :
    ∃ E : Subgroup K, (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 16 := by
  obtain ⟨p, f, -, -, h4, hL⟩ := h
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := statedClassicalModel_of_lieModel (by norm_num) hL
  have hq : Odd (p ^ f) := by
    rw [Nat.odd_iff]
    omega
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    exact hq.pow
  refine exists_E16_of_equiv e
    (exists_E16_diag5GL (CFSG.GH74.GLS.neg_one_ne_one_of_odd_card F hodd) fun i => ?_)
  exact Subgroup.subset_closure ⟨det_diag5GL i, unitary_diag5GL hq i⟩

end CFSG.GH74.GLS.IVK.Proofs2.Ivk94
