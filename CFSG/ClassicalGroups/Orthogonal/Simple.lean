module

public import CFSG.ClassicalGroups.Orthogonal.Models
public import CFSG.ClassicalGroups.Orthogonal.Matrix

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin

theorem ringChar_eq_of_card_eq {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) : ringChar K = p := by
  have := Fintype.ofFinite K
  have hq := CharP.prime_ringChar K
  obtain ⟨m, -, hm⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card] at hK
  have hdvd : p ∣ ringChar K ^ (m : ℕ) := by
    rw [← hm, hK]
    exact dvd_pow_self p (by omega)
  exact ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd)).symm

theorem two_eq_zero_iff_ringChar_eq_two {K : Type} [Field K] (hq : (ringChar K).Prime) :
    (2 : K) = 0 ↔ ringChar K = 2 := by
  rw [show (2 : K) = ((2 : ℕ) : K) by norm_num, ringChar.spec,
    Nat.prime_dvd_prime_iff_eq hq Nat.prime_two]

theorem two_ne_zero_of_charP {K : Type} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : p ≠ 2) : (2 : K) ≠ 0 := by
  have hq : (ringChar K).Prime := by rw [ringChar.eq K p]; exact Fact.out
  rw [Ne, two_eq_zero_iff_ringChar_eq_two hq, ringChar.eq K p]
  exact hp

section Odd

variable {n : ℕ} {K : Type} [Field K]

private theorem oddPairs (hn : 3 ≤ n) :
    (oddPair K (⟨0, by omega⟩ : Fin n)).Orth (oddPair K ⟨1, by omega⟩) ∧
      (oddPair K (⟨0, by omega⟩ : Fin n)).Orth (oddPair K ⟨2, by omega⟩) ∧
      (oddPair K (⟨1, by omega⟩ : Fin n)).Orth (oddPair K ⟨2, by omega⟩) :=
  ⟨oddPair_orth (by simp [Fin.ext_iff]), oddPair_orth (by simp [Fin.ext_iff]),
    oddPair_orth (by simp [Fin.ext_iff])⟩

theorem commutator_orthogonalGroup_quadOdd (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup (quadOdd n K),
      TauCeti.QuadraticMap.orthogonalGroup (quadOdd n K)⁆ = elementaryGroup (quadOdd n K) :=
  commutator_orthogonalGroup_eq_elementaryGroup_of_two_ne_zero h2
    (nondegenerate_polarBilin_quadOdd n K h2) (oddPairs hn).1 (oddPairs hn).2.1 (oddPairs hn).2.2

theorem statedOmega_quadOdd_eq_map (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    StatedOmega (StatedQuadOdd n K) =
      (elementaryGroup (quadOdd n K)).map (toLinEquiv (Fin n ⊕ Fin n ⊕ Unit) K).symm.toMonoidHom :=
  statedOmega_eq_map_elementaryGroup (coe_quadOdd n K) (commutator_orthogonalGroup_quadOdd h2 hn)

theorem isSimpleGroup_projElementary_quadOdd (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    IsSimpleGroup (ProjElementary (quadOdd n K)) :=
  isSimpleGroup_projElementary_of_hypPairs (nondegenerate_polarBilin_quadOdd n K h2)
    (oddPairs hn).1 (oddPairs hn).2.1 (oddPairs hn).2.2

theorem regular_quadOdd (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    (polarBilin (quadOdd n K)).Nondegenerate ∧
      ∃ T : Submodule K (Fin n ⊕ Fin n ⊕ Unit → K), Module.finrank K T = 3 ∧
        ∀ x ∈ T, quadOdd n K x = 0 :=
  ⟨nondegenerate_polarBilin_quadOdd n K h2,
    exists_totallySingular_of_hypPairs (oddPairs hn).1 (oddPairs hn).2.1 (oddPairs hn).2.2⟩

theorem isSimpleGroup_statedProj_statedOmega_quadOdd_of_two_ne_zero (h2 : (2 : K) ≠ 0)
    (hn : 3 ≤ n) : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadOdd n K))) :=
  have := isSimpleGroup_projElementary_quadOdd (K := K) h2 hn
  isSimpleGroup_statedProj_of_eq (coe_quadOdd n K) (commutator_orthogonalGroup_quadOdd h2 hn)

theorem isSimpleGroup_statedProj_statedOmega_quadOdd (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : p ≠ 2) (hn : 3 ≤ n) : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadOdd n K))) :=
  isSimpleGroup_statedProj_statedOmega_quadOdd_of_two_ne_zero (two_ne_zero_of_charP p hp) hn

end Odd

section Plus

variable {n : ℕ} {K : Type} [Field K]

private theorem plusPairs (hn : 3 ≤ n) :
    (plusPair K (⟨0, by omega⟩ : Fin n)).Orth (plusPair K ⟨1, by omega⟩) ∧
      (plusPair K (⟨0, by omega⟩ : Fin n)).Orth (plusPair K ⟨2, by omega⟩) ∧
      (plusPair K (⟨1, by omega⟩ : Fin n)).Orth (plusPair K ⟨2, by omega⟩) :=
  ⟨plusPair_orth (by simp [Fin.ext_iff]), plusPair_orth (by simp [Fin.ext_iff]),
    plusPair_orth (by simp [Fin.ext_iff])⟩

theorem commutator_orthogonalGroup_quadPlus (hn : 3 ≤ n) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K)⁆ = elementaryGroup (quadPlus n K) := by
  by_cases h2 : (2 : K) = 0
  · have hn0 : 0 < n := by omega
    exact commutator_orthogonalGroup_eq_of_two_eq_zero (plusFamily_orth hn0)
      (nondegenerate_polarBilin_quadPlus n K) h2
      (fun x hx _ => eq_zero_of_mem_tailSpace_plusFamily hn0 hx)
      (fun x hx hx0 => absurd (eq_zero_of_mem_tailSpace_plusFamily hn0 hx) hx0) hn
  · exact commutator_orthogonalGroup_eq_elementaryGroup_of_two_ne_zero h2
      (nondegenerate_polarBilin_quadPlus n K) (plusPairs hn).1 (plusPairs hn).2.1
      (plusPairs hn).2.2

theorem statedOmega_quadPlus_eq_map (hn : 3 ≤ n) :
    StatedOmega (StatedQuadPlus n K) =
      (elementaryGroup (quadPlus n K)).map (toLinEquiv (Fin n ⊕ Fin n) K).symm.toMonoidHom :=
  statedOmega_eq_map_elementaryGroup (coe_quadPlus n K) (commutator_orthogonalGroup_quadPlus hn)

theorem isSimpleGroup_projElementary_quadPlus (hn : 3 ≤ n) :
    IsSimpleGroup (ProjElementary (quadPlus n K)) :=
  isSimpleGroup_projElementary_of_hypPairs (nondegenerate_polarBilin_quadPlus n K)
    (plusPairs hn).1 (plusPairs hn).2.1 (plusPairs hn).2.2

theorem regular_quadPlus (hn : 3 ≤ n) :
    (polarBilin (quadPlus n K)).Nondegenerate ∧
      ∃ T : Submodule K (Fin n ⊕ Fin n → K), Module.finrank K T = 3 ∧
        ∀ x ∈ T, quadPlus n K x = 0 :=
  ⟨nondegenerate_polarBilin_quadPlus n K,
    exists_totallySingular_of_hypPairs (plusPairs hn).1 (plusPairs hn).2.1 (plusPairs hn).2.2⟩

theorem isSimpleGroup_statedProj_statedOmega_quadPlus (hn : 3 ≤ n) :
    IsSimpleGroup (StatedProj (StatedOmega (StatedQuadPlus n K))) :=
  have := isSimpleGroup_projElementary_quadPlus (K := K) hn
  isSimpleGroup_statedProj_of_eq (coe_quadPlus n K) (commutator_orthogonalGroup_quadPlus hn)

end Plus

section Minus

variable {n : ℕ} {K : Type} [Field K] {b c : K}

private theorem minusPairs (hn : 4 ≤ n) :
    (minusPair K b c (⟨0, by omega⟩ : Fin (n - 1))).Orth (minusPair K b c ⟨1, by omega⟩) ∧
      (minusPair K b c (⟨0, by omega⟩ : Fin (n - 1))).Orth (minusPair K b c ⟨2, by omega⟩) ∧
      (minusPair K b c (⟨1, by omega⟩ : Fin (n - 1))).Orth (minusPair K b c ⟨2, by omega⟩) :=
  ⟨minusPair_orth (by simp [Fin.ext_iff]), minusPair_orth (by simp [Fin.ext_iff]),
    minusPair_orth (by simp [Fin.ext_iff])⟩

theorem commutator_orthogonalGroup_quadMinus [Finite K] (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c)⁆ =
        elementaryGroup (quadMinus n K b c) := by
  have hnd := nondegenerate_polarBilin_quadMinus_of_finite n K hirr
  by_cases h2 : (2 : K) = 0
  · have hn0 : 0 < n - 1 := by omega
    exact commutator_orthogonalGroup_eq_of_two_eq_zero (minusFamily_orth hn0) hnd h2
      (fun x hx hQ => eq_zero_of_mem_tailSpace_minusFamily hirr hn0 hx hQ)
      (fun x hx hx0 y hy hxy => exists_eq_smul_of_mem_tailSpace_minusFamily h2 hirr hn0 hx hx0 hy
        hxy) (by omega)
  · exact commutator_orthogonalGroup_eq_elementaryGroup_of_two_ne_zero h2 hnd
      (minusPairs hn).1 (minusPairs hn).2.1 (minusPairs hn).2.2

theorem statedOmega_quadMinus_eq_map [Finite K] (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    StatedOmega (StatedQuadMinus n K b c) =
      (elementaryGroup (quadMinus n K b c)).map
        (toLinEquiv (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K).symm.toMonoidHom :=
  statedOmega_eq_map_elementaryGroup (coe_quadMinus n K b c)
    (commutator_orthogonalGroup_quadMinus hn hirr)

theorem isSimpleGroup_projElementary_quadMinus [Finite K] (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsSimpleGroup (ProjElementary (quadMinus n K b c)) :=
  isSimpleGroup_projElementary_of_hypPairs (nondegenerate_polarBilin_quadMinus_of_finite n K hirr)
    (minusPairs hn).1 (minusPairs hn).2.1 (minusPairs hn).2.2

theorem regular_quadMinus [Finite K] (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (polarBilin (quadMinus n K b c)).Nondegenerate ∧
      ∃ T : Submodule K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K), Module.finrank K T = 3 ∧
        ∀ x ∈ T, quadMinus n K b c x = 0 :=
  ⟨nondegenerate_polarBilin_quadMinus_of_finite n K hirr,
    exists_totallySingular_of_hypPairs (minusPairs hn).1 (minusPairs hn).2.1
      (minusPairs hn).2.2⟩

theorem isSimpleGroup_statedProj_statedOmega_quadMinus [Finite K] (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsSimpleGroup (StatedProj (StatedOmega (StatedQuadMinus n K b c))) :=
  have := isSimpleGroup_projElementary_quadMinus hn hirr
  isSimpleGroup_statedProj_of_eq (coe_quadMinus n K b c)
    (commutator_orthogonalGroup_quadMinus hn hirr)

end Minus

theorem isSimpleGroup_of_statedClassicalModel_POmegaOdd (G : Type) [Group G] (n p f : ℕ)
    (h : StatedClassicalModel G .POmegaOdd n p f) : Nontrivial G ∧ IsSimpleGroup G := by
  obtain ⟨⟨hp, hf, hn, hp2⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hq : (ringChar K).Prime := by rw [ringChar_eq_of_card_eq hp hf hK]; exact hp
  have h2 : (2 : K) ≠ 0 := by
    rw [Ne, two_eq_zero_iff_ringChar_eq_two hq, ringChar_eq_of_card_eq hp hf hK]
    exact hp2
  have := isSimpleGroup_statedProj_statedOmega_quadOdd_of_two_ne_zero h2 hn
  have hG : IsSimpleGroup G := e.isSimpleGroup
  exact ⟨inferInstance, hG⟩

theorem isSimpleGroup_of_statedClassicalModel_POmegaPlus (G : Type) [Group G] (n p f : ℕ)
    (h : StatedClassicalModel G .POmegaPlus n p f) : Nontrivial G ∧ IsSimpleGroup G := by
  obtain ⟨⟨-, -, hn⟩, K, _, _, -, ⟨e⟩⟩ := h
  have := isSimpleGroup_statedProj_statedOmega_quadPlus (K := K) (n := n) (by omega)
  have hG : IsSimpleGroup G := e.isSimpleGroup
  exact ⟨inferInstance, hG⟩

theorem isSimpleGroup_of_statedClassicalModel_POmegaMinus (G : Type) [Group G] (n p f : ℕ)
    (h : StatedClassicalModel G .POmegaMinus n p f) : Nontrivial G ∧ IsSimpleGroup G := by
  obtain ⟨⟨-, -, hn⟩, K, _, _, -, b, c, hirr, ⟨e⟩⟩ := h
  have := isSimpleGroup_statedProj_statedOmega_quadMinus (K := K) hn hirr
  have hG : IsSimpleGroup G := e.isSimpleGroup
  exact ⟨inferInstance, hG⟩


theorem isSimpleGroup_of_statedClassicalModel_orthogonal_of_odd (G : Type) [Group G]
    (t : StatedLieTag) (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (n p f : ℕ)
    (_hp : Odd p) (h : StatedClassicalModel G t n p f) : Nontrivial G ∧ IsSimpleGroup G := by
  rcases ht with rfl | rfl | rfl
  · exact isSimpleGroup_of_statedClassicalModel_POmegaOdd G n p f h
  · exact isSimpleGroup_of_statedClassicalModel_POmegaPlus G n p f h
  · exact isSimpleGroup_of_statedClassicalModel_POmegaMinus G n p f h

theorem isSimpleGroup_of_statedClassicalModel_orthogonal_two (G : Type) [Group G]
    (t : StatedLieTag) (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (n f : ℕ)
    (h : StatedClassicalModel G t n 2 f) : Nontrivial G ∧ IsSimpleGroup G := by
  rcases ht with rfl | rfl
  · exact isSimpleGroup_of_statedClassicalModel_POmegaPlus G n 2 f h
  · exact isSimpleGroup_of_statedClassicalModel_POmegaMinus G n 2 f h

end CFSG.ClassicalGroups.Orthogonal
