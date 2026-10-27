module

public import CFSG.RankThree.Classical.OddQuadraticFrame

public section

namespace CFSG.LinearAlgebra

open Module QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_orthogonal_basis_quad_eq_repeated [Finite K] (hK : Odd (Nat.card K))
    [FiniteDimensional K V] {d : ℕ} (hd : Module.finrank K V = d) (hd3 : 3 ≤ d) (hd4 : d ≠ 4)
    (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate) :
    ∃ v : Module.Basis (Fin d) K V, (∀ i j, i ≠ j → polar Q (v i) (v j) = 0) ∧
      ∀ i : Fin d, ∃ j : Fin d, j ≠ i ∧ ∃ t : K, t ≠ 0 ∧ Q (v i) = t ^ 2 * Q (v j) := by
  have := Fintype.ofFinite K
  have hK' : Fintype.card K % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hK
  have h2 : (2 : K) ≠ 0 := CFSG.RankThree.Classical.two_ne_zero_of_card_odd hK'
  obtain ⟨v, hvorth, hvnorm, hvlast⟩ :=
    CFSG.RankThree.Classical.exists_orthogonal_basis_quad_eq hK hd (by omega) Q hQ one_ne_zero
  set i₀ : Fin d := ⟨0, by omega⟩
  set i₁ : Fin d := ⟨1, by omega⟩
  set i₂ : Fin d := ⟨d - 1, by omega⟩
  have hi₀ : (i₀ : ℕ) = 0 := rfl
  have hi₁ : (i₁ : ℕ) = 1 := rfl
  have hi₂ : (i₂ : ℕ) = d - 1 := rfl
  have h0₁ : i₀ ≠ i₁ := by
    intro h
    have h' : (0 : ℕ) = 1 := by
      rw [← hi₀, ← hi₁]
      exact congrArg Fin.val h
    exact Nat.zero_ne_one h'
  have h2₀ : i₂ ≠ i₀ := by
    intro h
    have h' : d - 1 = 0 := by
      rw [← hi₂, ← hi₀]
      exact congrArg Fin.val h
    omega
  have h2₁ : i₂ ≠ i₁ := by
    intro h
    have h' : d - 1 = 1 := by
      rw [← hi₂, ← hi₁]
      exact congrArg Fin.val h
    omega
  have hQ0 : Q (v i₀) = 1 := by
    refine hvnorm i₀ ?_
    omega
  have hQ1 : Q (v i₁) = 1 := by
    refine hvnorm i₁ ?_
    omega
  have hc : Q (v i₂) ≠ 0 := hvlast
  have hxy : polar Q (v i₀) (v i₁) = 0 := hvorth i₀ i₁ h0₁
  obtain ⟨s, t, hst⟩ :=
    CFSG.RankThree.Classical.exists_mul_sq_add_mul_sq_eq hK' one_ne_zero one_ne_zero (Q (v i₂))
  let u : V := s • v i₀ + t • v i₁
  let w : V := t • v i₀ + (-s) • v i₁
  have hQu : Q u = Q (v i₂) := by
    show Q (s • v i₀ + t • v i₁) = Q (v i₂)
    rw [CFSG.RankThree.Classical.quad_smul_add_smul Q hxy, hQ0, hQ1]
    linear_combination hst
  have hQw : Q w = Q (v i₂) := by
    show Q (t • v i₀ + (-s) • v i₁) = Q (v i₂)
    rw [CFSG.RankThree.Classical.quad_smul_add_smul Q hxy, hQ0, hQ1]
    linear_combination hst
  have huw : polar Q u w = 0 := by
    show polar Q (s • v i₀ + t • v i₁) (t • v i₀ + (-s) • v i₁) = 0
    rw [CFSG.RankThree.Classical.polar_smul_add_smul Q hxy, hQ0, hQ1]
    ring
  let v' : Fin d → V := fun i => if i = i₀ then u else if i = i₁ then w else v i
  have hv'₀ : v' i₀ = u := by simp [v']
  have hv'₁ : v' i₁ = w := by simp [v', h0₁.symm]
  have hv'o : ∀ i, i ≠ i₀ → i ≠ i₁ → v' i = v i := by
    intro i h0 h1
    simp [v', h0, h1]
  have hvu_orth : ∀ i, i ≠ i₀ → i ≠ i₁ → polar Q (v i) u = 0 := by
    intro i h0 h1
    show polar Q (v i) (s • v i₀ + t • v i₁) = 0
    exact CFSG.RankThree.Classical.polar_smul_add_smul_right_eq_zero Q
      (hvorth i i₀ h0) (hvorth i i₁ h1) s t
  have hvw_orth : ∀ i, i ≠ i₀ → i ≠ i₁ → polar Q (v i) w = 0 := by
    intro i h0 h1
    show polar Q (v i) (t • v i₀ + (-s) • v i₁) = 0
    exact CFSG.RankThree.Classical.polar_smul_add_smul_right_eq_zero Q
      (hvorth i i₀ h0) (hvorth i i₁ h1) t (-s)
  have hu_orth : ∀ i, i ≠ i₀ → i ≠ i₁ → polar Q u (v i) = 0 := by
    intro i h0 h1
    rw [polar_comm]
    exact hvu_orth i h0 h1
  have hw_orth : ∀ i, i ≠ i₀ → i ≠ i₁ → polar Q w (v i) = 0 := by
    intro i h0 h1
    rw [polar_comm]
    exact hvw_orth i h0 h1
  have hv'orth : ∀ i j, i ≠ j → polar Q (v' i) (v' j) = 0 := by
    intro i j hij
    by_cases hi0 : i = i₀
    · subst hi0
      by_cases hj1 : j = i₁
      · subst hj1; rw [hv'₀, hv'₁]; exact huw
      · rw [hv'₀, hv'o j (Ne.symm hij) hj1]; exact hu_orth j (Ne.symm hij) hj1
    · by_cases hi1 : i = i₁
      · subst hi1
        by_cases hj0 : j = i₀
        · subst hj0; rw [hv'₀, hv'₁, polar_comm]; exact huw
        · rw [hv'₁, hv'o j hj0 (Ne.symm hij)]; exact hw_orth j hj0 (Ne.symm hij)
      · rw [hv'o i hi0 hi1]
        by_cases hj0 : j = i₀
        · subst hj0; rw [hv'₀]; exact hvu_orth i hi0 hi1
        · by_cases hj1 : j = i₁
          · subst hj1; rw [hv'₁]; exact hvw_orth i hi0 hi1
          · rw [hv'o j hj0 hj1]; exact hvorth i j hij
  have hmid_norm : ∀ i, i ≠ i₀ → i ≠ i₁ → i ≠ i₂ → Q (v' i) = 1 := by
    intro i h0 h1 h2'
    rw [hv'o i h0 h1]
    refine hvnorm i ?_
    have h' : (i : ℕ) ≠ d - 1 := fun h => h2' (Fin.ext h)
    have := i.isLt
    omega
  have hv'ne : ∀ i, Q (v' i) ≠ 0 := by
    intro i
    by_cases hi0 : i = i₀
    · subst hi0; rw [hv'₀, hQu]; exact hc
    by_cases hi1 : i = i₁
    · subst hi1; rw [hv'₁, hQw]; exact hc
    by_cases hi2 : i = i₂
    · subst hi2; rw [hv'o i₂ h2₀ h2₁]; exact hc
    · rw [hmid_norm i hi0 hi1 hi2]; exact one_ne_zero
  have hli : LinearIndependent K v' :=
    (CFSG.RankThree.Classical.nondegenerate_restrict_span h2 Q hv'orth hv'ne).1
  haveI : Nonempty (Fin d) := ⟨i₀⟩
  have hpair : ∀ i : Fin d, ∃ j : Fin d, j ≠ i ∧
      ∃ t : K, t ≠ 0 ∧ Q (v' i) = t ^ 2 * Q (v' j) := by
    intro i
    have hmid : ∀ j : Fin d, 2 ≤ (j : ℕ) → (j : ℕ) ≤ d - 2 → Q (v' j) = 1 := by
      intro j hj2 hj
      refine hmid_norm j ?_ ?_ ?_
      · intro h
        rw [h, hi₀] at hj2
        omega
      · intro h
        rw [h, hi₁] at hj2
        omega
      · intro h
        rw [h, hi₂] at hj
        omega
    by_cases hi0 : i = i₀
    · subst hi0
      exact ⟨i₁, h0₁.symm, 1, one_ne_zero, by rw [hv'₀, hv'₁, hQu, hQw]; ring⟩
    by_cases hi1 : i = i₁
    · subst hi1
      exact ⟨i₀, h0₁, 1, one_ne_zero, by rw [hv'₁, hv'₀, hQw, hQu]; ring⟩
    by_cases hi2 : i = i₂
    · subst hi2
      refine ⟨i₀, h2₀.symm, 1, one_ne_zero, ?_⟩
      rw [hv'o i₂ h2₀ h2₁, hv'₀, hQu]
      ring
    ·
      have hge : 2 ≤ (i : ℕ) := by
        have h0' : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext (by rw [hi₀]; exact h))
        have h1' : (i : ℕ) ≠ 1 := fun h => hi1 (Fin.ext (by rw [hi₁]; exact h))
        omega
      have hile : (i : ℕ) ≤ d - 2 := by
        have hne : (i : ℕ) ≠ d - 1 := fun h => hi2 (Fin.ext (by rw [hi₂]; exact h))
        have := i.isLt
        omega
      by_cases hi : (i : ℕ) = 2
      · refine ⟨⟨3, by omega⟩, ?_, 1, one_ne_zero, ?_⟩
        · intro h
          have h' : (3 : ℕ) = (i : ℕ) := congrArg Fin.val h
          omega
        · rw [hmid i hge hile, hmid ⟨3, by omega⟩ (by simp) (by simp; omega)]
          ring
      · refine ⟨⟨2, by omega⟩, ?_, 1, one_ne_zero, ?_⟩
        · intro h
          have h' : (2 : ℕ) = (i : ℕ) := congrArg Fin.val h
          omega
        · rw [hmid i hge hile, hmid ⟨2, by omega⟩ (by simp) (by simp; omega)]
          ring
  have hvb : ∀ i : Fin d,
      (basisOfLinearIndependentOfCardEqFinrank hli (by simp [hd]) : Module.Basis (Fin d) K V) i =
        v' i := fun i => by rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [hd]), ?_, ?_⟩
  · intro i j hij
    rw [hvb i, hvb j]
    exact hv'orth i j hij
  · intro i
    obtain ⟨j, hji, t, ht, hval⟩ := hpair i
    exact ⟨j, hji, t, ht, by rw [hvb i, hvb j]; exact hval⟩

end CFSG.LinearAlgebra

end
