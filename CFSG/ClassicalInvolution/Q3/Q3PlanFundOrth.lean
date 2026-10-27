module

public import CFSG.ClassicalInvolution.Q3.Q3PlanOrthMain
public import CFSG.ClassicalInvolution.Q3.Q3PlanTags

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small

private theorem natCard_galoisField_three_orth : Nat.card (GaloisField 3 1) = 3 := by
  rw [GaloisField.card 3 1 (by norm_num)]
  norm_num

theorem classicalMembersFundamental3Tag_POmegaPlus :
    ClassicalMembersFundamental3Tag .POmegaPlus := by
  intro n hp hFT hadm L z hL hO
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  have hM : Generic.modelUniv .POmegaPlus n 3 1 hp =
      ⟨spinGroup (quadPlus n (GaloisField 3 1)), plusDatum n (GaloisField 3 1) hn3⟩ :=
    (rfl : Generic.modelUniv .POmegaPlus n 3 1 hp =
        ModelFacts.modelUniv .POmegaPlus n 3 1 hp).trans
      (modelUniv_POmegaPlus (n := n) (p := 3) (f := 1) hn3)
  have hK := (modelClauseZero .POmegaPlus n 3 1 hp hFT hadm).1
  have hlong := isLongestRoot_single .POmegaPlus n 3 1 hp hFT hadm
  rw [modelUniv_POmegaPlus hn3] at hlong
  rw [hM] at hK
  suffices h : ∀ M : LieUniversal, M =
      ⟨spinGroup (quadPlus n (GaloisField 3 1)), plusDatum n (GaloisField 3 1) hn3⟩ →
      ∀ (L : Subgroup M.K) (z : M.K), IsClassicalMember3 L z → classicalInvolutionOddCore L = ⊥ →
        L ∈ Generic.fundamentalSubgroups .POmegaPlus M.D from h _ hM L z hL hO
  intro M hM' L z hL hO
  subst hM'
  have hdim : Module.finrank (GaloisField 3 1) (Fin n ⊕ Fin n → GaloisField 3 1) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  set k₀ : Fin n := ⟨0, by omega⟩ with hk₀
  have hperp : 2 ≤ Module.finrank (GaloisField 3 1)
      ((plusFrame n (GaloisField 3 1) hn3).toFrame (rootIdxD_ne n (by omega) k₀) true
        (rootSignD n k₀)).perp := by
    have := finrank_perp_add_four ((plusFrame n (GaloisField 3 1) hn3).toFrame
      (rootIdxD_ne n (by omega) k₀) true (rootSignD n k₀))
    omega
  obtain ⟨x, hx⟩ := exists_conj_longSL2_of_isClassicalMember3
    (nondegenerate_polarBilin_quadPlus n (GaloisField 3 1))
    (range_spinAction_quadPlus_eq_commutator hn3) (commutator_orthogonalGroup_quadPlus hn3).le hK
    (plusFrame n (GaloisField 3 1) hn3) (rootIdxD_ne n (by omega) k₀) true (rootSignD n k₀) hperp
    hL hO
  refine ⟨x, Pi.single k₀ 1, Or.inl (hlong k₀ trivial), hx.trans ?_⟩
  have hR := PlusCT.rankOne_plusRootGroup hn3 k₀ (n := n) (K := GaloisField 3 1)
  exact congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hR.symm

theorem classicalMembersFundamental3Tag_POmegaOdd :
    ClassicalMembersFundamental3Tag .POmegaOdd := by
  intro n hp hFT hadm L z hL hO
  have hn3 : 3 ≤ n := hadm.2.2.1
  have h2 : (2 : GaloisField 3 1) ≠ 0 :=
    (three_eq_zero_two_ne_zero_of_card_eq_three natCard_galoisField_three_orth).2
  have hM : Generic.modelUniv .POmegaOdd n 3 1 hp =
      ⟨spinGroup (quadOdd n (GaloisField 3 1)), oddDatum n (GaloisField 3 1)⟩ := rfl
  have hK := (modelClauseZero .POmegaOdd n 3 1 hp hFT hadm).1
  have hlong := isLongestRoot_single .POmegaOdd n 3 1 hp hFT hadm
  rw [hM] at hK
  suffices h : ∀ M : LieUniversal, M =
      ⟨spinGroup (quadOdd n (GaloisField 3 1)), oddDatum n (GaloisField 3 1)⟩ →
      ∀ (L : Subgroup M.K) (z : M.K), IsClassicalMember3 L z → classicalInvolutionOddCore L = ⊥ →
        L ∈ Generic.fundamentalSubgroups .POmegaOdd M.D from h _ hM L z hL hO
  intro M hM' L z hL hO
  subst hM'
  have hdim : Module.finrank (GaloisField 3 1) (Fin n ⊕ Fin n ⊕ Unit → GaloisField 3 1) =
      2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  have hk : (0 : ℕ) + 1 < n := by omega
  set k₀ : Fin n := ⟨0, by omega⟩ with hk₀
  set j₀ : Fin n := ⟨0 + 1, hk⟩ with hj₀
  have hij : k₀ ≠ j₀ := Fin.ne_of_val_ne (by simp [hk₀, hj₀])
  have hperp : 2 ≤ Module.finrank (GaloisField 3 1)
      ((oddFrame n (GaloisField 3 1)).toHypFrame.toFrame hij true false).perp := by
    have := finrank_perp_add_four
      ((oddFrame n (GaloisField 3 1)).toHypFrame.toFrame hij true false)
    omega
  obtain ⟨x, hx⟩ := exists_conj_longSL2_of_isClassicalMember3
    (nondegenerate_polarBilin_quadOdd n (GaloisField 3 1) h2)
    (range_spinAction_quadOdd_eq_commutator h2 hn3) (commutator_orthogonalGroup_quadOdd h2 hn3).le
    hK (oddFrame n (GaloisField 3 1)).toHypFrame hij true false hperp hL hO
  refine ⟨x, Pi.single k₀ 1, Or.inl (hlong k₀ (by show 0 + 1 < n; omega)), hx.trans ?_⟩
  have hR : CFSG.LieType.CurtisTits.rankOne (oddRootGroup n (GaloisField 3 1)) k₀ =
      (rankOneB (GaloisField 3 1) k₀).range :=
    le_antisymm (OddCT.rankOne_le_range k₀) (by
      rintro _ ⟨M, rfl⟩
      exact OddCT.rankOneB_mem_rankOne k₀ M)
  rw [rankOneB_of_lt (GaloisField 3 1) hk rfl hij] at hR
  exact congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hR.symm

theorem classicalMembersFundamental3Tag_POmegaMinus :
    ClassicalMembersFundamental3Tag .POmegaMinus := by
  intro n hp hFT hadm L z hL hO
  have hn4 : 4 ≤ n := hadm.2.2
  have hM : Generic.modelUniv .POmegaMinus n 3 1 hp =
      ⟨spinGroup (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
        Twisted.minusDatum n (minusCoeffs_irr 3 1)⟩ := rfl
  have hK := (modelClauseZero .POmegaMinus n 3 1 hp hFT hadm).1
  have hlong := isLongestRoot_single .POmegaMinus n 3 1 hp hFT hadm
  rw [hM] at hK
  suffices h : ∀ M : LieUniversal, M =
      ⟨spinGroup (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
        Twisted.minusDatum n (minusCoeffs_irr 3 1)⟩ →
      ∀ (L : Subgroup M.K) (z : M.K), IsClassicalMember3 L z → classicalInvolutionOddCore L = ⊥ →
        L ∈ Generic.fundamentalSubgroups .POmegaMinus M.D from h _ hM L z hL hO
  intro M hM' L z hL hO
  subst hM'
  have hdim : Module.finrank (GaloisField 3 1)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 3 1) = 2 * (n - 1) + 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    ring
  have hk : (0 : ℕ) + 1 < n - 1 := by omega
  set k₀ : Fin (n - 1) := ⟨0, by omega⟩ with hk₀
  have hij := Twisted.succ_ne_of_lt n (k := k₀) hk
  have hperp : 2 ≤ Module.finrank (GaloisField 3 1)
      ((Twisted.minusFrame n (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame.toFrame hij
        true false).perp := by
    have := finrank_perp_add_four
      ((Twisted.minusFrame n (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame.toFrame hij
        true false)
    omega
  obtain ⟨x, hx⟩ := exists_conj_longSL2_of_isClassicalMember3
    (nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 3 1) (minusCoeffs_irr 3 1))
    (range_spinAction_quadMinus_eq_commutator hn4 (minusCoeffs_irr 3 1))
    (commutator_orthogonalGroup_quadMinus hn4 (minusCoeffs_irr 3 1)).le hK
    (Twisted.minusFrame n (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame hij true false hperp
    hL hO
  refine ⟨x, Pi.single k₀ 1, Or.inl (hlong k₀ (by show 0 + 2 < n; omega)), hx.trans ?_⟩
  have hR := Twisted.rankOne_minusRootGroup_of_lt n (minusCoeffs_irr 3 1) (k := k₀) hk
  exact congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hR.symm

end CFSG.ClassicalInvolution.Q3
