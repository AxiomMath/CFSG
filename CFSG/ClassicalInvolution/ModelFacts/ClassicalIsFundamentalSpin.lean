module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpinBridge
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalReduce
public import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
public import CFSG.ClassicalInvolution.ModelFacts.Models

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap

variable {p f : ℕ} [Fact p.Prime]

theorem card_galoisField_facts (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    Odd (Nat.card (GaloisField p f)) ∧ 4 ≤ Nat.card (GaloisField p f) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  exact ⟨by rw [hcard]; exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow, by rw [hcard]; omega⟩

theorem classicalMembersFundamental_pOmegaPlus (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {n : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n p f) :
    ClassicalMembersFundamental p f .POmegaPlus n f hp := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  obtain ⟨hodd, h4⟩ := card_galoisField_facts hp2 hq
  have hM : Generic.modelUniv .POmegaPlus n p f hp =
      ⟨spinGroup (quadPlus n (GaloisField p f)), plusDatum n (GaloisField p f) hn3⟩ :=
    (rfl : Generic.modelUniv .POmegaPlus n p f hp = modelUniv .POmegaPlus n p f hp).trans
      (modelUniv_POmegaPlus (n := n) (p := p) (f := f) hn3)
  have hfin : Finite (Generic.modelUniv .POmegaPlus n p f hp).K :=
    finite_modelUniv (t := .POmegaPlus) hp2 hp trivial hadm
  have hK := (modelClauseZero .POmegaPlus n p f hp trivial hadm).1
  have hlong := isLongestRoot_single .POmegaPlus n p f hp trivial hadm
  rw [modelUniv_POmegaPlus hn3] at hlong
  rw [hM] at hfin hK
  have hfin' : Finite (spinGroup (quadPlus n (GaloisField p f))) := hfin
  suffices h : ∀ M : LieUniversal, M =
      ⟨spinGroup (quadPlus n (GaloisField p f)), plusDatum n (GaloisField p f) hn3⟩ →
      ∀ (L : Subgroup M.K) (z : M.K), IsClassicalMember p f L z →
        L ∈ Generic.fundamentalSubgroups .POmegaPlus M.D from h _ hM
  intro M hM' L z hL
  subst hM'
  have hdim : Module.finrank (GaloisField p f) (Fin n ⊕ Fin n → GaloisField p f) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  set k₀ : Fin n := ⟨0, by omega⟩ with hk₀
  have hperp : 2 ≤ Module.finrank (GaloisField p f)
      ((plusFrame n (GaloisField p f) hn3).toFrame (rootIdxD_ne n (by omega) k₀) true
        (rootSignD n k₀)).perp := by
    have := finrank_perp_add_four ((plusFrame n (GaloisField p f) hn3).toFrame
      (rootIdxD_ne n (by omega) k₀) true (rootSignD n k₀))
    omega
  obtain ⟨x, hx⟩ := exists_conj_longSL2_of_isClassicalMember hodd h4
    (nondegenerate_polarBilin_quadPlus n (GaloisField p f))
    (range_spinAction_quadPlus_eq_commutator hn3) hK (plusFrame n (GaloisField p f) hn3)
    (rootIdxD_ne n (by omega) k₀) true (rootSignD n k₀) hperp hL
  refine ⟨x, Pi.single k₀ 1, Or.inl (hlong k₀ trivial), hx.trans ?_⟩
  have hR := PlusCT.rankOne_plusRootGroup hn3 k₀ (n := n) (K := GaloisField p f)
  exact congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hR.symm

theorem classicalMembersFundamental_pOmegaOdd (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {n : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n p f) :
    ClassicalMembersFundamental p f .POmegaOdd n f hp := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  obtain ⟨hodd, h4⟩ := card_galoisField_facts hp2 hq
  have hM : Generic.modelUniv .POmegaOdd n p f hp =
      ⟨spinGroup (quadOdd n (GaloisField p f)), oddDatum n (GaloisField p f)⟩ := rfl
  have hfin : Finite (Generic.modelUniv .POmegaOdd n p f hp).K :=
    finite_modelUniv (t := .POmegaOdd) hp2 hp trivial hadm
  have hK := (modelClauseZero .POmegaOdd n p f hp trivial hadm).1
  have hlong := isLongestRoot_single .POmegaOdd n p f hp trivial hadm
  rw [hM] at hfin hK
  have hfin' : Finite (spinGroup (quadOdd n (GaloisField p f))) := hfin
  suffices h : ∀ M : LieUniversal, M =
      ⟨spinGroup (quadOdd n (GaloisField p f)), oddDatum n (GaloisField p f)⟩ →
      ∀ (L : Subgroup M.K) (z : M.K), IsClassicalMember p f L z →
        L ∈ Generic.fundamentalSubgroups .POmegaOdd M.D from h _ hM
  intro M hM' L z hL
  subst hM'
  have hdim : Module.finrank (GaloisField p f) (Fin n ⊕ Fin n ⊕ Unit → GaloisField p f) =
      2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  have hk : (0 : ℕ) + 1 < n := by omega
  set k₀ : Fin n := ⟨0, by omega⟩ with hk₀
  set j₀ : Fin n := ⟨0 + 1, hk⟩ with hj₀
  have hij : k₀ ≠ j₀ := Fin.ne_of_val_ne (by simp [hk₀, hj₀])
  have hperp : 2 ≤ Module.finrank (GaloisField p f)
      ((oddFrame n (GaloisField p f)).toHypFrame.toFrame hij true false).perp := by
    have := finrank_perp_add_four
      ((oddFrame n (GaloisField p f)).toHypFrame.toFrame hij true false)
    omega
  obtain ⟨x, hx⟩ := exists_conj_longSL2_of_isClassicalMember hodd h4
    (nondegenerate_polarBilin_quadOdd n (GaloisField p f) (two_ne_zero_galoisField f hp2))
    (range_spinAction_quadOdd_eq_commutator (two_ne_zero_galoisField f hp2) hn3) hK
    (oddFrame n (GaloisField p f)).toHypFrame hij true false hperp hL
  refine ⟨x, Pi.single k₀ 1, Or.inl (hlong k₀ (by show 0 + 1 < n; omega)), hx.trans ?_⟩
  have hR : CFSG.LieType.CurtisTits.rankOne (oddRootGroup n (GaloisField p f)) k₀ =
      (rankOneB (GaloisField p f) k₀).range :=
    le_antisymm (OddCT.rankOne_le_range k₀) (by
      rintro _ ⟨M, rfl⟩
      exact OddCT.rankOneB_mem_rankOne k₀ M)
  rw [rankOneB_of_lt (GaloisField p f) hk rfl hij] at hR
  exact congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hR.symm

theorem classicalMembersFundamental_pOmegaMinus (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {n : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n p f) :
    ClassicalMembersFundamental p f .POmegaMinus n f hp := by
  have hn4 : 4 ≤ n := hadm.2.2
  obtain ⟨hodd, h4⟩ := card_galoisField_facts hp2 hq
  have hM : Generic.modelUniv .POmegaMinus n p f hp =
      ⟨spinGroup (quadMinus n (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2),
        Twisted.minusDatum n (minusCoeffs_irr p f)⟩ := rfl
  have hfin : Finite (Generic.modelUniv .POmegaMinus n p f hp).K :=
    finite_modelUniv (t := .POmegaMinus) hp2 hp trivial hadm
  have hK := (modelClauseZero .POmegaMinus n p f hp trivial hadm).1
  have hlong := isLongestRoot_single .POmegaMinus n p f hp trivial hadm
  rw [hM] at hfin hK
  have hfin' : Finite
      (spinGroup (quadMinus n (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)) := hfin
  suffices h : ∀ M : LieUniversal, M =
      ⟨spinGroup (quadMinus n (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2),
        Twisted.minusDatum n (minusCoeffs_irr p f)⟩ →
      ∀ (L : Subgroup M.K) (z : M.K), IsClassicalMember p f L z →
        L ∈ Generic.fundamentalSubgroups .POmegaMinus M.D from h _ hM
  intro M hM' L z hL
  subst hM'
  have hdim : Module.finrank (GaloisField p f)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField p f) = 2 * (n - 1) + 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    ring
  have hk : (0 : ℕ) + 1 < n - 1 := by omega
  set k₀ : Fin (n - 1) := ⟨0, by omega⟩ with hk₀
  have hij := Twisted.succ_ne_of_lt n (k := k₀) hk
  have hperp : 2 ≤ Module.finrank (GaloisField p f)
      ((Twisted.minusFrame n (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame.toFrame hij
        true false).perp := by
    have := finrank_perp_add_four
      ((Twisted.minusFrame n (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame.toFrame hij
        true false)
    omega
  obtain ⟨x, hx⟩ := exists_conj_longSL2_of_isClassicalMember hodd h4
    (nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField p f) (minusCoeffs_irr p f))
    (range_spinAction_quadMinus_eq_commutator hn4 (minusCoeffs_irr p f)) hK
    (Twisted.minusFrame n (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame hij true false
    hperp hL
  refine ⟨x, Pi.single k₀ 1, Or.inl (hlong k₀ (by show 0 + 2 < n; omega)), hx.trans ?_⟩
  have hR := Twisted.rankOne_minusRootGroup_of_lt n (minusCoeffs_irr p f) (k := k₀) hk
  exact congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hR.symm

end CFSG.ClassicalInvolution.ModelFacts
