module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesSign

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {U : Type} [AddCommGroup U] [Module (ZMod 3) U] [FiniteDimensional (ZMod 3) U]
  {R : QuadraticForm (ZMod 3) U}

private lemma fk_zmod3_eq_one_or_neg_one : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by
  decide

private lemma fk_add_self_eq_neg (a : ZMod 3) : a + a = -a := by
  revert a
  decide

private lemma fk_two_nsmul_eq_neg (a : ZMod 3) : 2 • a = -a := by
  revert a
  decide

private lemma fk_sign_pattern (w : Fin 3 → ZMod 3) (hw : ∀ i, w i = 1 ∨ w i = -1)
    (hne : ¬ ∀ i j, w i = w j) :
    ∃ p q r : Fin 3, p ≠ q ∧ r ≠ p ∧ r ≠ q ∧ w p = w q ∧ w r = -w p := by
  revert w
  decide

private lemma fk_associated_separatingLeft (hR : R.Nondegenerate) :
    (QuadraticMap.associated (R := ZMod 3) R).SeparatingLeft := by
  intro x hx
  have hxmem : x ∈ (QuadraticMap.associated (R := ZMod 3) R).ker := by
    rw [LinearMap.mem_ker]
    ext y
    exact hx y
  have hrad : x ∈ R.radical := by
    rw [QuadraticMap.radical_eq_ker_associated]
    exact hxmem
  rw [hR.radical_eq_bot] at hrad
  simpa using hrad

private lemma fk_norm_ne_zero (b : Module.Basis (Fin 3) (ZMod 3) U)
    (horth : (QuadraticMap.associated (R := ZMod 3) R).IsOrthoᵢ b) (hR : R.Nondegenerate)
    (i : Fin 3) : R (b i) ≠ 0 := by
  have h := horth.not_isOrtho_basis_self_of_separatingLeft (fk_associated_separatingLeft hR) i
  have hself : QuadraticMap.associated (R := ZMod 3) R (b i) (b i) = R (b i) :=
    QuadraticMap.associated_eq_self_apply (ZMod 3) R (b i)
  rwa [hself] at h

private theorem fk_equal_norm_basis (b : Module.Basis (Fin 3) (ZMod 3) U)
    (hdim : Module.finrank (ZMod 3) U = 3)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar R (b i) (b j) = 0)
    (hnorm : ∀ i, R (b i) = 1 ∨ R (b i) = -1) :
    ∃ (b' : Module.Basis (Fin 3) (ZMod 3) U) (ε : ZMod 3), ε ≠ 0 ∧
      (∀ i, R (b' i) = ε) ∧ ∀ i j, i ≠ j → QuadraticMap.polar R (b' i) (b' j) = 0 := by
  by_cases hall : ∀ i j, R (b i) = R (b j)
  · refine ⟨b, R (b 0), ?_, fun i => hall i 0, horth⟩
    rcases hnorm 0 with h | h <;> rw [h] <;> decide
  · obtain ⟨p, q, r, hpq, hrp, hrq, hpqw, hrw⟩ :=
      fk_sign_pattern (fun i => R (b i)) hnorm hall
    set a : ZMod 3 := R (b p) with ha_def
    have hq : R (b q) = a := hpqw.symm
    have hr : R (b r) = -a := hrw
    have ha0 : a ≠ 0 := by
      rcases hnorm p with h | h <;> rw [ha_def, h] <;> decide
    have hpq0 : QuadraticMap.polar R (b p) (b q) = 0 := horth p q hpq
    have hpr0 : QuadraticMap.polar R (b p) (b r) = 0 := horth p r (Ne.symm hrp)
    have hqr0 : QuadraticMap.polar R (b q) (b r) = 0 := horth q r (Ne.symm hrq)
    let b' : Fin 3 → U := ![b p + b q, b p - b q, b r]
    have hb'0 : b' 0 = b p + b q := by simp [b']
    have hb'1 : b' 1 = b p - b q := by simp [b']
    have hb'2 : b' 2 = b r := by simp [b']
    have hnorm0 : R (b' 0) = R (b r) := by
      rw [hb'0, QuadraticMap.map_add (R : U → ZMod 3) (b p) (b q), ← ha_def, hq,
        hpq0, add_zero, fk_add_self_eq_neg, hr]
    have hnorm1 : R (b' 1) = R (b r) := by
      rw [hb'1, sub_eq_add_neg, QuadraticMap.map_add (R : U → ZMod 3) (b p) (-(b q)),
        QuadraticMap.map_neg R (b q), QuadraticMap.polar_neg_right R (b p) (b q),
        ← ha_def, hq, hpq0, neg_zero, add_zero, fk_add_self_eq_neg, hr]
    have hnorm2 : R (b' 2) = R (b r) := by rw [hb'2]
    have h01 : QuadraticMap.polar R (b' 0) (b' 1) = 0 := by
      rw [hb'0, hb'1, sub_eq_add_neg]
      simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
        QuadraticMap.polar_neg_left, QuadraticMap.polar_neg_right,
        QuadraticMap.polar_comm R (b q) (b p), hpq0, QuadraticMap.polar_self,
        ← ha_def, hq, neg_zero, add_zero, zero_add, add_neg_cancel]
    have h02 : QuadraticMap.polar R (b' 0) (b' 2) = 0 := by
      rw [hb'0, hb'2]
      simp only [QuadraticMap.polar_add_left, hpr0, hqr0, add_zero]
    have h12 : QuadraticMap.polar R (b' 1) (b' 2) = 0 := by
      rw [hb'1, hb'2, sub_eq_add_neg]
      simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_neg_left, hpr0, hqr0,
        neg_zero, add_zero]
    have h10 : QuadraticMap.polar R (b' 1) (b' 0) = 0 := by
      rw [QuadraticMap.polar_comm, h01]
    have h20 : QuadraticMap.polar R (b' 2) (b' 0) = 0 := by
      rw [QuadraticMap.polar_comm, h02]
    have h21 : QuadraticMap.polar R (b' 2) (b' 1) = 0 := by
      rw [QuadraticMap.polar_comm, h12]
    have hortho' : ∀ i j, i ≠ j → QuadraticMap.polar R (b' i) (b' j) = 0 := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        first
          | exact absurd rfl hij
          | exact h01
          | exact h02
          | exact h10
          | exact h12
          | exact h20
          | exact h21
    have hli : LinearIndependent (ZMod 3) b' := by
      refine LinearMap.linearIndependent_of_isOrthoᵢ (B := QuadraticMap.polarBilin R) ?_ ?_
      · rw [LinearMap.isOrthoᵢ_def]
        intro i j hij
        rw [QuadraticMap.polarBilin_apply_apply]
        exact hortho' i j hij
      · intro i
        rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self]
        have hi : R (b' i) = R (b r) := by
          fin_cases i
          · exact hnorm0
          · exact hnorm1
          · exact hnorm2
        rw [hi, fk_two_nsmul_eq_neg, hr, neg_neg]
        exact ha0
    have hcard : Fintype.card (Fin 3) = Module.finrank (ZMod 3) U := by
      rw [Fintype.card_fin, hdim]
    let bb := basisOfLinearIndependentOfCardEqFinrank hli hcard
    have hcoe : ⇑bb = b' := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
    refine ⟨bb, R (b r), ?_, ?_, ?_⟩
    · rw [hr]
      exact neg_ne_zero.mpr ha0
    · intro i
      rw [hcoe]
      fin_cases i
      · exact hnorm0
      · exact hnorm1
      · exact hnorm2
    · intro i j hij
      rw [hcoe]
      exact hortho' i j hij

theorem fkFrameBasis_exists (hR : R.Nondegenerate) (hdim : Module.finrank (ZMod 3) U = 3) :
    ∃ (b : Module.Basis (Fin 3) (ZMod 3) U) (ε : ZMod 3), ε ≠ 0 ∧ (∀ i, R (b i) = ε) ∧
      ∀ i j, i ≠ j → QuadraticMap.polar R (b i) (b j) = 0 := by
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (K := ZMod 3) (V := U) (B := QuadraticMap.associated (R := ZMod 3) R)
    (QuadraticForm.associated_isSymm (ZMod 3) R)
  let b : Module.Basis (Fin 3) (ZMod 3) U := v.reindex (finCongr hdim)
  have hborth : (QuadraticMap.associated (R := ZMod 3) R).IsOrthoᵢ b := by
    rw [LinearMap.isOrthoᵢ_def] at hv ⊢
    intro i j hij
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply]
    exact hv ((finCongr hdim).symm i) ((finCongr hdim).symm j)
      (fun h => hij ((finCongr hdim).symm.injective h))
  rw [LinearMap.isOrthoᵢ_def] at hborth
  have horth : ∀ i j, i ≠ j → QuadraticMap.polar R (b i) (b j) = 0 := by
    intro i j hij
    exact QuadraticMap.IsOrtho.polar_eq_zero
      ((QuadraticMap.associated_isOrtho).mp (hborth i j hij))
  have hnorm : ∀ i, R (b i) = 1 ∨ R (b i) = -1 := fun i =>
    fk_zmod3_eq_one_or_neg_one (R (b i)) (fk_norm_ne_zero b hborth hR i)
  exact fk_equal_norm_basis b hdim horth hnorm

end CFSG.OddStandard.SmallF3.Omega
