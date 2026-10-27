module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClUGraphOrth
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClUGraphSymp
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClUGraphThree
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClUFam

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank Module
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.Burgoyne.PSL (OrthNF diagGL)

theorem ClU.uGraphInput : ClU.UGraphInput := by
  intro p f K _ h hp2 n hn hinj A c hAc R hRodd hRi hRc
  suffices hall : ∀ y ∈ R, y = 1 by
    intro r₁ h₁ r₂ h₂
    rw [hall r₁ h₁, hall r₂ h₂]
  have := h.finite
  have := h.charP
  have h2K : (2 : K) ≠ 0 := by
    intro e
    have e' : ((2 : ℕ) : K) = 0 := by exact_mod_cast e
    rw [CharP.cast_eq_zero_iff K p] at e'
    have := Nat.le_of_dvd (by norm_num) e'
    have := h.prime.two_le
    exact hp2 (by omega)
  have h2F : (2 : h.fixedField) ≠ 0 := fun e => h2K (by
    have h1 : ((1 + 1 : h.fixedField) : K) = 1 + 1 := by rw [Subfield.coe_add, Subfield.coe_one]
    rw [← one_add_one_eq_two] at e ⊢
    rw [← h1, e, Subfield.coe_zero])
  have hF2 : ringChar h.fixedField ≠ 2 := fun e => h2F (by
    have := ringChar.spec h.fixedField 2
    exact_mod_cast (this.2 (by rw [e])))
  set Am := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  replace hAc : Am * Am.map h.bar = c • 1 := hAc
  have hA : (Am.map h.bar)ᵀ * Am = 1 := (mem_uU h).1 A.2
  have hc0 : c ≠ 0 := by
    rintro rfl
    have e : Am.map h.bar = 0 := by
      calc Am.map h.bar = ((Am.map h.bar)ᵀ * Am) * Am.map h.bar := by rw [hA, Matrix.one_mul]
        _ = 0 := by rw [Matrix.mul_assoc, hAc, zero_smul, Matrix.mul_zero]
    rw [e, transpose_zero, Matrix.zero_mul] at hA
    have := congrFun (congrFun hA ⟨0, by omega⟩) ⟨0, by omega⟩
    simp at this
  obtain ⟨hc1, P, Pi, b, s, R, hPPi, hPiP, hb, hs, hbP, hR, hsym, halt⟩ :=
    exists_graph_frame h hp2 (by omega) hA hc0 hAc
  have hdetP : P.det ≠ 0 := by
    intro e
    have := congrArg Matrix.det hPPi
    rw [Matrix.det_mul, e, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hdetPb : (P.map h.bar).det ≠ 0 := by
    have e := RingHom.map_det h.bar P
    rw [RingHom.mapMatrix_apply] at e
    rw [← e]
    exact (map_ne_zero h.bar).2 hdetP
  have hdetR : R.det ≠ 0 := by
    intro e
    have e1 := congrArg Matrix.det hR
    have e2 := RingHom.map_det h.fixedField.subtype R
    rw [RingHom.mapMatrix_apply] at e2
    rw [← e2, e, map_zero, Matrix.det_smul, Matrix.det_mul, det_transpose] at e1
    exact mul_ne_zero (pow_ne_zero _ hs) (mul_ne_zero hdetPb hdetP) e1.symm
  set RG : GL (Fin n) h.fixedField := Matrix.nonsingInvUnit R (isUnit_iff_ne_zero.2 hdetR)
    with hRGdef
  have hRG : (RG : Matrix (Fin n) (Fin n) h.fixedField) = R := rfl
  rcases hc1 with rfl | rfl
  ·
    have hRsym : (RG : Matrix (Fin n) (Fin n) h.fixedField)ᵀ = RG := hsym rfl
    obtain ⟨Q, w, hw, hQ⟩ := Burgoyne.PSL.exists_orth_normal_form hF2 hn RG hRsym
    set Qm := ((Q : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField) with hQm
    set Qim := ((Q⁻¹ : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField)
      with hQim
    have hQQ : Qm * Qim = 1 := by rw [hQm, hQim, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hQQ' : Qim * Qm = 1 := by rw [hQm, hQim, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hone : (1 : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype = 1 :=
      Matrix.map_one _ (map_zero _) (map_one _)
    set P' := P * Qm.map h.fixedField.subtype with hP'
    set Pi' := Qim.map h.fixedField.subtype * Pi with hPi'
    have hPPi' : P' * Pi' = 1 := by
      calc P' * Pi' = P * (Qm * Qim).map h.fixedField.subtype * Pi := by
            rw [Matrix.map_mul]; simp only [hP', hPi', Matrix.mul_assoc]
        _ = 1 := by rw [hQQ, hone, Matrix.mul_one, hPPi]
    have hPiP' : Pi' * P' = 1 := by
      calc Pi' * P' = Qim.map h.fixedField.subtype * (Pi * P) * Qm.map h.fixedField.subtype := by
            simp only [hP', hPi', Matrix.mul_assoc]
        _ = 1 := by rw [hPiP, Matrix.mul_one, ← Matrix.map_mul, hQQ', hone]
    have hbP' : b • (Am * P'.map h.bar) = P' := by
      rw [hP', Matrix.map_mul, map_bar_fmap, ← Matrix.mul_assoc, ← Matrix.smul_mul, hbP]
    have hR' : ((diagGL hw.1 : GL (Fin n) h.fixedField) :
        Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype =
          s • ((P'.map h.bar)ᵀ * P') := by
      rw [Burgoyne.PSL.coe_diagGL, ← hQ, Matrix.map_mul, Matrix.map_mul, hRG, hR, hP',
        Matrix.map_mul, map_bar_fmap, transpose_mul]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, transpose_map]
    by_cases hexc : p ^ f = 3 ∧ n ≤ 4
    · exact ClU.graphOrth_eq_one_three h hexc.1 hn hexc.2 hPPi' hPiP' hb hbP' hs hw hR' hRodd
        hRi hRc
    · exact ClU.graphOrth_eq_one h hp2 hn hinj hPPi' hPiP' hb hbP' hs hw hR' hexc hRodd hRi hRc
  ·
    have hRalt : (RG : Matrix (Fin n) (Fin n) h.fixedField)ᵀ =
        -(RG : Matrix (Fin n) (Fin n) h.fixedField) := halt rfl
    have hev : Even n := by
      have e := congrArg Matrix.det hRalt
      rw [det_transpose, det_neg, Fintype.card_fin, hRG] at e
      by_contra hodd
      rw [Nat.not_even_iff_odd] at hodd
      rw [hodd.neg_one_pow] at e
      have : (2 : h.fixedField) * R.det = 0 := by linear_combination e
      exact hdetR ((mul_eq_zero.1 this).resolve_left h2F)
    have hn4 : 4 ≤ n := by
      obtain ⟨k, hk⟩ := hev
      omega
    exact ClU.graphSymp_eq_one h hp2 hn4 hinj hPPi hPiP hb hbP hs hRalt hR hRodd hRi hRc

end CFSG.ComponentClassification.Foote5.OddLieCore
