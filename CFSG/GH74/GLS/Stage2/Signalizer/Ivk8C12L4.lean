module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12Four
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Gen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def l4aM : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]

@[expose] def l4wM : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

@[expose] def l4dMat (g : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![g 0 0, g 0 1, 0, 0; g 1 0, g 1 1, 0, 0; 0, 0, g 0 0, g 0 1; 0, 0, g 1 0, g 1 1]

theorem det_l4aM : (l4aM : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  simp [l4aM, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem det_l4wM : (l4wM : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  simp [l4wM, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem det_l4dMat (g : Matrix (Fin 2) (Fin 2) F) : (l4dMat g).det = g.det ^ 2 := by
  simp [l4dMat, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

@[expose] def l4a : SL(4, F) := ⟨l4aM, det_l4aM⟩
@[expose] def l4w : SL(4, F) := ⟨l4wM, det_l4wM⟩

theorem l4dMat_mul (g h : Matrix (Fin 2) (Fin 2) F) : l4dMat (g * h) = l4dMat g * l4dMat h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [l4dMat, Matrix.mul_apply, Fin.sum_univ_succ]

theorem l4dMat_one : l4dMat (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l4dMat]

@[expose] def l4d : SL(2, F) →* SL(4, F) where
  toFun g := ⟨l4dMat (g : Matrix (Fin 2) (Fin 2) F), by rw [det_l4dMat, g.2]; simp⟩
  map_one' := Subtype.ext (by simp [l4dMat_one])
  map_mul' g h := Subtype.ext (by
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    exact l4dMat_mul _ _)

theorem coe_l4d (g : SL(2, F)) :
    (l4d g : Matrix (Fin 4) (Fin 4) F) = l4dMat (g : Matrix _ _ F) := rfl
theorem coe_l4a : ((l4a : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = l4aM := rfl
theorem coe_l4w : ((l4w : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = l4wM := rfl

theorem l4aM_mul_self : (l4aM : Matrix (Fin 4) (Fin 4) F) * l4aM = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l4aM, Matrix.mul_apply, Fin.sum_univ_succ]

theorem l4wM_mul_self : (l4wM : Matrix (Fin 4) (Fin 4) F) * l4wM = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l4wM, Matrix.mul_apply, Fin.sum_univ_succ]

theorem l4dMat_mul_l4aM (g : Matrix (Fin 2) (Fin 2) F) :
    l4dMat g * l4aM = l4aM * l4dMat g := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l4dMat, l4aM, Matrix.mul_apply, Fin.sum_univ_succ]

theorem l4dMat_mul_l4wM (g : Matrix (Fin 2) (Fin 2) F) :
    l4dMat g * l4wM = l4wM * l4dMat g := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l4dMat, l4wM, Matrix.mul_apply, Fin.sum_univ_succ]

theorem l4a_mul_self : (l4a : SL(4, F)) * l4a = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_l4a, Matrix.SpecialLinearGroup.coe_one]
  exact l4aM_mul_self

theorem l4w_mul_self : (l4w : SL(4, F)) * l4w = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_l4w, Matrix.SpecialLinearGroup.coe_one]
  exact l4wM_mul_self

theorem l4d_mul_l4a (g : SL(2, F)) : l4d g * l4a = l4a * l4d g := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_l4a, coe_l4d]
  exact l4dMat_mul_l4aM _

theorem l4d_mul_l4w (g : SL(2, F)) : l4d g * l4w = l4w * l4d g := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_l4w, coe_l4d]
  exact l4dMat_mul_l4wM _

theorem l4a_notMem_scalars (h2 : (2 : F) ≠ 0) : (l4a : SL(4, F)) ∉ scalars 4 F := by
  rintro ⟨c, -, hc⟩
  have h00 := congrFun (congrFun hc 0) 0
  have h22 := congrFun (congrFun hc 2) 2
  simp [coe_l4a, l4aM, Matrix.scalar_apply] at h00 h22
  apply h2
  linear_combination h00 - h22

theorem l4w_notMem_scalars : (l4w : SL(4, F)) ∉ scalars 4 F := by
  rintro ⟨c, -, hc⟩
  have h02 := congrFun (congrFun hc 0) 2
  simp [coe_l4w, l4wM, Matrix.scalar_apply] at h02

theorem l4wa_notMem_scalars : (l4w * l4a : SL(4, F)) ∉ scalars 4 F := by
  rintro ⟨c, -, hc⟩
  have h02 := congrFun (congrFun hc 0) 2
  simp [Matrix.SpecialLinearGroup.coe_mul, coe_l4a, coe_l4w, l4aM, l4wM, Matrix.mul_apply,
    Fin.sum_univ_succ, Matrix.scalar_apply] at h02

theorem l4_comm : (l4a * l4w : SL(4, F))⁻¹ * (l4w * l4a) ∈ scalars 4 F := by
  refine ⟨-1, by norm_num, ?_⟩
  have hai : (l4a : SL(4, F))⁻¹ = l4a := inv_eq_of_mul_eq_one_right l4a_mul_self
  have hwi : (l4w : SL(4, F))⁻¹ = l4w := inv_eq_of_mul_eq_one_right l4w_mul_self
  rw [_root_.mul_inv_rev, hai, hwi]
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_l4a, coe_l4w, l4aM, l4wM, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.scalar_apply]

theorem l4d_mem_scalars {g : SL(2, F)} (h : (l4d g : SL(4, F)) ∈ scalars 4 F) :
    g ∈ Subgroup.center SL(2, F) := by
  obtain ⟨c, -, hc⟩ := h
  have h00 := congrFun (congrFun hc 0) 0
  have h01 := congrFun (congrFun hc 0) 1
  have h10 := congrFun (congrFun hc 1) 0
  have h11 := congrFun (congrFun hc 1) 1
  simp [coe_l4d, l4dMat, Matrix.scalar_apply] at h00 h01 h10 h11
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨c, ?_, ?_⟩
  · have hdet := g.2
    rw [Matrix.det_fin_two, h00, h01, h10, h11] at hdet
    simpa [Fintype.card_fin, pow_two] using (by linear_combination hdet : (c : F) ^ 2 = 1)
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]


@[expose] def FL43 (Y : Type) [Group Y] : Prop := CFSG.Blueprint.LieModel Y .PSL 4 3 1

theorem cellAbs_L4 (hsurv : CellAbs FL43) : CellAbs FL4 := by
  intro A _ _ zb Sb Vb J hfr hJ hnc hF
  obtain ⟨p, f, hp, hf, hp2, hq8, hL⟩ := hF
  by_cases hq3 : p ^ f = 3
  · have hp3 : p = 3 := by
      have : p ∣ 3 := hq3 ▸ dvd_pow_self p (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this
    subst hp3
    have hf1 : f = 1 := by
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (show 3 ^ f = 3 ^ 1 by rw [hq3, pow_one])
    subst hf1
    exact hsurv A zb Sb Vb J hfr hJ hnc hL
  · exfalso
    obtain ⟨F, hFfield, hFfin, hcard, ⟨e⟩⟩ :=
      LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
    have hnk : ¬ KindFactorAll Kind.ly (↥J ⧸ center ↥J) :=
      not_kindFactorAll_fl4 hp hp2 hf hL Kind.ly
    obtain ⟨hZ, -, -⟩ := hfr.reduce hJ hnk
    let eJ : (↥J ⧸ center ↥J) ≃* ↥J :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    let ι : projectiveSL 4 F →* A := J.subtype.comp (e.symm.trans eJ).toMonoidHom
    have hι : Function.Injective ι :=
      (Subgroup.subtype_injective _).comp (e.symm.trans eJ).injective
    have : Fact p.Prime := ⟨hp⟩
    have : CharP F p := by
      have := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
    have hK2 : ringChar F ≠ 2 := by rwa [ringChar.eq F p]
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hK2
    have hFodd : Odd (Nat.card F) := by
      rw [hcard]
      exact (hp.odd_of_ne_two hp2).pow
    have h5 : 5 ≤ Nat.card F := by
      rw [hcard]
      have h3 : 3 ≤ p ^ f := by
        have h2' : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
        have := Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow : Odd (p ^ f))
        omega
      have hodd' := Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow : Odd (p ^ f))
      omega
    refine false_of_four hfr ι hι hFodd h5 (x := proj 4 F l4a) (y := proj 4 F l4w) ?_ ?_ ?_ ?_ ?_ ?_
      ((proj 4 F).comp l4d) ?_ ?_ ?_
    · rw [← map_mul, l4a_mul_self, map_one]
    · rw [← map_mul, l4w_mul_self, map_one]
    · exact fun h => l4a_notMem_scalars h2 (proj_eq_one_iff.1 h)
    · exact fun h => l4w_notMem_scalars (proj_eq_one_iff.1 h)
    · intro h
      have h1 := proj_eq_proj_iff.1 h
      have hwi : (l4w : SL(4, F))⁻¹ = l4w := inv_eq_of_mul_eq_one_right l4w_mul_self
      rw [hwi] at h1
      exact l4wa_notMem_scalars h1
    · rw [← map_mul, ← map_mul]
      exact proj_eq_proj_iff.2 l4_comm
    · intro g hg
      exact l4d_mem_scalars (proj_eq_one_iff.1 hg)
    · intro g
      show proj 4 F (l4d g) * proj 4 F l4a = proj 4 F l4a * proj 4 F (l4d g)
      rw [← map_mul, ← map_mul, l4d_mul_l4a]
    · intro g
      show proj 4 F (l4d g) * proj 4 F l4w = proj 4 F l4w * proj 4 F (l4d g)
      rw [← map_mul, ← map_mul, l4d_mul_l4w]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
