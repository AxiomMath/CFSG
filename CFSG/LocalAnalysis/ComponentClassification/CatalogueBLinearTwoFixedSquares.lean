module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PureSemilinear
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PureSemilinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoFixedField

public section

namespace CFSG.ComponentClassification.CatalogueBLinearTwoFixed

noncomputable section

open Matrix CFSG.GorensteinWalter

universe u

theorem odd_square_half (r : ℕ) (hr : Odd r) :
    r ^ 2 / 2 = (r - 1) * ((r + 1) / 2) := by
  have hmod : r ^ 2 % 2 = 1 := Nat.odd_iff.mp hr.pow
  have hdiv : r ^ 2 / 2 = (r ^ 2 - 1) / 2 := by omega
  have hfactor : r ^ 2 - 1 = (r - 1) * (r + 1) := by
    simpa only [pow_two, mul_comm] using Nat.mul_self_sub_mul_self_eq r 1
  rw [hdiv, hfactor, Nat.mul_div_assoc _ hr.add_one.two_dvd]

theorem fixedField_unit_isSquare (K : Type u) [Field K] [Finite K]
    (hodd : ringChar K ≠ 2) (sigma : K ≃+* K) (hsigma : orderOf sigma = 2)
    (a : (fixedField K sigma)ˣ) :
    IsSquare (Units.map (fixedField K sigma).subtype a : Kˣ) := by
  let : Fintype K := Fintype.ofFinite K
  let : Fintype (fixedField K sigma) := Fintype.ofFinite (fixedField K sigma)
  have hchar : ringChar (fixedField K sigma) ≠ 2 := by
    rw [Algebra.ringChar_eq (fixedField K sigma) K]
    exact hodd
  have hr : Odd (Nat.card (fixedField K sigma)) := by
    apply Nat.odd_iff.mpr
    simpa only [Nat.card_eq_fintype_card] using FiniteField.odd_card_of_char_ne_two hchar
  have hpow : a ^ (Nat.card (fixedField K sigma) - 1) = 1 := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, Nat.card_eq_fintype_card] using
      FiniteField.pow_card_sub_one_eq_one (a : fixedField K sigma) a.ne_zero
  apply (FiniteField.unit_isSquare_iff hodd _).mpr
  rw [← Nat.card_eq_fintype_card, card_eq_fixedField_card_sq K sigma hsigma,
    odd_square_half _ hr, pow_mul, ← map_pow, hpow, map_one, one_pow]

theorem fixed_coefficient_isSquare (K : Type u) [Field K] [Finite K]
    (hodd : ringChar K ≠ 2) (sigma : K ≃+* K) (hsigma : orderOf sigma = 2)
    (a : K) (ha : a ≠ 0) (hfixed : sigma a = a) : IsSquare a := by
  let aF : fixedField K sigma := ⟨a, (mem_fixedField_iff K sigma a).mpr hfixed⟩
  have hne : aF ≠ 0 := by
    intro h
    exact ha (congrArg Subtype.val h)
  obtain ⟨b, hb⟩ := fixedField_unit_isSquare K hodd sigma hsigma (Units.mk0 aF hne)
  exact ⟨(b : K), congrArg Units.val hb⟩

theorem fixedField_GL_det_isSquare (K : Type u) [Field K] [Finite K]
    (hodd : ringChar K ≠ 2) (sigma : K ≃+* K) (hsigma : orderOf sigma = 2)
    (A : GL (Fin 2) (fixedField K sigma)) :
    IsSquare (Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map (fixedField K sigma).subtype A) : Kˣ) := by
  rw [Matrix.GeneralLinearGroup.map_det]
  exact fixedField_unit_isSquare K hodd sigma hsigma A.det

theorem square_det_projectivity_mem_PSL (K : Type u) [Field K]
    (A : GL (Fin 2) K) (hdet : IsSquare A.det) :
    Matrix.ProjGenLinGroup.mk A ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  obtain ⟨d, hd⟩ := hdet
  exact pgl2_mk_mem_toPGL_range_of_det_isSquare A
    ⟨(d : K), congrArg Units.val hd⟩

theorem fixedField_projectivity_mem_PSL (K : Type u) [Field K] [Finite K]
    (hodd : ringChar K ≠ 2) (sigma : K ≃+* K) (hsigma : orderOf sigma = 2)
    (A : GL (Fin 2) (fixedField K sigma)) :
    Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (fixedField K sigma).subtype A) ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  exact square_det_projectivity_mem_PSL K _
    (fixedField_GL_det_isSquare K hodd sigma hsigma A)

end

end CFSG.ComponentClassification.CatalogueBLinearTwoFixed
