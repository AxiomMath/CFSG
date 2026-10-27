module

public import CFSG.GH74.Generic.BProg.B3.S45EvenN4Lin
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutGraph
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutNF
public import CFSG.GH74.Generic.S45.LSymFix

public section

namespace CFSG.GH74.Generic.BProg.B3.S45EvenN4Fix

open CFSG CFSG.GH74.Generic.BProg.B3.S45EvenN4Eig CFSG.GH74.Generic.BProg.B3.S45EvenN4Lin CFSG.GH74.Generic.BProg.B2
  CFSG.GH74.Generic.BProg.B2.GenLocL4Ext CFSG.GH74.Generic.BProg.B2.GenLocL4Out
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification Matrix

variable {F : Type} [Field F]

theorem graph_fixed_of_isometry {B : GL (Fin 4) F}
    (hBt : (B : Matrix (Fin 4) (Fin 4) F)ᵀ = B ∨ (B : Matrix (Fin 4) (Fin 4) F)ᵀ = -(B : Matrix (Fin 4) (Fin 4) F))
    {c : Matrix.SpecialLinearGroup (Fin 4) F}
    (hc : (c : Matrix (Fin 4) (Fin 4) F) * B * (c : Matrix (Fin 4) (Fin 4) F)ᵀ = B) :
    (B : Matrix (Fin 4) (Fin 4) F) * ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ *
      ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = c := by
  set cm : Matrix (Fin 4) (Fin 4) F := (c : Matrix (Fin 4) (Fin 4) F) with hcm
  set c' : Matrix (Fin 4) (Fin 4) F :=
    ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hc'
  have h1 : c' * cm = 1 := by
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F))
      (inv_mul_cancel c)
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using this
  have h2 : (B : Matrix (Fin 4) (Fin 4) F) * cmᵀ = c' * B := by
    calc (B : Matrix (Fin 4) (Fin 4) F) * cmᵀ = (c' * cm) * B * cmᵀ := by rw [h1, Matrix.one_mul]
      _ = c' * (cm * B * cmᵀ) := by simp only [Matrix.mul_assoc]
      _ = c' * B := by rw [hc]
  have h3 : cm * (B : Matrix (Fin 4) (Fin 4) F) = B * c'ᵀ := by
    have := congrArg Matrix.transpose h2
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at this
    rcases hBt with hs | hs
    · rw [hs] at this
      exact this
    · rw [hs, Matrix.mul_neg, Matrix.neg_mul] at this
      exact neg_inj.1 this
  calc (B : Matrix (Fin 4) (Fin 4) F) * c'ᵀ * ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
      = cm * B * ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by rw [h3]
    _ = cm := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

@[expose] def dd : Matrix (Fin 4) (Fin 4) F := !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]

theorem dd_det : (dd : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  rw [dd, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero]
  rfl

theorem dd_sq : (dd : Matrix (Fin 4) (Fin 4) F) * dd = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dd, Matrix.mul_apply, Fin.sum_univ_four]

theorem dd_m1 : (dd : Matrix (Fin 4) (Fin 4) F) * m1 * (dd : Matrix (Fin 4) (Fin 4) F)ᵀ = m1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dd, m1, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply]

theorem exists_isometry_skew [Finite F] (hF4 : Nat.card F % 4 = 3) {B : GL (Fin 4) F}
    (hB : (B : Matrix (Fin 4) (Fin 4) F)ᵀ = -(B : Matrix (Fin 4) (Fin 4) F)) :
    ∃ c : Matrix.SpecialLinearGroup (Fin 4) F,
      (c : Matrix (Fin 4) (Fin 4) F) * B * (c : Matrix (Fin 4) (Fin 4) F)ᵀ = B ∧ c ^ 4 = 1 ∧ c ^ 2 ≠ 1 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_card_mod hF4
  have hdet : (B : Matrix (Fin 4) (Fin 4) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).ne_zero
  obtain ⟨P, hP⟩ := exists_cong_skew hF4 (B : Matrix (Fin 4) (Fin 4) F) hB hdet
  let ddSL : Matrix.SpecialLinearGroup (Fin 4) F := ⟨dd, dd_det⟩
  let φ := CatalogueBHigherLinearAction.slConjugation 4 F P
  have hcoe : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      ((φ g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (P : Matrix (Fin 4) (Fin 4) F) * g * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) :=
    fun g => LinearFlag.coe_slConjugation P g
  have hdd4 : ddSL ^ 4 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow]
    show (dd : Matrix (Fin 4) (Fin 4) F) ^ 4 = 1
    calc (dd : Matrix (Fin 4) (Fin 4) F) ^ 4 = dd * dd * (dd * dd) := by
          simp [pow_succ, Matrix.mul_assoc]
      _ = 1 := by rw [dd_sq]; simp
  refine ⟨φ ddSL, ?_, ?_, ?_⟩
  · rw [hcoe]
    set Pi : Matrix (Fin 4) (Fin 4) F := ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hPi
    have hPiP : Pi * (P : Matrix (Fin 4) (Fin 4) F) = 1 := P.inv_mul
    have hPtPit : (P : Matrix (Fin 4) (Fin 4) F)ᵀ * Piᵀ = 1 := by
      rw [← Matrix.transpose_mul, hPiP, Matrix.transpose_one]
    have hdd : ((ddSL : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = dd := rfl
    rw [hdd]
    calc (P : Matrix (Fin 4) (Fin 4) F) * dd * Pi * (B : Matrix (Fin 4) (Fin 4) F) *
          ((P : Matrix (Fin 4) (Fin 4) F) * dd * Pi)ᵀ
        = (P : Matrix (Fin 4) (Fin 4) F) * dd * (Pi * (P : Matrix (Fin 4) (Fin 4) F)) * m1 *
            ((P : Matrix (Fin 4) (Fin 4) F)ᵀ * Piᵀ) * ddᵀ * (P : Matrix (Fin 4) (Fin 4) F)ᵀ := by
          rw [hP]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (P : Matrix (Fin 4) (Fin 4) F) * (dd * m1 * ddᵀ) * (P : Matrix (Fin 4) (Fin 4) F)ᵀ := by
          rw [hPiP, hPtPit]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (P : Matrix (Fin 4) (Fin 4) F) * m1 * (P : Matrix (Fin 4) (Fin 4) F)ᵀ := by rw [dd_m1]
      _ = B := hP.symm
  · rw [← map_pow, hdd4, map_one]
  · intro h
    have h' : ddSL ^ 2 = 1 := φ.injective (by rw [map_pow, h, map_one])
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F)) h'
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at this
    rw [pow_two] at this
    change dd * dd = 1 at this
    rw [dd_sq] at this
    have h0 := congrFun (congrFun this 0) 0
    simp at h0
    apply h2
    linear_combination -h0

theorem exists_fixed_order_four_sl4 [Finite F] (hF4 : Nat.card F % 4 = 3)
    (u : MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) (hu : u * u = 1) :
    ∃ c : Matrix.SpecialLinearGroup (Fin 4) F, u c = c ∧ c ^ 4 = 1 ∧ c ^ 2 ≠ 1 := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_card_mod hF4
  have hu' : ∀ g, u (u g) = g := fun g => by
    simpa using congrArg (fun φ : MulAut (Matrix.SpecialLinearGroup (Fin 4) F) => φ g) hu
  by_cases hin : IsInnerDiag4 u
  · obtain ⟨x, hx⟩ := hin
    set X : Matrix (Fin 4) (Fin 4) F := (x : Matrix (Fin 4) (Fin 4) F) with hXdef
    set Xi : Matrix (Fin 4) (Fin 4) F := ((x⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hXidef
    have hXXi : X * Xi = 1 := x.mul_inv
    have hXiX : Xi * X = 1 := x.inv_mul
    have hcomm : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
        (g : Matrix (Fin 4) (Fin 4) F) * (X * X) = (X * X) * g := fun g => by
      have h1 := hx (u g)
      rw [hu' g, hx g] at h1
      calc (g : Matrix (Fin 4) (Fin 4) F) * (X * X)
          = (X * (X * g * Xi) * Xi) * (X * X) := by rw [← h1]
        _ = X * X * g * (Xi * (Xi * X) * X) := by simp only [Matrix.mul_assoc]
        _ = X * X * g := by rw [hXiX, Matrix.mul_one, hXiX, Matrix.mul_one]
    obtain ⟨l, hl⟩ := exists_scalar_of_commute_sl hcomm
    have hl0 : l ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hl
      have h1 : (1 : Matrix (Fin 4) (Fin 4) F) = 0 := by
        calc (1 : Matrix (Fin 4) (Fin 4) F) = Xi * X := hXiX.symm
          _ = Xi * (Xi * X) * X := by rw [hXiX, Matrix.mul_one, hXiX]
          _ = (Xi * Xi) * (X * X) := by simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hl, Matrix.mul_zero]
      have := congrFun (congrFun h1 0) 0
      simp at this
    have hfix : ∀ a : Matrix.SpecialLinearGroup (Fin 4) F,
        (a : Matrix (Fin 4) (Fin 4) F) * X = X * a → u a = a := fun a ha => by
      apply Subtype.ext
      rw [hx a, ← ha, Matrix.mul_assoc, hXXi, Matrix.mul_one]
    by_cases hsq : IsSquare l
    · obtain ⟨r, hr⟩ := hsq
      have hr0 : r ≠ 0 := fun h => hl0 (by rw [hr, h]; ring)
      set T : Matrix (Fin 4) (Fin 4) F := r⁻¹ • X with hTdef
      have hT : T * T = 1 := by
        rw [hTdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hl, smul_smul, hr]
        have : r⁻¹ * r⁻¹ * (r * r) = 1 := by field_simp
        rw [this, one_smul]
      obtain ⟨a, b, hat, -, ha4, ha2, -, -⟩ := exists_D8_comm h2 hT
      have hrT : r • T = X := by rw [hTdef, smul_smul, mul_inv_cancel₀ hr0, one_smul]
      have haX : (a : Matrix (Fin 4) (Fin 4) F) * X = X * a := by
        have h1 : (a : Matrix (Fin 4) (Fin 4) F) * (r • T) = (r • T) * a := by
          rw [Matrix.mul_smul, Matrix.smul_mul, hat]
        rwa [hrT] at h1
      exact ⟨a, hfix a haX, ha4, ha2⟩
    · obtain ⟨a, ha, ha4, ha2⟩ := exists_order_four_nsq hF4 hsq hl
      exact ⟨a, hfix a ha, ha4, ha2⟩
  · obtain ⟨B, hB, hBt⟩ := exists_graph_form hF4 u hu hin
    have hBdet : IsUnit (B : Matrix (Fin 4) (Fin 4) F).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
    rcases hBt with hs | hs
    · have := Fintype.ofFinite F
      obtain ⟨cm, hdet, hcB, hnsc, hc4⟩ := CFSG.GH74.Generic.S45.exists_isometry_order_four h2 (m := 4)
        (by norm_num) (B : Matrix (Fin 4) (Fin 4) F) hs hBdet
      let c : Matrix.SpecialLinearGroup (Fin 4) F := ⟨cm, hdet⟩
      refine ⟨c, Subtype.ext ?_, ?_, ?_⟩
      · rw [hB c]
        exact graph_fixed_of_isometry (Or.inl hs) hcB
      · apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_pow]
        show cm ^ 4 = 1
        calc cm ^ 4 = cm * cm * (cm * cm) := by simp [pow_succ, Matrix.mul_assoc]
          _ = 1 := hc4
      · intro h
        apply hnsc 1
        have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F)) h
        simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at this
        rw [pow_two] at this
        rw [one_smul]
        exact this
    · obtain ⟨c, hcB, hc4, hc2⟩ := exists_isometry_skew hF4 hs
      exact ⟨c, Subtype.ext (by rw [hB c]; exact graph_fixed_of_isometry (Or.inr hs) hcB), hc4, hc2⟩

end CFSG.GH74.Generic.BProg.B3.S45EvenN4Fix
