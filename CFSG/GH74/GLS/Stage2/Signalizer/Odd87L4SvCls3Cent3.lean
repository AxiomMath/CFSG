module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvCls3Frame
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups commutatorElement

section Elements

variable {F : Type} [Field F]

@[expose] def l4SgnA : SL(4, F) :=
  ⟨Matrix.diagonal ![-1, 1, -1, 1], by simp [Matrix.det_diagonal, Fin.prod_univ_four]⟩

@[expose] def l4SwapB : SL(4, F) :=
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1], by
    rw [Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero]
    have h : Fin.succAbove (1 : Fin 4) (2 : Fin 3) = 3 := by decide
    simp [h]⟩

@[expose] def l4Y : SL(4, F) :=
  ⟨Matrix.diagonal ![-1, -1, 1, 1], by simp [Matrix.det_diagonal, Fin.prod_univ_four]⟩

theorem coe_l4SgnA :
    ((l4SgnA : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![-1, 1, -1, 1] := rfl

theorem coe_l4SwapB : ((l4SwapB : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1] := rfl

theorem coe_l4Y :
    ((l4Y : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![-1, -1, 1, 1] := rfl

theorem l4_comm_sgnA_swapB :
    ⁅(l4SgnA : SL(4, F)), (l4SwapB : SL(4, F))⁆ = (l4Y : SL(4, F)) := by
  have h : (l4SgnA : SL(4, F)) * (l4SwapB : SL(4, F)) =
      (l4Y : SL(4, F)) * (l4SwapB : SL(4, F)) * (l4SgnA : SL(4, F)) := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_l4SgnA, coe_l4SwapB, coe_l4Y]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.diagonal_apply]
  rw [commutatorElement_def, h]
  group

theorem l4_sgnA_cong (d : Fin 4 → F) :
    ((l4SgnA : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)ᵀ * Matrix.diagonal d *
      ((l4SgnA : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal d := by
  rw [coe_l4SgnA, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp

theorem l4_swapB_cong (d : Fin 4 → F) (hd01 : d 0 = d 1) :
    ((l4SwapB : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)ᵀ * Matrix.diagonal d *
      ((l4SwapB : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal d := by
  rw [coe_l4SwapB]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply, hd01]

end Elements


section Blocks

variable {F : Type} [Field F]

@[expose] def l4Blk (P Q : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![P 0 0, P 0 1, 0, 0; P 1 0, P 1 1, 0, 0; 0, 0, Q 0 0, Q 0 1; 0, 0, Q 1 0, Q 1 1]

theorem l4Blk_mul (P Q P' Q' : Matrix (Fin 2) (Fin 2) F) :
    l4Blk P Q * l4Blk P' Q' = l4Blk (P * P') (Q * Q') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [l4Blk, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem l4Blk_one : l4Blk (1 : Matrix (Fin 2) (Fin 2) F) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l4Blk]

theorem l4Blk_pow (P Q : Matrix (Fin 2) (Fin 2) F) (k : ℕ) :
    (l4Blk P Q) ^ k = l4Blk (P ^ k) (Q ^ k) := by
  induction k with
  | zero => simp [l4Blk_one]
  | succ k ih => rw [pow_succ, ih, l4Blk_mul, ← pow_succ, ← pow_succ]

theorem l4Blk_inj {P Q P' Q' : Matrix (Fin 2) (Fin 2) F} (h : l4Blk P Q = l4Blk P' Q') :
    P = P' ∧ Q = Q' := by
  have e : ∀ i j, l4Blk P Q i j = l4Blk P' Q' i j := fun i j => by rw [h]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  have e22 := e 2 2
  have e23 := e 2 3
  have e32 := e 3 2
  have e33 := e 3 3
  simp [l4Blk] at e00 e01 e10 e11 e22 e23 e32 e33
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simpa using ‹_›
  · ext i j
    fin_cases i <;> fin_cases j <;> simpa using ‹_›

end Blocks


section Main

variable {F : Type} [Field F] [Finite F]

theorem l4_two_by_two_pow_eq_one (hF : Nat.card F = 3) {r n : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    {P : Matrix (Fin 2) (Fin 2) F} (hP : P ^ (r ^ n) = 1) : P = 1 := by
  have : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card, hF]
  have hunit : IsUnit P := IsUnit.of_pow_eq_one hP (pow_ne_zero n hr.ne_zero)
  let Pu : GL (Fin 2) F := hunit.unit
  have hpow : Pu ^ (r ^ n) = 1 := Units.ext (by simpa [Pu] using hP)
  have hcard : Nat.card (GL (Fin 2) F) = 48 := by
    rw [Matrix.card_GL_field, hq]
    decide
  have hord1 : orderOf Pu ∣ r ^ n := orderOf_dvd_of_pow_eq_one hpow
  have hord2 : orderOf Pu ∣ 48 := hcard ▸ orderOf_dvd_natCard Pu
  have hcop : Nat.Coprime (r ^ n) 48 := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd hr]
    intro h
    have h48 : r ∣ 2 ^ 4 * 3 := by norm_num; exact h
    rcases (Nat.Prime.dvd_mul hr).1 h48 with h1 | h1
    · have := Nat.le_of_dvd (by norm_num) (hr.dvd_of_dvd_pow h1)
      omega
    · have := Nat.le_of_dvd (by norm_num) h1
      omega
  have h1 : orderOf Pu = 1 := by
    have := Nat.dvd_gcd hord1 hord2
    rw [hcop.gcd_eq_one] at this
    exact Nat.dvd_one.1 this
  have h2 : Pu = 1 := orderOf_eq_one_iff.1 h1
  have h3 := congrArg Units.val h2
  simpa [Pu] using h3

theorem l4_cls3_cent3_std (hF : Nat.card F = 3) {D : GL (Fin 4) F} {d : Fin 4 → F}
    (hd : ∀ i, d i ≠ 0) (hd01 : d 0 = d 1)
    (hD : ((D⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal d)
    (x : SL(4, F)) (hx : ∃ r n : ℕ, r.Prime ∧ 5 ≤ r ∧ x ^ (r ^ n) = 1)
    (h : ∀ a b : SL(4, F), proj 4 F a ∈ fixSub (conjAut 4 F D * dualAut 4 F) →
      proj 4 F b ∈ fixSub (conjAut 4 F D * dualAut 4 F) → x * ⁅a, b⁆ = ⁅a, b⁆ * x) :
    x ∈ scalars 4 F := by
  classical
  have _ := hd
  obtain ⟨r, n, hr, hr5, hxn⟩ := hx
  have hodd : Odd (Nat.card F) := by rw [hF]; decide
  have h2 : (2 : F) ≠ 0 := l4_two_ne_zero_of_odd hodd
  have hfixA : proj 4 F l4SgnA ∈ fixSub (conjAut 4 F D * dualAut 4 F) :=
    mem_fixSub.2 (conjAut_dualAut_proj_of_transpose_mul_mul D l4SgnA
      (by rw [hD]; exact l4_sgnA_cong d))
  have hfixB : proj 4 F l4SwapB ∈ fixSub (conjAut 4 F D * dualAut 4 F) :=
    mem_fixSub.2 (conjAut_dualAut_proj_of_transpose_mul_mul D l4SwapB
      (by rw [hD]; exact l4_swapB_cong d hd01))
  have hxy := h _ _ hfixA hfixB
  rw [l4_comm_sgnA_swapB] at hxy
  have hxy' : (x : Matrix (Fin 4) (Fin 4) F) * Matrix.diagonal ![-1, -1, 1, 1] =
      Matrix.diagonal ![-1, -1, 1, 1] * (x : Matrix (Fin 4) (Fin 4) F) := by
    have := congrArg (fun z : SL(4, F) => (z : Matrix (Fin 4) (Fin 4) F)) hxy
    simpa [Matrix.SpecialLinearGroup.coe_mul, coe_l4Y] using this
  have hne : (-1 : F) ≠ 1 := fun h' => h2 (by linear_combination -h')
  have hz : ∀ u v : Fin 4, (![-1, -1, 1, 1] : Fin 4 → F) u ≠ (![-1, -1, 1, 1] : Fin 4 → F) v →
      (x : Matrix (Fin 4) (Fin 4) F) u v = 0 := by
    intro u v huv
    have h1 := congrFun (congrFun hxy' u) v
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    have h3 : (x : Matrix (Fin 4) (Fin 4) F) u v *
        ((![-1, -1, 1, 1] : Fin 4 → F) v - (![-1, -1, 1, 1] : Fin 4 → F) u) = 0 := by
      linear_combination h1
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact h4
    · exact absurd (by linear_combination -h4) huv
  have e02 := hz 0 2 (by simpa using hne)
  have e03 := hz 0 3 (by simpa using hne)
  have e12 := hz 1 2 (by simpa using hne)
  have e13 := hz 1 3 (by simpa using hne)
  have e20 := hz 2 0 (by simpa using hne.symm)
  have e21 := hz 2 1 (by simpa using hne.symm)
  have e30 := hz 3 0 (by simpa using hne.symm)
  have e31 := hz 3 1 (by simpa using hne.symm)
  set P : Matrix (Fin 2) (Fin 2) F := !![(x : Matrix (Fin 4) (Fin 4) F) 0 0, (x : Matrix (Fin 4) (Fin 4) F) 0 1;
    (x : Matrix (Fin 4) (Fin 4) F) 1 0, (x : Matrix (Fin 4) (Fin 4) F) 1 1] with hP
  set Q : Matrix (Fin 2) (Fin 2) F := !![(x : Matrix (Fin 4) (Fin 4) F) 2 2, (x : Matrix (Fin 4) (Fin 4) F) 2 3;
    (x : Matrix (Fin 4) (Fin 4) F) 3 2, (x : Matrix (Fin 4) (Fin 4) F) 3 3] with hQ
  have hblk : (x : Matrix (Fin 4) (Fin 4) F) = l4Blk P Q := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [l4Blk, P, Q, e02, e03, e12, e13, e20, e21, e30, e31]
  have hpow : (l4Blk P Q) ^ (r ^ n) = 1 := by
    rw [← hblk, ← Matrix.SpecialLinearGroup.coe_pow, hxn, Matrix.SpecialLinearGroup.coe_one]
  rw [l4Blk_pow, ← l4Blk_one] at hpow
  obtain ⟨hP', hQ'⟩ := l4Blk_inj hpow
  have hP1 := l4_two_by_two_pow_eq_one hF hr hr5 hP'
  have hQ1 := l4_two_by_two_pow_eq_one hF hr hr5 hQ'
  have hx1 : x = 1 := Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    rw [hblk, hP1, hQ1, l4Blk_one, Matrix.SpecialLinearGroup.coe_one]
  rw [hx1]
  exact Subgroup.one_mem _

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
