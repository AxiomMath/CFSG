module

public import CFSG.GH74.Generic.BProg.B2.GenLocU3Good

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.GH74 CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.GH74.Generic.BProg.B2.GenLocU3Blk CFSG.GH74.Generic.BProg.B2.GenLocU3Good
open scoped MatrixGroups

namespace GenLocU3E8Elem

variable {p f : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [CharP F p]

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem prime_eq_seven (h : UnitaryFieldData p f F) (hq : p ^ f = 7) : p = 7 := by
  have h1 : p ∣ 7 := by
    rw [← hq]
    exact dvd_pow_self p (by have := h.one_le; omega)
  exact (Nat.prime_dvd_prime_iff_eq h.prime (by norm_num)).1 h1

omit [Fact p.Prime] [Finite F] in
theorem seven_eq_zero (h : UnitaryFieldData p f F) (hq : p ^ f = 7) : (7 : F) = 0 := by
  have := CharP.cast_eq_zero F p
  rw [prime_eq_seven h hq] at this
  exact_mod_cast this

structure Gauss (h : UnitaryFieldData p f F) where
  i : F
  hi : i * i = -1
  h7 : (7 : F) = 0
  bar_i : h.bar i = -i

omit [Fact p.Prime] in
theorem nonempty_gauss (h : UnitaryFieldData p f F) (hq : p ^ f = 7) : Nonempty (Gauss h) := by
  have := Fintype.ofFinite F
  have hc : Fintype.card F = 49 := by
    rw [← Nat.card_eq_fintype_card, h.card_eq_sq, hq]
    norm_num
  obtain ⟨i, hi⟩ := FiniteField.isSquare_neg_one_iff.2 (by rw [hc]; decide)
  refine ⟨⟨i, hi.symm, seven_eq_zero h hq, ?_⟩⟩
  rw [h.bar_apply, hq]
  have : i ^ 7 = i * (i * i) ^ 3 := by ring
  rw [this, ← hi]
  ring

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem bar_two (h : UnitaryFieldData p f F) : h.bar (2 : F) = 2 := map_ofNat h.bar 2

@[expose] noncomputable def mkSu2 (h : UnitaryFieldData p f F) (M : Matrix (Fin 2) (Fin 2) F)
    (hu : (M.map h.bar)ᵀ * M = 1) (hdet : M.det = 1) : Su F p f 2 :=
  (suEquiv h 2).symm (CFSG.GH74.Generic.S45.Uni.mkSU h M hu hdet)

theorem ym_mkSu2 (h : UnitaryFieldData p f F) (M : Matrix (Fin 2) (Fin 2) F)
    (hu : (M.map h.bar)ᵀ * M = 1) (hdet : M.det = 1) : ym (mkSu2 h M hu hdet) = M := by
  have := coe_suEquiv h 2 ((suEquiv h 2).symm (CFSG.GH74.Generic.S45.Uni.mkSU h M hu hdet))
  rw [MulEquiv.apply_symm_apply] at this
  exact (congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) this).symm.trans
    (CFSG.GH74.Generic.S45.Uni.coe_mkSU h M hu hdet)

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem unitary_mul' {h : UnitaryFieldData p f F} {M N : Matrix (Fin 2) (Fin 2) F}
    (hM : (M.map h.bar)ᵀ * M = 1) (hN : (N.map h.bar)ᵀ * N = 1) :
    ((M * N).map h.bar)ᵀ * (M * N) = 1 := by
  rw [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (M.map h.bar)ᵀ,
    hM, Matrix.one_mul, hN]

namespace Gauss

variable {h : UnitaryFieldData p f F} (D : Gauss h)

@[expose] def tau : F := 2 + 2 * D.i

@[expose] def tauI : F := 2 - 2 * D.i

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem tau_mul_tauI : D.tau * D.tauI = 1 := by
  unfold tau tauI
  linear_combination (-4 : F) * D.hi + D.h7

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem tauI_mul_tau : D.tauI * D.tau = 1 := by
  rw [mul_comm]; exact D.tau_mul_tauI

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem bar_tau : h.bar D.tau = D.tauI := by
  unfold tau tauI
  rw [map_add, map_mul, bar_two, D.bar_i]
  ring

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem bar_tauI : h.bar D.tauI = D.tau := by
  unfold tau tauI
  rw [map_sub, map_mul, bar_two, D.bar_i]
  ring

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem tau_sq : D.tau * D.tau = D.i := by
  unfold tau
  linear_combination (4 : F) * D.hi + D.i * D.h7

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem tau_pow_four : D.tau ^ 4 = -1 := by
  have : D.tau ^ 4 = (D.tau * D.tau) * (D.tau * D.tau) := by ring
  rw [this, D.tau_sq]
  exact D.hi

end Gauss

@[expose] def rMat : Matrix (Fin 2) (Fin 2) F := !![2, 2; -2, 2]

namespace Gauss

variable {h : UnitaryFieldData p f F} (D : Gauss h)

@[expose] def tMat : Matrix (Fin 2) (Fin 2) F := !![D.tau, 0; 0, D.tauI]

@[expose] def dMat2 : Matrix (Fin 2) (Fin 2) F := !![D.tau * D.tau, 0; 0, D.tauI]

@[expose] def dMat1 : Matrix (Fin 2) (Fin 2) F := !![D.tauI, 0; 0, 1]

@[expose] def bMat : Matrix (Fin 2) (Fin 2) F := rMat * D.dMat2 * rMat * D.dMat1

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem rMat_unitary (D : Gauss h) : ((rMat : Matrix (Fin 2) (Fin 2) F).map h.bar)ᵀ * rMat = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [rMat, Matrix.mul_apply, Fin.sum_univ_two, bar_two]
  all_goals linear_combination D.h7

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem rMat_det (D : Gauss h) : (rMat : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  rw [rMat, Matrix.det_fin_two_of]
  linear_combination D.h7

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem tMat_unitary : (D.tMat.map h.bar)ᵀ * D.tMat = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [tMat, Matrix.mul_apply, Fin.sum_univ_two, D.bar_tau, D.bar_tauI, D.tauI_mul_tau,
      D.tau_mul_tauI]

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem tMat_det : D.tMat.det = 1 := by
  rw [tMat, Matrix.det_fin_two_of]
  linear_combination D.tau_mul_tauI

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem dMat2_unitary : (D.dMat2.map h.bar)ᵀ * D.dMat2 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [dMat2, Matrix.mul_apply, Fin.sum_univ_two, D.bar_tau, D.bar_tauI]
  · linear_combination (D.tau * D.tauI + 1) * D.tau_mul_tauI
  · exact D.tau_mul_tauI

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem dMat2_det : D.dMat2.det = D.tau * D.tau * D.tauI := by
  rw [dMat2, Matrix.det_fin_two_of]; ring

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem dMat1_unitary : (D.dMat1.map h.bar)ᵀ * D.dMat1 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [dMat1, Matrix.mul_apply, Fin.sum_univ_two, D.bar_tauI, D.tau_mul_tauI]

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem dMat1_det : D.dMat1.det = D.tauI := by
  rw [dMat1, Matrix.det_fin_two_of]; ring

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem bMat_unitary : (D.bMat.map h.bar)ᵀ * D.bMat = 1 :=
  unitary_mul' (unitary_mul' (unitary_mul' (rMat_unitary D) D.dMat2_unitary) (rMat_unitary D))
    D.dMat1_unitary

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem bMat_det : D.bMat.det = 1 := by
  rw [bMat, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, rMat_det D, D.dMat2_det, D.dMat1_det]
  linear_combination (D.tau * D.tauI + 1) * D.tau_mul_tauI

end Gauss

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem blockMat3_zero (Y : Matrix (Fin 2) (Fin 2) F) :
    blockMat 3 0 Y = !![Y 0 0, Y 0 1, 0; Y 1 0, Y 1 1, 0; 0, 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blockMat_apply]

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem blockMat3_one (Y : Matrix (Fin 2) (Fin 2) F) :
    blockMat 3 1 Y = !![1, 0, 0; 0, Y 0 0, Y 0 1; 0, Y 1 0, Y 1 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blockMat_apply]

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem mul_self_fin_two' (M : Matrix (Fin 2) (Fin 2) F) :
    M * M = (M 0 0 + M 1 1) • M - M.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem pow_succ_of_sq {M : Matrix (Fin 2) (Fin 2) F} (hM : M * M = (2 : F) • M - 1) (n : ℕ) :
    M ^ (n + 1) = ((n + 1 : ℕ) : F) • M - (n : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, sub_mul, smul_mul_assoc, smul_mul_assoc, Matrix.one_mul, hM]
    push_cast
    module

namespace Gauss

variable {h : UnitaryFieldData p f F} (D : Gauss h)

@[expose] noncomputable def tSu : Su F p f 2 := mkSu2 h D.tMat D.tMat_unitary D.tMat_det

@[expose] noncomputable def rSu : Su F p f 2 := mkSu2 h rMat (rMat_unitary D) (rMat_det D)

@[expose] noncomputable def bSu : Su F p f 2 := mkSu2 h D.bMat D.bMat_unitary D.bMat_det

theorem ym_tSu : ym D.tSu = D.tMat := ym_mkSu2 h _ _ _

theorem ym_rSu : ym D.rSu = rMat := ym_mkSu2 h _ _ _

theorem ym_bSu : ym D.bSu = D.bMat := ym_mkSu2 h _ _ _

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem bMat_eq : D.bMat = !![(4 * (D.tau * D.tau) - 4 * D.tauI) * D.tauI,
      4 * (D.tau * D.tau) + 4 * D.tauI;
    (-4 * (D.tau * D.tau) - 4 * D.tauI) * D.tauI, -4 * (D.tau * D.tau) + 4 * D.tauI] := by
  rw [bMat, rMat, dMat2, dMat1]
  simp only [Matrix.mul_fin_two]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val', Fin.zero_eta, Fin.mk_one] <;> ring

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem trace_bMat : D.bMat 0 0 + D.bMat 1 1 = 2 := by
  rw [D.bMat_eq]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val']
  unfold tau tauI
  linear_combination (-32 * D.i - 64) * D.hi + (8 * D.i + 10) * D.h7

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem bMat_sq : D.bMat * D.bMat = (2 : F) • D.bMat - 1 := by
  rw [mul_self_fin_two', D.trace_bMat, D.bMat_det, one_smul]

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem bMat_pow_seven : D.bMat ^ 7 = 1 := by
  have := pow_succ_of_sq D.bMat_sq 6
  rw [show (6 + 1 : ℕ) = 7 from rfl] at this
  rw [this]
  have h7 : ((7 : ℕ) : F) = 0 := by exact_mod_cast D.h7
  rw [h7, zero_smul, zero_sub]
  have h6 : -((6 : ℕ) : F) = 1 := by
    push_cast
    linear_combination -D.h7
  rw [← neg_smul, h6, one_smul]

end Gauss

theorem ym_pow (s : Su F p f 2) (n : ℕ) : ym (s ^ n) = ym s ^ n := by
  simp [ym]

theorem coe_iota0 (y : Su F p f 2) :
    (((blockEmb2 F p f 2 0 y : Su F p f 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![ym y 0 0, ym y 0 1, 0; ym y 1 0, ym y 1 1, 0; 0, 0, 1] := by
  rw [coe_coe_blockEmb2]
  exact blockMat3_zero _

theorem coe_iota1 (y : Su F p f 2) :
    (((blockEmb2 F p f 2 1 y : Su F p f 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, ym y 0 0, ym y 0 1; 0, ym y 1 0, ym y 1 1] := by
  rw [coe_coe_blockEmb2]
  exact blockMat3_one _

namespace Gauss

variable {h : UnitaryFieldData p f F} (D : Gauss h)

omit [Fact p.Prime] [Finite F] [CharP F p] in
include D in
theorem two_ne_zero : (2 : F) ≠ 0 := by
  intro h2
  have : (1 : F) = 0 := by linear_combination D.h7 - 3 * h2
  exact one_ne_zero this

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem bMat_01 : D.bMat 0 1 = 1 + 3 * D.i := by
  rw [D.bMat_eq]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val']
  unfold tau tauI
  linear_combination (16 : F) * D.hi + (3 * D.i + 1) * D.h7

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem one_add_three_i_ne_zero : (1 : F) + 3 * D.i ≠ 0 := by
  intro hz
  have : (1 : F) = 0 := by
    linear_combination 3 * D.h7 - 2 * (9 * D.hi - (3 * D.i - 1) * hz)
  exact one_ne_zero this

theorem bSu_pow_seven : D.bSu ^ 7 = 1 :=
  Subtype.ext (Units.ext (by
    change ym (D.bSu ^ 7) = ym 1
    rw [ym_pow, ym_one, D.ym_bSu, D.bMat_pow_seven]))

theorem bSu_ne_one : D.bSu ≠ 1 := by
  intro hb
  have h1 : D.bMat = 1 := by rw [← D.ym_bSu, hb, ym_one]
  have h2 := congrFun (congrFun h1 0) 1
  rw [D.bMat_01] at h2
  simp at h2
  exact D.one_add_three_i_ne_zero h2

theorem bSu_orderOf : orderOf D.bSu = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime D.bSu_pow_seven D.bSu_ne_one

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem tauI_pow_four : D.tauI ^ 4 = -1 := by
  unfold tauI
  linear_combination (16 * D.i ^ 2 - 64 * D.i + 80) * D.hi + (-9) * D.h7

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem tMat_pow_two : D.tMat ^ 2 = !![D.tau * D.tau, 0; 0, D.tauI * D.tauI] := by
  rw [pow_two, tMat]
  simp only [Matrix.mul_fin_two]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem tMat_pow_four : D.tMat ^ 4 = !![-1, 0; 0, -1] := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, D.tMat_pow_two, pow_two]
  simp only [Matrix.mul_fin_two]
  have h1 : D.tau * D.tau * (D.tau * D.tau) = -1 := by rw [← D.tau_pow_four]; ring
  have h2 : D.tauI * D.tauI * (D.tauI * D.tauI) = -1 := by rw [← D.tauI_pow_four]; ring
  ext a b
  fin_cases a <;> fin_cases b <;> simp [h1, h2]

theorem tSu_pow_four_ne : ¬ D.tSu ^ 2 ^ 2 = 1 := by
  intro hb
  have h1 : D.tMat ^ 4 = 1 := by
    have := congrArg ym hb
    rw [show (2 : ℕ) ^ 2 = 4 from rfl, ym_pow, D.ym_tSu, ym_one] at this
    exact this
  have h2 := congrFun (congrFun h1 0) 0
  rw [D.tMat_pow_four] at h2
  simp at h2
  exact D.two_ne_zero (by linear_combination -h2)

theorem tSu_pow_eight : D.tSu ^ 2 ^ (2 + 1) = 1 :=
  Subtype.ext (Units.ext (by
    change ym (D.tSu ^ 2 ^ (2 + 1)) = ym 1
    rw [show (2 : ℕ) ^ (2 + 1) = 4 * 2 from rfl, ym_pow, pow_mul, D.ym_tSu, D.tMat_pow_four, ym_one,
      pow_two]
    simp only [Matrix.mul_fin_two]
    ext a b
    fin_cases a <;> fin_cases b <;> simp))

theorem tSu_orderOf : orderOf D.tSu = 8 := by
  have := orderOf_eq_prime_pow (x := D.tSu) (p := 2) (n := 2) D.tSu_pow_four_ne D.tSu_pow_eight
  exact this

theorem ym_tSu_inv : ym D.tSu⁻¹ = !![D.tauI, 0; 0, D.tau] := by
  have h1 : D.tMat * !![D.tauI, 0; 0, D.tau] = 1 := by
    rw [tMat]
    simp only [Matrix.mul_fin_two]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [D.tau_mul_tauI, D.tauI_mul_tau]
  calc ym D.tSu⁻¹ = ym D.tSu⁻¹ * (D.tMat * !![D.tauI, 0; 0, D.tau]) := by
        rw [h1, Matrix.mul_one]
    _ = (ym D.tSu⁻¹ * ym D.tSu) * !![D.tauI, 0; 0, D.tau] := by
        rw [D.ym_tSu, Matrix.mul_assoc]
    _ = _ := by rw [ym_inv_mul, Matrix.one_mul]

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem word_matrix : (!![1, 0, 0; 0, 2, 2; 0, -2, 2] * !![1, 0, 0; 0, D.tau, 0; 0, 0, D.tauI] *
      !![D.tauI, 0, 0; 0, D.tau, 0; 0, 0, 1] * !![1, 0, 0; 0, 2, 2; 0, -2, 2] *
      !![D.tau, 0, 0; 0, D.tauI, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) =
    !![1, 0, 0;
      0, (4 * (D.tau * D.tau) - 4 * D.tauI) * D.tauI, 4 * (D.tau * D.tau) + 4 * D.tauI;
      0, (-4 * (D.tau * D.tau) - 4 * D.tauI) * D.tauI, -4 * (D.tau * D.tau) + 4 * D.tauI] := by
  simp only [Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
  all_goals first | ring1 | linear_combination D.tau_mul_tauI

theorem word_eq :
    blockEmb2 F p f 2 1 D.rSu * blockEmb2 F p f 2 1 D.tSu * blockEmb2 F p f 2 0 D.tSu⁻¹ *
      blockEmb2 F p f 2 1 D.rSu * blockEmb2 F p f 2 0 D.tSu = blockEmb2 F p f 2 1 D.bSu := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_iota0, coe_iota1, D.ym_rSu, D.ym_tSu,
    D.ym_tSu_inv, D.ym_bSu, D.bMat_eq, tMat, rMat]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val']
  exact D.word_matrix

end Gauss

end GenLocU3E8Elem

end CFSG.GH74.Generic.BProg.B2
