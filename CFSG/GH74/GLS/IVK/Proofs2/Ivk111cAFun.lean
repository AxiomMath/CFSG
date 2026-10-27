module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDefs
public import CFSG.GH74.GLS.Stage4.T2SL2Defs
public import Mathlib.RingTheory.PiTensorProduct

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open CFSG.GH74.GLS.Stage4.Hex

section Action

variable {F L : Type} [Field F] [Field L]

theorem funRep_apply (g : SLm F) (f : (Fin 2 → F) → L) (v : Fin 2 → F) :
    funRep F L g f v = f (((g⁻¹ : SLm F) : Matrix (Fin 2) (Fin 2) F).mulVec v) := rfl

theorem inv_mulVec_zero (g : SLm F) (v : Fin 2 → F) :
    (((g⁻¹ : SLm F) : Matrix (Fin 2) (Fin 2) F).mulVec v) 0 =
      (g : Matrix (Fin 2) (Fin 2) F) 1 1 * v 0 - (g : Matrix (Fin 2) (Fin 2) F) 0 1 * v 1 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, sub_eq_add_neg]

theorem inv_mulVec_one (g : SLm F) (v : Fin 2 → F) :
    (((g⁻¹ : SLm F) : Matrix (Fin 2) (Fin 2) F).mulVec v) 1 =
      (g : Matrix (Fin 2) (Fin 2) F) 0 0 * v 1 - (g : Matrix (Fin 2) (Fin 2) F) 1 0 * v 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, sub_eq_add_neg, add_comm]

theorem funRep_sl2U (b : F) (f : (Fin 2 → F) → L) (v : Fin 2 → F) :
    funRep F L (sl2U b) f v = f ![v 0 - b * v 1, v 1] := by
  rw [funRep_apply]
  congr 1
  refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
  · rw [inv_mulVec_zero]; simp
  · rw [inv_mulVec_one]; simp

theorem funRep_sl2W (f : (Fin 2 → F) → L) (v : Fin 2 → F) :
    funRep F L (sl2W F) f v = f ![-v 1, v 0] := by
  rw [funRep_apply]
  congr 1
  refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
  · rw [inv_mulVec_zero]; simp
  · rw [inv_mulVec_one]; simp

theorem funRep_sl2D (t : Fˣ) (f : (Fin 2 → F) → L) (v : Fin 2 → F) :
    funRep F L (sl2D t) f v = f ![((t⁻¹ : Fˣ) : F) * v 0, (t : F) * v 1] := by
  rw [funRep_apply]
  congr 1
  refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
  · rw [inv_mulVec_zero]; simp
  · rw [inv_mulVec_one]; simp

theorem funRep_negOne (f : (Fin 2 → F) → L) (v : Fin 2 → F) :
    funRep F L (T2.negOne F) f v = f (-v) := by
  rw [funRep_apply]
  congr 1
  refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
  · rw [inv_mulVec_zero]; simp
  · rw [inv_mulVec_one]; simp

end Action

section Poly

variable {F L : Type} [Field F] [Field L] [Algebra F L]

@[expose] def IsHomPoly (A : ℕ) (f : (Fin 2 → F) → L) : Prop :=
  ∃ c : ℕ → L, ∀ v : Fin 2 → F, f v = ∑ i ∈ Finset.range (A + 1),
    c i * (algebraMap F L (v 0)) ^ i * (algebraMap F L (v 1)) ^ (A - i)

theorem isHomPoly_lin (a b : F) (A : ℕ) :
    IsHomPoly A (fun v : Fin 2 → F => (algebraMap F L (a * v 0 + b * v 1)) ^ A) := by
  refine ⟨fun m => (algebraMap F L a) ^ m * (algebraMap F L b) ^ (A - m) * (A.choose m : L),
    fun v => ?_⟩
  beta_reduce
  rw [map_add, map_mul, map_mul, add_pow]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_pow, mul_pow]
  ring

theorem funRep_monoFun_x (g : SLm F) (A : ℕ) :
    funRep F L g (monoFun F L A 0) =
      fun v => (algebraMap F L ((g : Matrix (Fin 2) (Fin 2) F) 1 1 * v 0 +
        (-(g : Matrix (Fin 2) (Fin 2) F) 0 1) * v 1)) ^ A := by
  funext v
  rw [funRep_apply]
  simp only [monoFun, inv_mulVec_zero, pow_zero, mul_one]
  congr 2
  ring

theorem isHomPoly_of_mem {A : ℕ} {f : (Fin 2 → F) → L} (hf : f ∈ steinbergSub F L A) :
    IsHomPoly A f := by
  unfold steinbergSub at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    beta_reduce
    rw [funRep_monoFun_x]
    exact isHomPoly_lin _ _ A
  | zero => exact ⟨0, fun v => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨c', hc'⟩ := hy
    exact ⟨c + c', fun v => by simp [hc v, hc' v, add_mul, Finset.sum_add_distrib]⟩
  | smul a x _ hx =>
    obtain ⟨c, hc⟩ := hx
    exact ⟨a • c, fun v => by simp [hc v, Finset.mul_sum, mul_assoc]⟩

end Poly

section Indep

variable {F L : Type} [Field F] [Finite F] [Field L] [Algebra F L]

theorem coeff_eq_zero_of_eval_eq {N : ℕ} (hN : N < Nat.card F) (c : ℕ → L)
    (h : ∀ b : F, ∑ i ∈ Finset.range (N + 1), c i * (algebraMap F L b) ^ i = c 0) :
    ∀ i, 1 ≤ i → i ≤ N → c i = 0 := by
  classical
  have := Fintype.ofFinite F
  set P : Polynomial L := ∑ i ∈ Finset.range (N + 1), Polynomial.C (c i) * Polynomial.X ^ i
    - Polynomial.C (c 0) with hP
  have hPeval : ∀ b : F, P.eval (algebraMap F L b) = 0 := by
    intro b
    simp only [hP, Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [h b, sub_self]
  have hdeg : P.natDegree < Fintype.card F := by
    have h1 : P.natDegree ≤ N := by
      have h3 := Polynomial.natDegree_sub_le_of_le (m := N) (n := 0)
        (p := ∑ i ∈ Finset.range (N + 1), Polynomial.C (c i) * Polynomial.X ^ i)
        (q := Polynomial.C (c 0))
        (Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i hi =>
          (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))))
        (Polynomial.natDegree_C _).le
      simpa [hP] using h3
    rw [← Nat.card_eq_fintype_card]
    omega
  have hP0 : P = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    (algebraMap F L).injective hPeval hdeg
  intro i hi1 hiN
  have h2 := congrArg (fun Q => Polynomial.coeff Q i) hP0
  simp only [hP, Polynomial.coeff_sub, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_zero] at h2
  have hi0 : i ≠ 0 := by omega
  have hmem : i ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hiN)
  simpa [Finset.sum_ite_eq, hmem, hi0] using h2

theorem eq_smul_of_fixed {A : ℕ} (hA : A < Nat.card F) {f : (Fin 2 → F) → L} (hf : IsHomPoly A f)
    (hU : ∀ b : F, funRep F L (sl2U b) f = f) : ∃ c : L, f = c • monoFun F L 0 A := by
  obtain ⟨c, hc⟩ := hf
  have h1 : ∀ b : F, ∑ i ∈ Finset.range (A + 1), c i * (algebraMap F L b) ^ i = c 0 := by
    intro b
    have h2 := congrFun (hU b) ![b, 1]
    rw [funRep_sl2U] at h2
    have h2' : f ![0, 1] = f ![b, 1] := by simpa using h2
    rw [hc, hc] at h2'
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_zero, map_one, one_pow, mul_one] at h2'
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos _)) (fun i _ hi => by
      simp [zero_pow hi])] at h2'
    simpa using h2'.symm
  have h3 := coeff_eq_zero_of_eval_eq hA c h1
  refine ⟨c 0, funext fun v => ?_⟩
  rw [hc v, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos _)) (fun i hi hne => by
    rw [h3 i (Nat.one_le_iff_ne_zero.mpr hne) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
    simp)]
  simp [monoFun]

end Indep

section Special

variable {F L : Type} [Field F] [Field L] [Algebra F L]

theorem funRep_sl2W_x (A : ℕ) :
    funRep F L (sl2W F) (monoFun F L A 0) = (-1 : L) ^ A • monoFun F L 0 A := by
  funext v
  rw [funRep_sl2W]
  simp only [monoFun, Matrix.cons_val_zero, Matrix.cons_val_one, map_neg, pow_zero, mul_one,
    Pi.smul_apply, smul_eq_mul]
  rw [neg_pow, one_mul]

theorem funRep_sl2W_y (A : ℕ) :
    funRep F L (sl2W F) (monoFun F L 0 A) = monoFun F L A 0 := by
  funext v
  rw [funRep_sl2W]
  simp [monoFun]

theorem funRep_sl2U_y (b : F) (A : ℕ) :
    funRep F L (sl2U b) (monoFun F L 0 A) = monoFun F L 0 A := by
  funext v
  rw [funRep_sl2U]
  simp [monoFun]

theorem funRep_sl2D_y (t : Fˣ) (A : ℕ) :
    funRep F L (sl2D t) (monoFun F L 0 A) = (algebraMap F L (t : F)) ^ A • monoFun F L 0 A := by
  funext v
  rw [funRep_sl2D]
  simp [monoFun, mul_pow]

theorem monoFun_x_mem (A : ℕ) : monoFun F L A 0 ∈ steinbergSub F L A := by
  refine Submodule.subset_span ⟨1, ?_⟩
  simp

theorem monoFun_y_mem (A : ℕ) : monoFun F L 0 A ∈ steinbergSub F L A := by
  have h1 : funRep F L (sl2W F) (monoFun F L A 0) ∈ steinbergSub F L A :=
    steinbergSub_stable F L A _ (monoFun_x_mem A)
  rw [funRep_sl2W_x] at h1
  have h2 := Submodule.smul_mem _ ((-1 : L) ^ A) h1
  rwa [smul_smul, ← mul_pow, neg_mul_neg, mul_one, one_pow, one_smul] at h2

theorem monoFun_x_ne_zero (A : ℕ) : monoFun F L A 0 ≠ 0 := by
  intro h
  have := congrFun h ![1, 0]
  simp [monoFun] at this

theorem monoFun_y_ne_zero (A : ℕ) : monoFun F L 0 A ≠ 0 := by
  intro h
  have := congrFun h ![0, 1]
  simp [monoFun] at this

theorem funRep_negOne_of_isHomPoly {A : ℕ} {f : (Fin 2 → F) → L} (hf : IsHomPoly A f) :
    funRep F L (T2.negOne F) f = (-1 : L) ^ A • f := by
  obtain ⟨c, hc⟩ := hf
  funext v
  rw [funRep_negOne, Pi.smul_apply, smul_eq_mul, hc (-v), hc v, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ A := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h1 : (-1 : L) ^ A = (-1) ^ i * (-1) ^ (A - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hi']
  simp only [Pi.neg_apply, map_neg, neg_pow (algebraMap F L (v 0)) i, neg_pow (algebraMap F L (v 1)) (A - i)]
  rw [h1]
  ring

end Special

end CFSG.GH74.GLS.Stage4.Rest
