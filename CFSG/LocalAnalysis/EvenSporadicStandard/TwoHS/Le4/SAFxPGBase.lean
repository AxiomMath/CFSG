module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxDef

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Matrix

@[expose] def soGramInv5 : SoMat5 :=
  !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 3]

theorem soGramInv_mul : soGramInv5 * soGram5 = 1 := by decide

@[expose] def IsSO5 (A : SoMat5) : Prop := Aᵀ * soGram5 * A = soGram5 ∧ A.det = 1

instance (A : SoMat5) : Decidable (IsSO5 A) := by unfold IsSO5; infer_instance

@[expose] def mkPG (A : SoMat5) (h : IsSO5 A) : PGSp45 := by
  refine ⟨⟨A, soGramInv5 * Aᵀ * soGram5, ?_, ?_⟩, h⟩
  · have h1 : (soGramInv5 * Aᵀ * soGram5) * A = 1 := by
      calc (soGramInv5 * Aᵀ * soGram5) * A = soGramInv5 * (Aᵀ * soGram5 * A) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h.1, soGramInv_mul]
    exact mul_eq_one_comm.1 h1
  · calc (soGramInv5 * Aᵀ * soGram5) * A = soGramInv5 * (Aᵀ * soGram5 * A) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h.1, soGramInv_mul]

@[simp] theorem mkPG_val (A : SoMat5) (h : IsSO5 A) :
    ((mkPG A h : PGSp45) : GL (Fin 5) (ZMod 5)).1 = A := rfl

theorem pg_ext {x y : PGSp45} (h : x.1.1 = y.1.1) : x = y :=
  Subtype.ext (Units.ext h)

@[simp] theorem pg_mul_val (x y : PGSp45) : (x * y).1.1 = x.1.1 * y.1.1 := rfl

@[simp] theorem pg_one_val : (1 : PGSp45).1.1 = 1 := rfl

theorem mkPG_self (x : PGSp45) : mkPG x.1.1 x.2 = x := pg_ext rfl

abbrev FM : Type := Array ℕ

@[expose] def toM (a : FM) : SoMat5 :=
  Matrix.of fun i j => ((a.getD (5 * i.val + j.val) 0 : ℕ) : ZMod 5)

@[expose] def fmEntry (a b : FM) (i j : ℕ) : ℕ :=
  (a.getD (5 * i) 0 * b.getD j 0 + a.getD (5 * i + 1) 0 * b.getD (5 + j) 0 +
    a.getD (5 * i + 2) 0 * b.getD (10 + j) 0 + a.getD (5 * i + 3) 0 * b.getD (15 + j) 0 +
    a.getD (5 * i + 4) 0 * b.getD (20 + j) 0) % 5

@[expose] def fmMul (a b : FM) : FM :=
  Array.ofFn (n := 25) fun p => fmEntry a b (p.val / 5) (p.val % 5)

@[expose] def fmOne : FM :=
  #[1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]

@[expose] def fmPow (a : FM) : ℕ → FM
  | 0 => fmOne
  | n + 1 => fmMul a (fmPow a n)

@[expose] def fmTr (a : FM) : ℕ :=
  (a.getD 0 0 + a.getD 6 0 + a.getD 12 0 + a.getD 18 0 + a.getD 24 0) % 5

@[expose] def fmOk (a : FM) : Prop := a.size = 25 ∧ ∀ i < 25, a.getD i 0 < 5

instance (a : FM) : Decidable (fmOk a) := by unfold fmOk; infer_instance

theorem fmMul_getD (a b : FM) {p : ℕ} (hp : p < 25) :
    (fmMul a b).getD p 0 = fmEntry a b (p / 5) (p % 5) := by
  simp [fmMul, Array.getD_eq_getD_getElem?, hp]

theorem toM_fmMul (a b : FM) : toM (fmMul a b) = toM a * toM b := by
  ext i j
  have h : 5 * i.val + j.val < 25 := by omega
  have e1 : (5 * i.val + j.val) / 5 = i.val := by omega
  have e2 : (5 * i.val + j.val) % 5 = j.val := by omega
  simp only [toM, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_five, fmMul_getD _ _ h, e1, e2,
    fmEntry]
  rw [ZMod.natCast_mod]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num

theorem toM_fmOne : toM fmOne = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toM, fmOne]

theorem toM_fmPow (a : FM) (n : ℕ) : toM (fmPow a n) = toM a ^ n := by
  induction n with
  | zero => exact toM_fmOne
  | succ n ih => rw [fmPow, toM_fmMul, ih, pow_succ']

theorem fmOk_fmOne : fmOk fmOne := by decide

theorem fmOk_fmMul {a b : FM} (_ : fmOk a) (_ : fmOk b) : fmOk (fmMul a b) := by
  refine ⟨by simp [fmMul], fun i hi => ?_⟩
  rw [fmMul_getD _ _ hi, fmEntry]
  exact Nat.mod_lt _ (by norm_num)

theorem fmOk_fmPow {a : FM} (ha : fmOk a) (n : ℕ) : fmOk (fmPow a n) := by
  induction n with
  | zero => exact fmOk_fmOne
  | succ n ih => exact fmOk_fmMul ha ih

theorem toM_inj {a b : FM} (ha : fmOk a) (hb : fmOk b) (h : toM a = toM b) : a = b := by
  apply Array.ext (by rw [ha.1, hb.1])
  intro i hi _
  have hi25 : i < 25 := by rw [← ha.1]; exact hi
  have := congrFun (congrFun h ⟨i / 5, by omega⟩) ⟨i % 5, by omega⟩
  simp only [toM, Matrix.of_apply] at this
  have e : 5 * (i / 5) + i % 5 = i := by omega
  rw [e] at this
  have h2 := (ZMod.natCast_eq_natCast_iff' _ _ 5).1 this
  rw [Nat.mod_eq_of_lt (ha.2 i hi25), Nat.mod_eq_of_lt (hb.2 i hi25)] at h2
  simpa [Array.getD_eq_getD_getElem?, hi25, ha.1, hb.1, hi] using h2

theorem trace_toM (a : FM) : (toM a).trace = ((fmTr a : ℕ) : ZMod 5) := by
  simp only [Matrix.trace, Matrix.diag, toM, Matrix.of_apply, Fin.sum_univ_five, fmTr]
  rw [ZMod.natCast_mod]
  push_cast
  simp

abbrev OmegaPts : Type := {v : Fin 5 → ZMod 5 // v ⬝ᵥ (soGram5 *ᵥ v) = 4}

theorem omega_smul_mem (g : PGSp45) (v : Fin 5 → ZMod 5) (hv : v ⬝ᵥ (soGram5 *ᵥ v) = 4) :
    (g.1.1 *ᵥ v) ⬝ᵥ (soGram5 *ᵥ (g.1.1 *ᵥ v)) = 4 := by
  have hG : g.1.1ᵀ * soGram5 * g.1.1 = soGram5 := g.2.1
  have h1 : (g.1.1 *ᵥ v) ⬝ᵥ (soGram5 *ᵥ (g.1.1 *ᵥ v)) =
      v ⬝ᵥ ((g.1.1ᵀ * soGram5 * g.1.1) *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      Matrix.mulVec_mulVec, dotProduct_comm]
    simp only [Matrix.mul_assoc]
  rw [h1, hG]; exact hv

instance : MulAction PGSp45 OmegaPts where
  smul g v := ⟨g.1.1 *ᵥ v.1, omega_smul_mem g v.1 v.2⟩
  one_smul v := Subtype.ext (by
    show ((1 : PGSp45).1.1 : SoMat5) *ᵥ v.1 = v.1
    simp)
  mul_smul g h v := Subtype.ext (by
    show (g * h).1.1 *ᵥ v.1 = g.1.1 *ᵥ (h.1.1 *ᵥ v.1)
    simp [Matrix.mulVec_mulVec])

@[expose] def chiPG : PGSp45 →* ℤˣ :=
  Equiv.Perm.sign.comp (MulAction.toPermHom PGSp45 OmegaPts)

theorem chiPG_of_sq (g : PGSp45) (hg : g * g = 1) :
    chiPG g = (-1) ^ ((Fintype.card OmegaPts -
      Fintype.card (Function.fixedPoints (MulAction.toPermHom PGSp45 OmegaPts g))) / 2) := by
  unfold chiPG
  simp only [MonoidHom.comp_apply]
  apply Equiv.Perm.sign_of_pow_two_eq_one
  rw [← map_pow, pow_two, hg, map_one]

theorem chiPG_conj (c g : PGSp45) : chiPG (c * g * c⁻¹) = chiPG g := by
  rw [map_mul, map_mul, map_inv, mul_comm (chiPG c) (chiPG g), mul_assoc, mul_inv_cancel, mul_one]

theorem pg_trace_conj (c g : PGSp45) : ((c * g * c⁻¹).1.1).trace = g.1.1.trace := by
  have := Matrix.trace_units_conj c.1 g.1.1
  simpa using this

end CFSG.EvenSporadicStandard.TwoHS
