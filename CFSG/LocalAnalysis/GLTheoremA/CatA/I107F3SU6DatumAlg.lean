module

public import CFSG.GH74.KGroups.FieldGF
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LocalAnalysis.GLTheoremA.U6Herm

open CFSG.GH74.KGroups Matrix

class CjField (F : Type) [Field F] : Prop where
  two : (2 : F) = 0
  pow_four : ∀ x : F, x ^ 4 = x

namespace CjField

variable {F : Type} [Field F] [CjField F]

theorem two_eq_zero : (2 : F) = 0 := CjField.two

theorem add_self (x : F) : x + x = 0 := by
  rw [← two_mul, two_eq_zero, zero_mul]

theorem add_sq (x y : F) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  linear_combination (x * y) * (two_eq_zero (F := F))

theorem sq_sq (x : F) : (x ^ 2) ^ 2 = x := by
  rw [← pow_mul]; exact CjField.pow_four x

@[expose] def sqHom (F : Type) [Field F] [CjField F] : F →+* F where
  toFun x := x ^ 2
  map_one' := one_pow 2
  map_mul' x y := mul_pow x y 2
  map_zero' := zero_pow two_ne_zero
  map_add' := add_sq

end CjField

@[expose] def conjT {F : Type} [Field F] {m n : Type} (M : Matrix m n F) : Matrix n m F :=
  (M.map (· ^ 2))ᵀ

theorem conjT_apply {F : Type} [Field F] {m n : Type} (M : Matrix m n F) (i : n) (j : m) :
    conjT M i j = M j i ^ 2 := rfl

@[expose] def IsSU {F : Type} [Field F] (M : Matrix (Fin 6) (Fin 6) F) : Prop :=
  M.det = 1 ∧ conjT M * M = 1

section Conj

variable {F : Type} [Field F] [CjField F] {l m n : Type}

theorem conjT_eq (M : Matrix m n F) : conjT M = (M.map (CjField.sqHom F))ᵀ := rfl

@[expose] def conjTAdd (F : Type) [Field F] [CjField F] (m n : Type) :
    Matrix m n F →+ Matrix n m F where
  toFun := conjT
  map_zero' := by ext i j; simp [conjT_apply]
  map_add' M N := by ext i j; simp [conjT_apply, CjField.add_sq]

theorem conjT_add (M N : Matrix m n F) : conjT (M + N) = conjT M + conjT N :=
  map_add (conjTAdd F m n) M N

theorem conjT_zero : conjT (0 : Matrix m n F) = 0 := map_zero (conjTAdd F m n)

theorem conjT_neg (M : Matrix m n F) : conjT (-M) = -conjT M := map_neg (conjTAdd F m n) M

theorem conjT_mul [Fintype m] (M : Matrix l m F) (N : Matrix m n F) :
    conjT (M * N) = conjT N * conjT M := by
  rw [conjT_eq, conjT_eq, conjT_eq, Matrix.map_mul, Matrix.transpose_mul]

theorem conjT_conjT (M : Matrix m n F) : conjT (conjT M) = M := by
  ext i j; simp [conjT_apply, CjField.sq_sq]

theorem conjT_one [DecidableEq n] : conjT (1 : Matrix n n F) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [conjT_apply]
  · simp [conjT_apply, Matrix.one_apply, h, Ne.symm h]

theorem matrix_add_self (X : Matrix m n F) : X + X = 0 := by
  ext i j; simp [CjField.add_self]

theorem conjT_conj_herm [Fintype m] {X : Matrix m m F} (hX : conjT X = X) (A : Matrix l m F) :
    conjT (A * X * conjT A) = A * X * conjT A := by
  rw [conjT_mul, conjT_mul, conjT_conjT, hX, Matrix.mul_assoc]

end Conj

structure Hyp (F : Type) [Field F] where
  U : Matrix (Fin 6) (Fin 3) F
  W : Matrix (Fin 6) (Fin 3) F
  UU : conjT U * U = 0
  WW : conjT W * W = 0
  UW : conjT U * W = 1
  WU : conjT W * U = 1
  sumId : U * conjT W + W * conjT U = 1

namespace Hyp

section Defs

variable {F : Type} [Field F] (H : Hyp F)

@[expose] def B (X : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 6) (Fin 6) F :=
  1 + H.U * X * conjT H.U

@[expose] def L (A A' : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 6) (Fin 6) F :=
  H.U * A * conjT H.W + H.W * A' * conjT H.U

end Defs

section Lemmas

variable {F : Type} [Field F] [CjField F] (H : Hyp F)

theorem UU_mul {k : Type} (Z : Matrix (Fin 3) k F) : conjT H.U * (H.U * Z) = 0 := by
  rw [← Matrix.mul_assoc, H.UU, Matrix.zero_mul]

theorem WW_mul {k : Type} (Z : Matrix (Fin 3) k F) : conjT H.W * (H.W * Z) = 0 := by
  rw [← Matrix.mul_assoc, H.WW, Matrix.zero_mul]

theorem UW_mul {k : Type} (Z : Matrix (Fin 3) k F) : conjT H.U * (H.W * Z) = Z := by
  rw [← Matrix.mul_assoc, H.UW, Matrix.one_mul]

theorem WU_mul {k : Type} (Z : Matrix (Fin 3) k F) : conjT H.W * (H.U * Z) = Z := by
  rw [← Matrix.mul_assoc, H.WU, Matrix.one_mul]

theorem B_mul (X Y : Matrix (Fin 3) (Fin 3) F) : H.B X * H.B Y = H.B (X + Y) := by
  simp only [B, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
    H.UU_mul, Matrix.mul_zero, add_zero]
  abel

theorem B_zero : H.B 0 = 1 := by simp [B]

theorem conjT_B (X : Matrix (Fin 3) (Fin 3) F) : conjT (H.B X) = H.B (conjT X) := by
  simp only [B, conjT_add, conjT_one, conjT_mul, conjT_conjT, Matrix.mul_assoc]

theorem B_unit {X : Matrix (Fin 3) (Fin 3) F} (hX : conjT X = X) :
    conjT (H.B X) * H.B X = 1 := by
  rw [conjT_B, hX, B_mul, matrix_add_self, B_zero]

theorem det_B (X : Matrix (Fin 3) (Fin 3) F) : (H.B X).det = 1 := by
  unfold B
  rw [Matrix.det_one_add_mul_comm, H.UU_mul]
  simp

theorem B_isSU {X : Matrix (Fin 3) (Fin 3) F} (hX : conjT X = X) : IsSU (H.B X) :=
  ⟨H.det_B X, H.B_unit hX⟩

theorem L_mul_U (A A' : Matrix (Fin 3) (Fin 3) F) : H.L A A' * H.U = H.U * A := by
  simp only [L, Matrix.add_mul, Matrix.mul_assoc, H.WU, H.UU, Matrix.mul_one, Matrix.mul_zero,
    add_zero]

theorem conjTU_mul_L (A A' : Matrix (Fin 3) (Fin 3) F) :
    conjT H.U * H.L A A' = A' * conjT H.U := by
  simp only [L, Matrix.mul_add, ← Matrix.mul_assoc, H.UU, H.UW, Matrix.zero_mul, Matrix.one_mul,
    zero_add]

theorem L_mul_B {A A' : Matrix (Fin 3) (Fin 3) F} (hA : conjT A * A' = 1)
    (X : Matrix (Fin 3) (Fin 3) F) :
    H.L A A' * H.B X = H.B (A * X * conjT A) * H.L A A' := by
  have hA_mul : ∀ {k : Type} (Z : Matrix (Fin 3) k F), conjT A * (A' * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hA, Matrix.one_mul]
  have h1 : H.L A A' * H.B X = H.L A A' + H.U * A * X * conjT H.U := by
    simp only [B, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, H.L_mul_U]
  have h2 : H.B (A * X * conjT A) * H.L A A' = H.L A A' + H.U * A * X * conjT H.U := by
    simp only [B, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, H.conjTU_mul_L, hA_mul]
  rw [h1, h2]

theorem conjT_L (A A' : Matrix (Fin 3) (Fin 3) F) :
    conjT (H.L A A') = H.W * conjT A * conjT H.U + H.U * conjT A' * conjT H.W := by
  simp only [L, conjT_add, conjT_mul, conjT_conjT, Matrix.mul_assoc]

theorem conjT_L_mul_L {A A' : Matrix (Fin 3) (Fin 3) F} (hA : conjT A * A' = 1) :
    conjT (H.L A A') * H.L A A' = 1 := by
  have hA' : conjT A' * A = 1 := by
    have := congrArg conjT hA
    rwa [conjT_mul, conjT_conjT, conjT_one] at this
  have hA_mul : ∀ {k : Type} (Z : Matrix (Fin 3) k F), conjT A * (A' * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hA, Matrix.one_mul]
  have hA'_mul : ∀ {k : Type} (Z : Matrix (Fin 3) k F), conjT A' * (A * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hA', Matrix.one_mul]
  rw [conjT_L]
  simp only [L, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, H.UU_mul, H.WW_mul, H.UW_mul,
    H.WU_mul, hA_mul, hA'_mul, Matrix.mul_zero, add_zero, zero_add]
  exact H.sumId

theorem det_L (A A' : Matrix (Fin 3) (Fin 3) F) : (H.L A A').det = A.det * A'.det := by
  let e : Fin 6 ≃ Fin 3 ⊕ Fin 3 := (finSumFinEquiv (m := 3) (n := 3)).symm
  let P : Matrix (Fin 6) (Fin 6) F := (fromCols H.U H.W).submatrix id e
  let D : Matrix (Fin 6) (Fin 6) F := (fromBlocks A 0 0 A').submatrix e e
  let Q : Matrix (Fin 6) (Fin 6) F := (fromRows (conjT H.W) (conjT H.U)).submatrix e id
  have hPDQ : P * D * Q = H.L A A' := by
    simp only [P, D, Q, submatrix_mul_equiv, fromCols_mul_fromBlocks, Matrix.mul_zero,
      add_zero, zero_add, fromCols_mul_fromRows, Matrix.submatrix_id_id]
    rfl
  have hPQ : P * Q = 1 := by
    simp only [P, Q, submatrix_mul_equiv, fromCols_mul_fromRows, Matrix.submatrix_id_id]
    exact H.sumId
  rw [← hPDQ, Matrix.det_mul, Matrix.det_mul]
  have h1 : P.det * Q.det = 1 := by rw [← Matrix.det_mul, hPQ, Matrix.det_one]
  have h2 : D.det = A.det * A'.det := by
    simp only [D, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  calc P.det * D.det * Q.det = (P.det * Q.det) * D.det := by ring
    _ = A.det * A'.det := by rw [h1, one_mul, h2]

theorem L_isSU {A A' : Matrix (Fin 3) (Fin 3) F} (hA : conjT A * A' = 1) (h1 : A.det = 1)
    (h2 : A'.det = 1) : IsSU (H.L A A') :=
  ⟨by rw [H.det_L, h1, h2, one_mul], H.conjT_L_mul_L hA⟩

theorem eq_zero_of_B_eq_smul {Y : Matrix (Fin 3) (Fin 3) F} {u : F}
    (h : H.B Y = u • (1 : Matrix (Fin 6) (Fin 6) F)) : Y = 0 := by
  have hne : ∃ i j, conjT H.U i j ≠ 0 := by
    by_contra hcon
    have h0 : conjT H.U = 0 := by
      ext i j
      by_contra h
      exact hcon ⟨i, j, h⟩
    have h1 := H.UW
    rw [h0, Matrix.zero_mul] at h1
    have := congrFun (congrFun h1 0) 0
    simp at this
  have h1 : conjT H.U * H.B Y = conjT H.U := by
    simp only [B, Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc, H.UU_mul, add_zero]
  have h2 : conjT H.U = u • conjT H.U := by
    have h1' := h1
    rw [h, Matrix.mul_smul, Matrix.mul_one] at h1'
    exact h1'.symm
  have hu : u = 1 := by
    obtain ⟨i, j, hij⟩ := hne
    have := congrFun (congrFun h2 i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_eq_self₀.mp this.symm |>.resolve_right hij
  subst hu
  rw [one_smul] at h
  have h3 : H.U * Y * conjT H.U = 0 := by
    unfold B at h
    simpa using h
  have h4 : Y = conjT H.W * (H.U * Y * conjT H.U) * H.W := by
    simp only [Matrix.mul_assoc, H.WU_mul, H.UW, Matrix.mul_one]
  rw [h4, h3, Matrix.mul_zero, Matrix.zero_mul]

end Lemmas

end Hyp

@[expose] def gw : GF4 := ⟨2⟩

@[expose] def gv : GF4 := ⟨3⟩

@[expose] def uM : Matrix (Fin 6) (Fin 3) GF4 :=
  !![1, 0, 0; 1, 0, 0; 0, 1, 0; 0, 1, 0; 0, 0, 1; 0, 0, 1]

@[expose] def wM : Matrix (Fin 6) (Fin 3) GF4 :=
  !![gw, 0, 0; gv, 0, 0; 0, gw, 0; 0, gv, 0; 0, 0, gw; 0, 0, gv]

theorem uu4 : conjT uM * uM = 0 := by decide +kernel

theorem ww4 : conjT wM * wM = 0 := by decide +kernel

theorem uw4 : conjT uM * wM = 1 := by decide +kernel

theorem wu4 : conjT wM * uM = 1 := by decide +kernel

theorem sum4 : uM * conjT wM + wM * conjT uM = 1 := by decide +kernel

@[expose] def A4 : Fin 3 → Matrix (Fin 3) (Fin 3) GF4
  | 0 => !![gw, 0, 0; 0, gv, 0; 0, 0, 1]
  | 1 => !![0, 0, 1; 1, 0, 0; 0, 1, 0]
  | 2 => !![1, 1, 0; 0, 1, 0; 0, 0, 1]

@[expose] def A4' : Fin 3 → Matrix (Fin 3) (Fin 3) GF4
  | 0 => !![gw, 0, 0; 0, gv, 0; 0, 0, 1]
  | 1 => !![0, 0, 1; 1, 0, 0; 0, 1, 0]
  | 2 => !![1, 0, 0; 1, 1, 0; 0, 0, 1]

@[expose] def H4 : Fin 9 → Matrix (Fin 3) (Fin 3) GF4
  | 0 => !![1, 0, 0; 0, 0, 0; 0, 0, 0]
  | 1 => !![0, 0, 0; 0, 1, 0; 0, 0, 0]
  | 2 => !![0, 0, 0; 0, 0, 0; 0, 0, 1]
  | 3 => !![0, 1, 0; 1, 0, 0; 0, 0, 0]
  | 4 => !![0, gw, 0; gv, 0, 0; 0, 0, 0]
  | 5 => !![0, 0, 1; 0, 0, 0; 1, 0, 0]
  | 6 => !![0, 0, gw; 0, 0, 0; gv, 0, 0]
  | 7 => !![0, 0, 0; 0, 0, 1; 0, 1, 0]
  | 8 => !![0, 0, 0; 0, 0, gw; 0, gv, 0]

theorem herm4 : ∀ i, conjT (H4 i) = H4 i := by decide +kernel

theorem unit4 : ∀ j, conjT (A4 j) * A4' j = 1 := by decide +kernel

theorem det4 : ∀ j, (A4 j).det = 1 ∧ (A4' j).det = 1 := by
  intro j
  simp only [Matrix.det_fin_three]
  revert j
  decide +kernel

theorem indep4 : ∀ c : Fin 9 → ZMod 2, ∑ k, (c k).val • H4 k = 0 → c = 0 := by
  decide +kernel

theorem cjField_of_equiv {F : Type} [Field F] (ψ : GF4 ≃+* F) : CjField F where
  two := by
    have h2 : (2 : GF4) = 0 := by decide
    have := congrArg ψ h2
    rwa [map_ofNat, map_zero] at this
  pow_four x := by
    obtain ⟨y, rfl⟩ := ψ.surjective x
    rw [← map_pow]
    congr 1
    revert y
    decide +kernel

section Transport

variable {F : Type} [Field F] (ψ : GF4 ≃+* F) {l m n : Type}

@[expose] def emb (M : Matrix m n GF4) : Matrix m n F := M.map ψ.toRingHom

theorem emb_mul [Fintype m] (M : Matrix l m GF4) (N : Matrix m n GF4) :
    emb ψ (M * N) = emb ψ M * emb ψ N := Matrix.map_mul

theorem emb_add (M N : Matrix m n GF4) : emb ψ (M + N) = emb ψ M + emb ψ N := by
  ext i j; simp [emb]

theorem emb_zero : emb ψ (0 : Matrix m n GF4) = 0 := by ext i j; simp [emb]

theorem emb_one [DecidableEq n] : emb ψ (1 : Matrix n n GF4) = 1 := by
  ext i j; by_cases h : i = j <;> simp [emb, h, Matrix.one_apply]

theorem emb_nsmul (k : ℕ) (M : Matrix m n GF4) : emb ψ (k • M) = k • emb ψ M := by
  ext i j; simp [emb]

theorem emb_sum {ι : Type} (s : Finset ι) (f : ι → Matrix m n GF4) :
    emb ψ (∑ i ∈ s, f i) = ∑ i ∈ s, emb ψ (f i) := by
  ext a b; simp [emb, Matrix.sum_apply]

theorem emb_injective : Function.Injective (emb ψ : Matrix m n GF4 → Matrix m n F) := by
  intro M N h
  ext i j
  exact ψ.injective (congrFun (congrFun h i) j)

theorem conjT_emb (M : Matrix m n GF4) : conjT (emb ψ M) = emb ψ (conjT M) := by
  ext i j; simp [emb, conjT_apply]

theorem det_emb (M : Matrix (Fin 3) (Fin 3) GF4) : (emb ψ M).det = ψ M.det :=
  (RingHom.map_det ψ.toRingHom M).symm

@[expose] def hyp : Hyp F where
  U := emb ψ uM
  W := emb ψ wM
  UU := by rw [conjT_emb, ← emb_mul, uu4, emb_zero]
  WW := by rw [conjT_emb, ← emb_mul, ww4, emb_zero]
  UW := by rw [conjT_emb, ← emb_mul, uw4, emb_one]
  WU := by rw [conjT_emb, ← emb_mul, wu4, emb_one]
  sumId := by rw [conjT_emb, conjT_emb, ← emb_mul, ← emb_mul, ← emb_add, sum4, emb_one]

@[expose] def hermB (i : Fin 9) : Matrix (Fin 3) (Fin 3) F := emb ψ (H4 i)

@[expose] def actA (j : Fin 3) : Matrix (Fin 3) (Fin 3) F := emb ψ (A4 j)

@[expose] def actA' (j : Fin 3) : Matrix (Fin 3) (Fin 3) F := emb ψ (A4' j)

theorem conjT_hermB (i : Fin 9) : conjT (hermB ψ i) = hermB ψ i := by
  rw [hermB, conjT_emb, herm4]

theorem conjT_actA_mul (j : Fin 3) : conjT (actA ψ j) * actA' ψ j = 1 := by
  rw [actA, actA', conjT_emb, ← emb_mul, unit4, emb_one]

theorem det_actA (j : Fin 3) : (actA ψ j).det = 1 := by
  rw [actA, det_emb, (det4 j).1, map_one]

theorem det_actA' (j : Fin 3) : (actA' ψ j).det = 1 := by
  rw [actA', det_emb, (det4 j).2, map_one]

theorem act_identity (tab : Fin 3 → Fin 9 → Fin 9 → ℕ)
    (h : ∀ (j : Fin 3) (i : Fin 9),
      A4 j * H4 i * conjT (A4 j) = ∑ k : Fin 9, tab j k i • H4 k) (j : Fin 3) (i : Fin 9) :
    actA ψ j * hermB ψ i * conjT (actA ψ j) = ∑ k : Fin 9, tab j k i • hermB ψ k := by
  have := congrArg (emb ψ) (h j i)
  rwa [emb_mul, emb_mul, ← conjT_emb, emb_sum, Finset.sum_congr rfl fun k _ => emb_nsmul ψ _ _]
    at this

theorem hermB_indep (c : Fin 9 → ZMod 2) (h : ∑ k, (c k).val • hermB ψ k = 0) : c = 0 := by
  refine indep4 c (emb_injective ψ ?_)
  rw [emb_sum, emb_zero]
  rw [← h]
  exact Finset.sum_congr rfl fun k _ => emb_nsmul ψ _ _

end Transport

end CFSG.LocalAnalysis.GLTheoremA.U6Herm
