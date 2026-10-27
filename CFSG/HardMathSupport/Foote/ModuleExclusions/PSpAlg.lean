module

public import CFSG.Open.StatedDefs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

open Matrix CFSG.Open

variable {n : ℕ} {K : Type} [Field K]

abbrev sJ (n : ℕ) (K : Type) [Field K] : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.fromBlocks 0 1 (-1) 0

theorem sJ_mul_self : sJ n K * sJ n K = -1 := by
  simp [sJ, Matrix.fromBlocks_multiply]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp

theorem sJ_transpose : (sJ n K)ᵀ = -sJ n K := by
  simp [sJ, Matrix.fromBlocks_transpose]
  rw [Matrix.fromBlocks_neg]
  simp

abbrev sLam (a : Fin n ⊕ Fin n → K) : Fin n ⊕ Fin n → K := a ᵥ* sJ n K

theorem sJ_mulVec (a : Fin n ⊕ Fin n → K) : sJ n K *ᵥ a = -sLam a := by
  have h : sLam a = (sJ n K)ᵀ *ᵥ a := (Matrix.mulVec_transpose _ _).symm
  rw [h, sJ_transpose, Matrix.neg_mulVec, neg_neg]

theorem sLam_sLam (a : Fin n ⊕ Fin n → K) : sLam (sLam a) = -a := by
  show a ᵥ* sJ n K ᵥ* sJ n K = -a
  rw [Matrix.vecMul_vecMul, sJ_mul_self, Matrix.vecMul_neg, Matrix.vecMul_one]

theorem sLam_eq_zero {a : Fin n ⊕ Fin n → K} (h : sLam a = 0) : a = 0 := by
  have := sLam_sLam a
  rw [h] at this
  have h0 : sLam (0 : Fin n ⊕ Fin n → K) = 0 := by simp [sLam]
  rw [h0] at this
  exact neg_eq_zero.mp this.symm

theorem exists_sLam_ne {a : Fin n ⊕ Fin n → K} (ha : a ≠ 0) :
    ∃ x : Fin n ⊕ Fin n → K, sLam a ⬝ᵥ x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply ha
  apply sLam_eq_zero
  funext i
  have := hcon (Pi.single i 1)
  simpa [dotProduct_single] using this

theorem sLam_dot_swap (x y : Fin n ⊕ Fin n → K) : sLam x ⬝ᵥ y = -(sLam y ⬝ᵥ x) := by
  have h1 : sLam x ⬝ᵥ y = x ⬝ᵥ (sJ n K *ᵥ y) := (Matrix.dotProduct_mulVec _ _ _).symm
  rw [h1, sJ_mulVec, dotProduct_neg, dotProduct_comm]

theorem sLam_dot_self (h2 : (2 : K) ≠ 0) (x : Fin n ⊕ Fin n → K) : sLam x ⬝ᵥ x = 0 := by
  have h := sLam_dot_swap x x
  have : (2 : K) * (sLam x ⬝ᵥ x) = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left h2

theorem sLam_add (x y : Fin n ⊕ Fin n → K) : sLam (x + y) = sLam x + sLam y :=
  Matrix.add_vecMul _ _ _

theorem sLam_smul (t : K) (x : Fin n ⊕ Fin n → K) : sLam (t • x) = t • sLam x :=
  Matrix.smul_vecMul _ _ _

theorem symp_of_mem_statedSp {A : GL (Fin n ⊕ Fin n) K} (hA : A ∈ StatedSp n K) :
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * sJ n K *
      (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = sJ n K := by
  induction hA using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => simp
  | mul x y _ _ hx hy =>
    rw [Units.val_mul, Matrix.transpose_mul]
    calc (↑y)ᵀ * (↑x)ᵀ * sJ n K * (↑x * ↑y) = (↑y)ᵀ * ((↑x)ᵀ * sJ n K * ↑x) * ↑y := by
          simp only [Matrix.mul_assoc]
      _ = sJ n K := by rw [hx, hy]
  | inv x _ hx =>
    set B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
      ((x⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) with hB
    have h1 : (↑x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * B = 1 := Units.mul_inv x
    calc Bᵀ * sJ n K * B
        = Bᵀ * ((↑x)ᵀ * sJ n K * ↑x) * B := by rw [hx]
      _ = ((↑x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * B)ᵀ * sJ n K *
            (↑x * B) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = sJ n K := by rw [h1]; simp

theorem mem_statedSp_of_symp {A : GL (Fin n ⊕ Fin n) K}
    (h : (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * sJ n K *
      (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = sJ n K) : A ∈ StatedSp n K :=
  Subgroup.subset_closure h

theorem sDot_mulVec_left (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (y w : Fin n ⊕ Fin n → K) : (M *ᵥ y) ⬝ᵥ w = y ⬝ᵥ (Mᵀ *ᵥ w) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

theorem sLam_symp {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} (hM : Mᵀ * sJ n K * M = sJ n K)
    (y z : Fin n ⊕ Fin n → K) : sLam (M *ᵥ y) ⬝ᵥ (M *ᵥ z) = sLam y ⬝ᵥ z := by
  have e1 : sLam (M *ᵥ y) ⬝ᵥ (M *ᵥ z) = (M *ᵥ y) ⬝ᵥ (sJ n K *ᵥ (M *ᵥ z)) :=
    (Matrix.dotProduct_mulVec _ _ _).symm
  rw [e1, sDot_mulVec_left, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM,
    ← Matrix.dotProduct_mulVec]

theorem sLam_vecMul_eigen {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hM : Mᵀ * sJ n K * M = sJ n K) {c ε : K} (hMM : M * M = c • 1)
    {a : Fin n ⊕ Fin n → K} (hMa : M *ᵥ a = ε • a) : sLam a ᵥ* M = (ε * c) • sLam a := by
  have key : ∀ x : Fin n ⊕ Fin n → K, (sLam a ᵥ* M) ⬝ᵥ x = ((ε * c) • sLam a) ⬝ᵥ x := by
    intro x
    have h1 : (sLam a ᵥ* M) ⬝ᵥ x = sLam a ⬝ᵥ (M *ᵥ x) := (Matrix.dotProduct_mulVec _ _ _).symm
    have h2 : sLam a ⬝ᵥ (M *ᵥ x) = sLam (M *ᵥ a) ⬝ᵥ (M *ᵥ (M *ᵥ x)) :=
      (sLam_symp hM a (M *ᵥ x)).symm
    have h3 : M *ᵥ (M *ᵥ x) = c • x := by
      rw [Matrix.mulVec_mulVec, hMM, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [h1, h2, h3, hMa, dotProduct_smul, sLam_smul, smul_dotProduct, smul_eq_mul,
      smul_dotProduct, smul_eq_mul]
    simp only [smul_eq_mul]
    ring
  funext i
  have := key (Pi.single i 1)
  simpa [dotProduct_single] using this

theorem sLam_eigen_zero {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hM : Mᵀ * sJ n K * M = sJ n K) {ε ε' : K} {a b : Fin n ⊕ Fin n → K} (ha : M *ᵥ a = ε • a)
    (hb : M *ᵥ b = ε' • b) (h : ε * ε' ≠ 1) : sLam a ⬝ᵥ b = 0 := by
  have h1 := sLam_symp hM a b
  rw [ha, hb, sLam_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h1
  have h3 : (ε * ε' - 1) * (sLam a ⬝ᵥ b) = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr h)

abbrev sS (u v : Fin n ⊕ Fin n → K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  vecMulVec u (sLam v) + vecMulVec v (sLam u)

theorem sS_add_right (u v w : Fin n ⊕ Fin n → K) : sS u (v + w) = sS u v + sS u w := by
  simp only [sS, sLam_add, vecMulVec_add, add_vecMulVec]
  abel

theorem sS_smul_right (t : K) (u v : Fin n ⊕ Fin n → K) : sS u (t • v) = t • sS u v := by
  simp only [sS, sLam_smul, vecMulVec_smul, smul_vecMulVec, smul_add]

theorem sS_mulVec (u v x : Fin n ⊕ Fin n → K) :
    sS u v *ᵥ x = (sLam v ⬝ᵥ x) • u + (sLam u ⬝ᵥ x) • v := by
  simp [sS, Matrix.add_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]

theorem sS_symp (h2 : (2 : K) ≠ 0) (u v : Fin n ⊕ Fin n → K) (huv : sLam u ⬝ᵥ v = 0) (t : K) :
    (1 + t • sS u v)ᵀ * sJ n K * (1 + t • sS u v) = sJ n K := by
  set N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := sS u v with hN
  have hvu : sLam v ⬝ᵥ u = 0 := by rw [sLam_dot_swap, huv, neg_zero]
  have hNJ : Nᵀ * sJ n K = vecMulVec (sLam v) (sLam u) + vecMulVec (sLam u) (sLam v) := by
    simp only [hN, sS, Matrix.transpose_add, Matrix.transpose_vecMulVec, Matrix.add_mul,
      Matrix.vecMulVec_mul]
  have hJN : sJ n K * N = -(vecMulVec (sLam u) (sLam v) + vecMulVec (sLam v) (sLam u)) := by
    simp only [hN, sS, Matrix.mul_add, Matrix.mul_vecMulVec, sJ_mulVec, Matrix.neg_vecMulVec]
    abel
  have hsum : Nᵀ * sJ n K + sJ n K * N = 0 := by
    rw [hNJ, hJN]
    abel
  have hNN : Nᵀ * sJ n K * N = 0 := by
    rw [hNJ]
    simp only [hN, sS, Matrix.add_mul, Matrix.mul_add, Matrix.vecMulVec_mul_vecMulVec,
      sLam_dot_self h2, huv, hvu, zero_smul]
    simp
  have e1 : (1 + t • N)ᵀ * sJ n K * (1 + t • N) =
      sJ n K + t • (Nᵀ * sJ n K + sJ n K * N) + (t * t) • (Nᵀ * sJ n K * N) := by
    simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_add,
      smul_smul]
    abel
  rw [e1, hsum, hNN]
  simp

theorem sS_mul_sS (h2 : (2 : K) ≠ 0) (u w w' : Fin n ⊕ Fin n → K) (h1 : sLam w ⬝ᵥ u = 0)
    (h2' : sLam u ⬝ᵥ w' = 0) (h3 : sLam w ⬝ᵥ w' = 0) : sS u w * sS u w' = 0 := by
  simp only [sS, Matrix.mul_add, Matrix.add_mul, Matrix.vecMulVec_mul_vecMulVec, h1, h2', h3,
    sLam_dot_self h2, zero_smul]
  simp

theorem eq_zero_of_sS (h2 : (2 : K) ≠ 0) {u w : Fin n ⊕ Fin n → K} (hu : u ≠ 0)
    (h : sS u w = 0) : w = 0 := by
  obtain ⟨y, hy⟩ := exists_sLam_ne hu
  set z : Fin n ⊕ Fin n → K := (sLam u ⬝ᵥ y)⁻¹ • y with hz
  have hz1 : sLam u ⬝ᵥ z = 1 := by
    rw [hz, dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hy]
  have hx : ∀ x, (sLam w ⬝ᵥ x) • u + (sLam u ⬝ᵥ x) • w = 0 := fun x => by
    have := congrArg (fun N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K => N *ᵥ x) h
    simpa [sS_mulVec] using this
  have hw : w = (-(sLam w ⬝ᵥ z)) • u := by
    have := hx z
    rw [hz1, one_smul] at this
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_right this
  set κ : K := -(sLam w ⬝ᵥ z) with hκ
  have h1 : sLam w ⬝ᵥ z = κ := by
    rw [hw, sLam_smul, smul_dotProduct, hz1, smul_eq_mul, mul_one]
  have h3 : κ = -κ := by linear_combination hκ - h1
  have h4 : κ = 0 := by
    have : (2 : K) * κ = 0 := by linear_combination h3
    exact (mul_eq_zero.mp this).resolve_left h2
  rw [hw, h4, zero_smul]

theorem anticomm_sS {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hM : Mᵀ * sJ n K * M = sJ n K) {c ε ε' : K} (hMM : M * M = c • 1)
    {u v : Fin n ⊕ Fin n → K} (hu : u ≠ 0) (hv : v ≠ 0) (hMu : M *ᵥ u = ε • u)
    (hMv : M *ᵥ v = ε' • v) (hεε' : ε * ε' = -1) : M * sS u v = -(sS u v * M) := by
  have hcε : c = ε * ε := by
    have h1 : M *ᵥ (M *ᵥ u) = c • u := by
      rw [Matrix.mulVec_mulVec, hMM, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hMu, Matrix.mulVec_smul, hMu, smul_smul] at h1
    have h2 : (c - ε * ε) • u = 0 := by rw [sub_smul]; exact sub_eq_zero.mpr h1.symm
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hu)
  have hcε' : c = ε' * ε' := by
    have h1 : M *ᵥ (M *ᵥ v) = c • v := by
      rw [Matrix.mulVec_mulVec, hMM, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hMv, Matrix.mulVec_smul, hMv, smul_smul] at h1
    have h2 : (c - ε' * ε') • v = 0 := by rw [sub_smul]; exact sub_eq_zero.mpr h1.symm
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv)
  have e1 : ε' * c = -ε := by linear_combination ε' * hcε + ε * hεε'
  have e2 : ε * c = -ε' := by linear_combination ε * hcε' + ε' * hεε'
  have l1 := sLam_vecMul_eigen hM hMM hMu
  have l2 := sLam_vecMul_eigen hM hMM hMv
  rw [e2] at l1
  rw [e1] at l2
  simp only [sS, Matrix.mul_add, Matrix.add_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hMu,
    hMv, l1, l2, smul_vecMulVec, vecMulVec_smul]
  module

theorem finrank_sp_space : Module.finrank K (Fin n ⊕ Fin n → K) = n + n := by simp

theorem sJ_det_ne_zero : (sJ n K).det ≠ 0 := by
  have : (sJ n K).det * (sJ n K).det = 1 := by
    rw [← Matrix.det_mul, sJ_mul_self, Matrix.det_neg]
    simp
  exact left_ne_zero_of_mul_eq_one this

theorem sJ_nondeg : (Matrix.toBilin' (sJ n K)).Nondegenerate := by
  rw [Matrix.nondegenerate_toBilin'_iff, Matrix.nondegenerate_iff_det_ne_zero]
  exact sJ_det_ne_zero

theorem finrank_le_of_isotropic (W : Submodule K (Fin n ⊕ Fin n → K))
    (hW : ∀ x ∈ W, ∀ y ∈ W, sLam x ⬝ᵥ y = 0) : Module.finrank K W ≤ n := by
  let B : LinearMap.BilinForm K (Fin n ⊕ Fin n → K) := Matrix.toBilin' (sJ n K)
  have hB : ∀ x y : Fin n ⊕ Fin n → K, B x y = sLam x ⬝ᵥ y := fun x y => by
    show Matrix.toBilin' (sJ n K) x y = sLam x ⬝ᵥ y
    rw [Matrix.toBilin'_apply']
    exact Matrix.dotProduct_mulVec x (sJ n K) y
  have hle : W ≤ B.orthogonal W := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    show B y x = 0
    rw [hB]
    exact hW y hy x hx
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal sJ_nondeg W, finrank_sp_space] at h1
  omega

abbrev eig (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (μ : K) : Submodule K (Fin n ⊕ Fin n → K) :=
  Module.End.eigenspace (Matrix.mulVecLin M) μ

theorem mem_eig {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} {μ : K} {x : Fin n ⊕ Fin n → K} :
    x ∈ eig M μ ↔ M *ᵥ x = μ • x := by
  simp [eig]

theorem eig_sup {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} {s : K} (h2 : (2 : K) ≠ 0)
    (hs : s ≠ 0) (hM : M * M = (s * s) • 1) : eig M s ⊔ eig M (-s) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hMM : M *ᵥ (M *ᵥ x) = (s * s) • x := by
    rw [Matrix.mulVec_mulVec, hM, Matrix.smul_mulVec, Matrix.one_mulVec]
  have ha : x + s⁻¹ • (M *ᵥ x) ∈ eig M s := by
    rw [mem_eig, Matrix.mulVec_add, Matrix.mulVec_smul, hMM, smul_add, smul_smul, smul_smul]
    have e' : s⁻¹ * (s * s) = s := by field_simp
    rw [e', mul_inv_cancel₀ hs, one_smul, add_comm]
  have hb : x - s⁻¹ • (M *ᵥ x) ∈ eig M (-s) := by
    rw [mem_eig, Matrix.mulVec_sub, Matrix.mulVec_smul, hMM, smul_sub, smul_smul, smul_smul]
    have e' : s⁻¹ * (s * s) = s := by field_simp
    rw [e']
    simp only [neg_smul, neg_mul, mul_inv_cancel₀ hs, one_smul]
    abel
  have hx : (2⁻¹ : K) • (x + s⁻¹ • (M *ᵥ x)) + (2⁻¹ : K) • (x - s⁻¹ • (M *ᵥ x)) = x := by
    rw [← smul_add]
    have : x + s⁻¹ • (M *ᵥ x) + (x - s⁻¹ • (M *ᵥ x)) = (2 : K) • x := by
      rw [two_smul]
      abel
    rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul]
  exact Submodule.mem_sup.mpr ⟨_, Submodule.smul_mem _ _ ha, _, Submodule.smul_mem _ _ hb, hx⟩

theorem finrank_eig_add {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} {s : K}
    (h2 : (2 : K) ≠ 0) (hs : s ≠ 0) (hM : M * M = (s * s) • 1) :
    n + n ≤ Module.finrank K (eig M s) + Module.finrank K (eig M (-s)) := by
  have h1 := Submodule.finrank_add_le_finrank_add_finrank (eig M s) (eig M (-s))
  rw [eig_sup h2 hs hM, finrank_top, finrank_sp_space] at h1
  exact h1

end CFSG.HardMathSupport.Foote.ModuleExclusions
