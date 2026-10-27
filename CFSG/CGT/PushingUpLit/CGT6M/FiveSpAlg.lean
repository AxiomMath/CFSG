module

public import CFSG.Open.StatedDefs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open Matrix CFSG.Open


variable {K : Type} [Field K]

abbrev spJ (K : Type) [Field K] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks 0 1 (-1) 0

theorem spJ_mul_self : spJ K * spJ K = -1 := by
  simp [spJ, Matrix.fromBlocks_multiply]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp

theorem spJ_transpose : (spJ K)ᵀ = -spJ K := by
  simp [spJ, Matrix.fromBlocks_transpose]
  rw [Matrix.fromBlocks_neg]
  simp

abbrev spLam (a : Fin 2 ⊕ Fin 2 → K) : Fin 2 ⊕ Fin 2 → K := a ᵥ* spJ K

theorem spJ_mulVec (a : Fin 2 ⊕ Fin 2 → K) : spJ K *ᵥ a = -spLam a := by
  have h : spLam a = (spJ K)ᵀ *ᵥ a := (Matrix.mulVec_transpose _ _).symm
  rw [h, spJ_transpose, Matrix.neg_mulVec, neg_neg]

theorem spLam_spLam (a : Fin 2 ⊕ Fin 2 → K) : spLam (spLam a) = -a := by
  show a ᵥ* spJ K ᵥ* spJ K = -a
  rw [Matrix.vecMul_vecMul, spJ_mul_self, Matrix.vecMul_neg, Matrix.vecMul_one]

theorem spLam_eq_zero {a : Fin 2 ⊕ Fin 2 → K} (h : spLam a = 0) : a = 0 := by
  have := spLam_spLam a
  rw [h] at this
  have h0 : spLam (0 : Fin 2 ⊕ Fin 2 → K) = 0 := by simp [spLam]
  rw [h0] at this
  exact neg_eq_zero.mp this.symm

theorem exists_spLam_ne {a : Fin 2 ⊕ Fin 2 → K} (ha : a ≠ 0) :
    ∃ x : Fin 2 ⊕ Fin 2 → K, spLam a ⬝ᵥ x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply ha
  apply spLam_eq_zero
  funext i
  have := hcon (Pi.single i 1)
  simpa [dotProduct_single] using this

theorem spLam_dot_swap (x y : Fin 2 ⊕ Fin 2 → K) : spLam x ⬝ᵥ y = -(spLam y ⬝ᵥ x) := by
  have h1 : spLam x ⬝ᵥ y = x ⬝ᵥ (spJ K *ᵥ y) := (Matrix.dotProduct_mulVec _ _ _).symm
  rw [h1, spJ_mulVec, dotProduct_neg, dotProduct_comm]

theorem spLam_dot_self (h2 : (2 : K) ≠ 0) (x : Fin 2 ⊕ Fin 2 → K) : spLam x ⬝ᵥ x = 0 := by
  have h := spLam_dot_swap x x
  have : (2 : K) * (spLam x ⬝ᵥ x) = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left h2

theorem symp_of_mem_statedSp {A : GL (Fin 2 ⊕ Fin 2) K} (hA : A ∈ StatedSp 2 K) :
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * spJ K *
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = spJ K := by
  induction hA using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => simp
  | mul x y _ _ hx hy =>
    rw [Units.val_mul, Matrix.transpose_mul]
    calc (↑y)ᵀ * (↑x)ᵀ * spJ K * (↑x * ↑y) = (↑y)ᵀ * ((↑x)ᵀ * spJ K * ↑x) * ↑y := by
          simp only [Matrix.mul_assoc]
      _ = spJ K := by rw [hx, hy]
  | inv x _ hx =>
    set B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
      ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hB
    have h1 : (↑x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * B = 1 := Units.mul_inv x
    calc Bᵀ * spJ K * B
        = Bᵀ * ((↑x)ᵀ * spJ K * ↑x) * B := by rw [hx]
      _ = ((↑x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * B)ᵀ * spJ K *
            (↑x * B) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = spJ K := by rw [h1]; simp

theorem spDot_mulVec_left (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (y w : Fin 2 ⊕ Fin 2 → K) : (M *ᵥ y) ⬝ᵥ w = y ⬝ᵥ (Mᵀ *ᵥ w) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

theorem spLam_symp {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K} (hM : Mᵀ * spJ K * M = spJ K)
    (y z : Fin 2 ⊕ Fin 2 → K) : spLam (M *ᵥ y) ⬝ᵥ (M *ᵥ z) = spLam y ⬝ᵥ z := by
  have e1 : spLam (M *ᵥ y) ⬝ᵥ (M *ᵥ z) = (M *ᵥ y) ⬝ᵥ (spJ K *ᵥ (M *ᵥ z)) :=
    (Matrix.dotProduct_mulVec _ _ _).symm
  rw [e1, spDot_mulVec_left, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM,
    ← Matrix.dotProduct_mulVec]

theorem spLam_vecMul_eigen {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hM : Mᵀ * spJ K * M = spJ K) {c ε : K} (hMM : M * M = c • 1) {a : Fin 2 ⊕ Fin 2 → K}
    (hMa : M *ᵥ a = ε • a) : spLam a ᵥ* M = (ε * c) • spLam a := by
  have key : ∀ x : Fin 2 ⊕ Fin 2 → K, (spLam a ᵥ* M) ⬝ᵥ x = ((ε * c) • spLam a) ⬝ᵥ x := by
    intro x
    have h1 : (spLam a ᵥ* M) ⬝ᵥ x = spLam a ⬝ᵥ (M *ᵥ x) := (Matrix.dotProduct_mulVec _ _ _).symm
    have h2 : spLam a ⬝ᵥ (M *ᵥ x) = spLam (M *ᵥ a) ⬝ᵥ (M *ᵥ (M *ᵥ x)) :=
      (spLam_symp hM a (M *ᵥ x)).symm
    have h3 : M *ᵥ (M *ᵥ x) = c • x := by
      rw [Matrix.mulVec_mulVec, hMM, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [h1, h2, h3, hMa, dotProduct_smul]
    have : spLam (ε • a) = ε • spLam a := by simp [spLam, Matrix.smul_vecMul]
    rw [this, smul_dotProduct, smul_eq_mul, smul_dotProduct, smul_eq_mul]
    simp only [smul_eq_mul]
    ring
  funext i
  have := key (Pi.single i 1)
  simpa [dotProduct_single] using this

theorem spJ_det_ne_zero : (spJ K).det ≠ 0 := by
  have : (spJ K).det * (spJ K).det = 1 := by
    rw [← Matrix.det_mul, spJ_mul_self, Matrix.det_neg]
    simp
    norm_num
  exact left_ne_zero_of_mul_eq_one this

theorem spJ_nondeg : (Matrix.toBilin' (spJ K)).Nondegenerate := by
  rw [Matrix.nondegenerate_toBilin'_iff, Matrix.nondegenerate_iff_det_ne_zero]
  exact spJ_det_ne_zero

theorem exists_two_eigen_sp [CharP K 5] {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hM : Mᵀ * spJ K * M = spJ K) (hMM : M * M = (-1 : K) • 1) :
    ∃ a₁ a₂ : Fin 2 ⊕ Fin 2 → K, LinearIndependent K ![a₁, a₂] ∧ M *ᵥ a₁ = (2 : K) • a₁ ∧
      M *ᵥ a₂ = (2 : K) • a₂ := by
  have h5 : (5 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 5
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : (1 : K) = 0 := by linear_combination 3 * h - h5
    exact one_ne_zero this
  have hMMx : ∀ x : Fin 2 ⊕ Fin 2 → K, M *ᵥ (M *ᵥ x) = (-1 : K) • x := fun x => by
    rw [Matrix.mulVec_mulVec, hMM, Matrix.smul_mulVec, Matrix.one_mulVec]
  let N2 : Submodule K (Fin 2 ⊕ Fin 2 → K) :=
    LinearMap.ker (Matrix.mulVecLin M - (2 : K) • LinearMap.id)
  let N3 : Submodule K (Fin 2 ⊕ Fin 2 → K) :=
    LinearMap.ker (Matrix.mulVecLin M + (2 : K) • LinearMap.id)
  have hN2 : ∀ x, x ∈ N2 ↔ M *ᵥ x = (2 : K) • x := fun x => by
    simp only [N2, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.mulVecLin_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  have hN3 : ∀ x, x ∈ N3 ↔ M *ᵥ x = (-2 : K) • x := fun x => by
    simp only [N3, LinearMap.mem_ker, LinearMap.add_apply, Matrix.mulVecLin_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
    rw [neg_smul, eq_neg_iff_add_eq_zero]
  have h4 : (2 : K) * 2 = -1 := by linear_combination h5
  have h4' : (-2 : K) * 2 = 1 := by linear_combination (-1 : K) * h5
  have h44 : (4 : K) * 4 = 1 := by linear_combination 3 * h5
  have hsup : N2 ⊔ N3 = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have ha : M *ᵥ x + (2 : K) • x ∈ N2 := by
      rw [hN2, Matrix.mulVec_add, Matrix.mulVec_smul, hMMx, smul_add, smul_smul, h4]
      abel
    have hb : M *ᵥ x - (2 : K) • x ∈ N3 := by
      rw [hN3, Matrix.mulVec_sub, Matrix.mulVec_smul, hMMx]
      simp only [neg_smul, one_smul, smul_sub, smul_smul, h4']
      abel
    have hx : (4 : K) • (M *ᵥ x + (2 : K) • x) + -((4 : K) • (M *ᵥ x - (2 : K) • x)) = x := by
      have e : (4 : K) • (M *ᵥ x + (2 : K) • x) + -((4 : K) • (M *ᵥ x - (2 : K) • x)) =
          ((4 : K) * 4) • x := by
        module
      rw [e, h44, one_smul]
    exact Submodule.mem_sup.mpr ⟨_, N2.smul_mem (4 : K) ha, _, N3.neg_mem (N3.smul_mem (4 : K) hb),
      hx⟩
  have hiso : ∀ x ∈ N3, ∀ y ∈ N3, spLam x ⬝ᵥ y = 0 := by
    intro x hx y hy
    have hx' := (hN3 x).mp hx
    have hy' := (hN3 y).mp hy
    have h1 := spLam_symp hM x y
    rw [hx', hy'] at h1
    have h2' : spLam ((-2 : K) • x) = (-2 : K) • spLam x := Matrix.smul_vecMul _ _ _
    rw [h2', smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h1
    have h3 : (-2 : K) * ((-2 : K) * (spLam x ⬝ᵥ y)) = (spLam x ⬝ᵥ y) := h1
    have h3' : (3 : K) * (spLam x ⬝ᵥ y) = 0 := by linear_combination h3
    linear_combination 2 * h3' - (spLam x ⬝ᵥ y) * h5
  let B : LinearMap.BilinForm K (Fin 2 ⊕ Fin 2 → K) := Matrix.toBilin' (spJ K)
  have hB : ∀ x y : Fin 2 ⊕ Fin 2 → K, B x y = spLam x ⬝ᵥ y := fun x y => by
    show Matrix.toBilin' (spJ K) x y = spLam x ⬝ᵥ y
    rw [Matrix.toBilin'_apply']
    exact Matrix.dotProduct_mulVec x (spJ K) y
  have hle3 : N3 ≤ B.orthogonal N3 := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    show B y x = 0
    rw [hB]
    exact hiso y hy x hx
  have hfin : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by simp
  have hrank3 : Module.finrank K N3 ≤ 2 := by
    have h1 := Submodule.finrank_mono hle3
    rw [LinearMap.BilinForm.finrank_orthogonal spJ_nondeg N3, hfin] at h1
    omega
  have hrank2 : 2 ≤ Module.finrank K N2 := by
    have h1 := Submodule.finrank_add_le_finrank_add_finrank N2 N3
    rw [hsup, finrank_top, hfin] at h1
    omega
  have hpos : 0 < Module.finrank K N2 := by omega
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  obtain ⟨y, hy⟩ := exists_linearIndependent_pair_of_one_lt_finrank (R := K) (M := N2)
    (by omega) hx
  refine ⟨(x : Fin 2 ⊕ Fin 2 → K), (y : Fin 2 ⊕ Fin 2 → K), ?_, (hN2 x).mp x.2, (hN2 y).mp y.2⟩
  rw [LinearIndependent.pair_iff] at hy ⊢
  intro s t hst
  exact hy s t (Subtype.ext (by simpa using hst))



theorem spS2_symp (h2 : (2 : K) ≠ 0) (u v : Fin 2 ⊕ Fin 2 → K) (huv : spLam u ⬝ᵥ v = 0) (t : K) :
    (1 + t • (vecMulVec u (spLam v) + vecMulVec v (spLam u)))ᵀ * spJ K *
      (1 + t • (vecMulVec u (spLam v) + vecMulVec v (spLam u))) = spJ K := by
  set N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := vecMulVec u (spLam v) + vecMulVec v (spLam u)
    with hN
  have hvu : spLam v ⬝ᵥ u = 0 := by rw [spLam_dot_swap, huv, neg_zero]
  have hNJ : Nᵀ * spJ K = vecMulVec (spLam v) (spLam u) + vecMulVec (spLam u) (spLam v) := by
    simp only [hN, Matrix.transpose_add, Matrix.transpose_vecMulVec, Matrix.add_mul,
      Matrix.vecMulVec_mul]
  have hJN : spJ K * N = -(vecMulVec (spLam u) (spLam v) + vecMulVec (spLam v) (spLam u)) := by
    simp only [hN, Matrix.mul_add, Matrix.mul_vecMulVec, spJ_mulVec, Matrix.neg_vecMulVec]
    abel
  have hsum : Nᵀ * spJ K + spJ K * N = 0 := by
    rw [hNJ, hJN]
    abel
  have hNN : Nᵀ * spJ K * N = 0 := by
    rw [hNJ]
    simp only [hN, Matrix.add_mul, Matrix.mul_add, Matrix.vecMulVec_mul_vecMulVec,
      spLam_dot_self h2, huv, hvu, zero_smul]
    simp
  have e1 : (1 + t • N)ᵀ * spJ K * (1 + t • N) =
      spJ K + t • (Nᵀ * spJ K + spJ K * N) + (t * t) • (Nᵀ * spJ K * N) := by
    simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_add,
      smul_smul]
    abel
  rw [e1, hsum, hNN]
  simp

theorem spTransv_symp (h2 : (2 : K) ≠ 0) (a : Fin 2 ⊕ Fin 2 → K) (t : K) :
    (1 + t • vecMulVec a (spLam a))ᵀ * spJ K * (1 + t • vecMulVec a (spLam a)) = spJ K := by
  have h := spS2_symp h2 a a (spLam_dot_self h2 a) (t / 2)
  have e : (t / 2) • (vecMulVec a (spLam a) + vecMulVec a (spLam a)) =
      t • vecMulVec a (spLam a) := by
    rw [← two_smul K (vecMulVec a (spLam a)), smul_smul]
    congr 1
    field_simp
  rwa [e] at h

theorem symp_mul {P Q : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K} (hP : Pᵀ * spJ K * P = spJ K)
    (hQ : Qᵀ * spJ K * Q = spJ K) : (P * Q)ᵀ * spJ K * (P * Q) = spJ K := by
  rw [Matrix.transpose_mul]
  calc Qᵀ * Pᵀ * spJ K * (P * Q) = Qᵀ * (Pᵀ * spJ K * P) * Q := by simp only [Matrix.mul_assoc]
    _ = spJ K := by rw [hP, hQ]

theorem spLam_eigen_zero {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hM : Mᵀ * spJ K * M = spJ K) {ε ε' : K} {a b : Fin 2 ⊕ Fin 2 → K} (ha : M *ᵥ a = ε • a)
    (hb : M *ᵥ b = ε' • b) (h : ε * ε' ≠ 1) : spLam a ⬝ᵥ b = 0 := by
  have h1 := spLam_symp hM a b
  rw [ha, hb] at h1
  have e : spLam (ε • a) = ε • spLam a := Matrix.smul_vecMul _ _ _
  rw [e, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h1
  have h3 : (ε * ε' - 1) * (spLam a ⬝ᵥ b) = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr h)

end CFSG.CGT.PushingUpLit.CGT6M
