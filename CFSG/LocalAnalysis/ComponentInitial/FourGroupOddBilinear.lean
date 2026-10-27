module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupCommuting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix

namespace FourGroupOddBilinear

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def isometrySL (R : Matrix (Fin n) (Fin n) K) : Subgroup (SpecialLinearGroup (Fin n) K)
    where
  carrier := {g | (g : Matrix (Fin n) (Fin n) K)ᵀ * R * g = R}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq, SpecialLinearGroup.coe_mul, transpose_mul] at hg hh ⊢
    rw [show (h : Matrix (Fin n) (Fin n) K)ᵀ * (g : Matrix (Fin n) (Fin n) K)ᵀ * R *
        ((g : Matrix (Fin n) (Fin n) K) * h) =
      (h : Matrix (Fin n) (Fin n) K)ᵀ * ((g : Matrix (Fin n) (Fin n) K)ᵀ * R * g) * h by
        simp only [Matrix.mul_assoc], hg, hh]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg ⊢
    set a : Matrix (Fin n) (Fin n) K := (g : Matrix (Fin n) (Fin n) K)
    set b : Matrix (Fin n) (Fin n) K := ((g⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K)
    have h2 : a * b = 1 := by
      simp only [a, b]
      rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]
    calc bᵀ * R * b = bᵀ * (aᵀ * R * a) * b := by rw [hg]
      _ = (a * b)ᵀ * R * (a * b) := by simp only [transpose_mul, Matrix.mul_assoc]
      _ = R := by rw [h2, transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem mem_isometrySL {R : Matrix (Fin n) (Fin n) K} {g : SpecialLinearGroup (Fin n) K} :
    g ∈ isometrySL R ↔ (g : Matrix (Fin n) (Fin n) K)ᵀ * R * g = R :=
  Iff.rfl

theorem mem_scalars_of_coe_eq_smul (hn : 0 < n) {A : SpecialLinearGroup (Fin n) K} {a : K}
    (h : (A : Matrix (Fin n) (Fin n) K) = a • 1) : A ∈ LinearFlag.scalars n K := by
  have hdet : a ^ n = 1 := by
    have := A.prop
    rw [h, det_smul, det_one, mul_one, Fintype.card_fin] at this
    exact this
  have ha : a ≠ 0 := fun ha => by
    rw [ha, zero_pow hn.ne'] at hdet
    exact zero_ne_one hdet
  refine ⟨Units.mk0 a ha, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hdet,
    Units.val_one]), ?_⟩
  rw [h, Units.val_mk0, scalar_apply, smul_one_eq_diagonal]

theorem proj_eq_of_coe_eq_smul (hn : 0 < n) {A B : SpecialLinearGroup (Fin n) K} {a : K}
    (h : (A : Matrix (Fin n) (Fin n) K) = a • (B : Matrix (Fin n) (Fin n) K)) :
    LinearFlag.proj n K A = LinearFlag.proj n K B := by
  have hmem : A * B⁻¹ ∈ LinearFlag.scalars n K := by
    refine mem_scalars_of_coe_eq_smul hn (a := a) ?_
    rw [SpecialLinearGroup.coe_mul, h, Matrix.smul_mul, ← SpecialLinearGroup.coe_mul,
      mul_inv_cancel, SpecialLinearGroup.coe_one]
  have h1 : LinearFlag.proj n K (A * B⁻¹) = 1 := LinearFlag.proj_eq_one_iff.2 hmem
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

section Transfer

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_four_of_model (hn : 0 < n) (c : Module.Basis ι K (Fin n → K))
    (R : Matrix (Fin n) (Fin n) K) (M : Matrix ι ι K)
    (hM : ∀ i j, M i j = c i ⬝ᵥ (R *ᵥ c j)) {X Y : Matrix ι ι K} (hXM : Xᵀ * M * X = M)
    (hYM : Yᵀ * M * Y = M) (hXd : X.det = 1) (hYd : Y.det = 1) (hXX : ∃ a : K, X * X = a • 1)
    (hYY : ∃ a : K, Y * Y = a • 1) (hXY : ∃ a : K, X * Y = a • (Y * X))
    (hX : ∀ a : K, X ≠ a • 1) (hY : ∀ a : K, Y ≠ a • 1) (hXYn : ∀ a : K, X * Y ≠ a • 1) :
    ∃ V : Subgroup (LinearFlag.projectiveSL n K),
      V ≤ (isometrySL R).map (LinearFlag.proj n K) ∧ CFSG.IsElementaryAbelian 2 V ∧
        Nat.card V = 4 := by
  classical
  set e := Pi.basisFun K (Fin n)
  set P : Matrix (Fin n) ι K := e.toMatrix c
  set Q : Matrix ι (Fin n) K := c.toMatrix e
  have hPQ : P * Q = 1 := Module.Basis.toMatrix_mul_toMatrix_flip e c
  have hQP : Q * P = 1 := Module.Basis.toMatrix_mul_toMatrix_flip c e
  have hPRP : Pᵀ * R * P = M := by
    ext i j
    rw [hM, dotProduct, Matrix.mul_apply]
    simp only [Matrix.mul_apply, transpose_apply, P, Module.Basis.toMatrix_apply, e,
      Pi.basisFun_repr, mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hΦmul : ∀ A B : Matrix ι ι K, P * A * Q * (P * B * Q) = P * (A * B) * Q := fun A B => by
    rw [show P * A * Q * (P * B * Q) = P * A * (Q * P) * B * Q by simp only [Matrix.mul_assoc],
      hQP, Matrix.mul_one, Matrix.mul_assoc P A B]
  have hΦsmul : ∀ (a : K) (A : Matrix ι ι K), P * (a • A) * Q = a • (P * A * Q) := fun a A => by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hΦone : P * (1 : Matrix ι ι K) * Q = 1 := by rw [Matrix.mul_one, hPQ]
  have hΦiso : ∀ A : Matrix ι ι K, Aᵀ * M * A = M → (P * A * Q)ᵀ * R * (P * A * Q) = R := by
    intro A hA
    calc (P * A * Q)ᵀ * R * (P * A * Q) = Qᵀ * (Aᵀ * (Pᵀ * R * P) * A) * Q := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = (P * Q)ᵀ * R * (P * Q) := by
          rw [hPRP, hA, ← hPRP]; simp only [transpose_mul, Matrix.mul_assoc]
      _ = R := by rw [hPQ, transpose_one, Matrix.one_mul, Matrix.mul_one]
  have hΦdet : ∀ A : Matrix ι ι K, (P * A * Q).det = A.det := by
    intro A
    have h := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix e c e c (Matrix.toLin c c A)
    rw [LinearMap.toMatrix_toLin, LinearMap.toMatrix_eq_toMatrix'] at h
    rw [h, LinearMap.det_toMatrix', ← LinearMap.det_toMatrix c, LinearMap.toMatrix_toLin]
  have hΦscalar : ∀ (A : Matrix ι ι K) (a : K), P * A * Q = a • 1 → A = a • 1 := by
    intro A a h
    calc A = Q * (P * A * Q) * P := by
          rw [show Q * (P * A * Q) * P = (Q * P) * A * (Q * P) by simp only [Matrix.mul_assoc],
            hQP, Matrix.one_mul, Matrix.mul_one]
      _ = a • 1 := by rw [h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hQP]
  let x : SpecialLinearGroup (Fin n) K := ⟨P * X * Q, by rw [hΦdet, hXd]⟩
  let y : SpecialLinearGroup (Fin n) K := ⟨P * Y * Q, by rw [hΦdet, hYd]⟩
  have hx : (x : Matrix (Fin n) (Fin n) K) = P * X * Q := rfl
  have hy : (y : Matrix (Fin n) (Fin n) K) = P * Y * Q := rfl
  have hxI : x ∈ isometrySL R := hΦiso X hXM
  have hyI : y ∈ isometrySL R := hΦiso Y hYM
  have hnotscalar : ∀ (A : Matrix ι ι K), (∀ a : K, A ≠ a • 1) → ∀ g : SpecialLinearGroup (Fin n) K,
      (g : Matrix (Fin n) (Fin n) K) = P * A * Q → g ∉ LinearFlag.scalars n K := by
    rintro A hA g hg ⟨u, -, hu⟩
    rw [hg, scalar_apply, ← smul_one_eq_diagonal] at hu
    exact hA _ (hΦscalar A _ hu)
  have hsq : ∀ (A : Matrix ι ι K) (g : SpecialLinearGroup (Fin n) K),
      (g : Matrix (Fin n) (Fin n) K) = P * A * Q → (∃ a : K, A * A = a • 1) →
        LinearFlag.proj n K g * LinearFlag.proj n K g = 1 := by
    rintro A g hg ⟨a, ha⟩
    rw [← map_mul, LinearFlag.proj_eq_one_iff]
    refine mem_scalars_of_coe_eq_smul hn (a := a) ?_
    rw [SpecialLinearGroup.coe_mul, hg, hΦmul, ha, hΦsmul, hΦone]
  have hpx : LinearFlag.proj n K x * LinearFlag.proj n K x = 1 := hsq X x hx hXX
  have hpy : LinearFlag.proj n K y * LinearFlag.proj n K y = 1 := hsq Y y hy hYY
  have hpxy : LinearFlag.proj n K x * LinearFlag.proj n K y =
      LinearFlag.proj n K y * LinearFlag.proj n K x := by
    obtain ⟨a, ha⟩ := hXY
    rw [← map_mul, ← map_mul]
    refine proj_eq_of_coe_eq_smul hn (a := a) ?_
    rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, hx, hy, hΦmul, hΦmul, ha, hΦsmul]
  have hpx1 : LinearFlag.proj n K x ≠ 1 := fun h =>
    hnotscalar X hX x hx (LinearFlag.proj_eq_one_iff.1 h)
  have hpy1 : LinearFlag.proj n K y ≠ 1 := fun h =>
    hnotscalar Y hY y hy (LinearFlag.proj_eq_one_iff.1 h)
  have hpne : LinearFlag.proj n K x ≠ LinearFlag.proj n K y := fun h => by
    have h1 : LinearFlag.proj n K (x * y) = 1 := by rw [map_mul, ← h, hpx]
    exact hnotscalar (X * Y) hXYn (x * y) (by rw [SpecialLinearGroup.coe_mul, hx, hy, hΦmul])
      (LinearFlag.proj_eq_one_iff.1 h1)
  obtain ⟨V, -, hVle, hV, hVcard⟩ := FourGroup.exists_kleinFour hpx hpy hpxy hpx1 hpy1 hpne
  exact ⟨V, hVle _ (Subgroup.mem_map_of_mem _ hxI) (Subgroup.mem_map_of_mem _ hyI), hV, hVcard⟩

end Transfer

section Signs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def signDiag (S : Finset ι) : Matrix ι ι K :=
  diagonal fun i => if i ∈ S then -1 else 1

omit [Fintype ι] in
theorem signDiag_apply (S : Finset ι) (i j : ι) :
    signDiag (K := K) S i j = if i = j then (if i ∈ S then -1 else 1) else 0 := by
  rw [signDiag, diagonal_apply]

theorem signDiag_mul_self (S : Finset ι) : signDiag (K := K) S * signDiag S = 1 := by
  rw [signDiag, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  split_ifs <;> simp

theorem signDiag_comm (S T : Finset ι) :
    signDiag (K := K) S * signDiag T = signDiag T * signDiag S := by
  rw [signDiag, signDiag, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem signDiag_mul_signDiag_apply_self (S T : Finset ι) (i : ι) :
    (signDiag (K := K) S * signDiag (K := K) T : Matrix ι ι K) i i =
      (if i ∈ S then -1 else 1) * (if i ∈ T then -1 else 1) := by
  rw [signDiag, signDiag, diagonal_mul_diagonal, diagonal_apply_eq]

theorem det_signDiag (S : Finset ι) : (signDiag (K := K) S).det = (-1) ^ S.card := by
  rw [signDiag, det_diagonal, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

omit [Fintype ι] in
theorem transpose_signDiag (S : Finset ι) : (signDiag (K := K) S)ᵀ = signDiag S :=
  diagonal_transpose _

theorem signDiag_mul_comm {S : Finset ι} {M : Matrix ι ι K}
    (hM : ∀ i j, M i j ≠ 0 → (i ∈ S ↔ j ∈ S)) : signDiag S * M = M * signDiag S := by
  ext i j
  rw [signDiag, diagonal_mul, mul_diagonal]
  by_cases h : M i j = 0
  · rw [h, mul_zero, zero_mul]
  · have := hM i j h
    by_cases hi : i ∈ S
    · simp only [hi, this.1 hi, ↓reduceIte]
      ring
    · simp only [hi, show j ∉ S from fun hj => hi (this.2 hj), ↓reduceIte]
      ring

theorem signDiag_conj {S : Finset ι} {M : Matrix ι ι K}
    (hM : ∀ i j, M i j ≠ 0 → (i ∈ S ↔ j ∈ S)) :
    (signDiag S)ᵀ * M * signDiag S = M := by
  rw [transpose_signDiag, signDiag_mul_comm hM, Matrix.mul_assoc, signDiag_mul_self,
    Matrix.mul_one]

omit [Fintype ι] in
theorem signDiag_ne_smul (h2 : (2 : K) ≠ 0) {S : Finset ι} {i j : ι} (hi : i ∈ S) (hj : j ∉ S)
    (a : K) : signDiag S ≠ a • (1 : Matrix ι ι K) := fun h => by
  have h1 := congrFun (congrFun h i) i
  have h2' := congrFun (congrFun h j) j
  simp only [signDiag_apply, hi, ↓reduceIte, Matrix.smul_apply, one_apply_eq, smul_eq_mul,
    mul_one] at h1
  simp only [signDiag_apply, hj, ↓reduceIte, Matrix.smul_apply, one_apply_eq, smul_eq_mul,
    mul_one] at h2'
  exact h2 (by linear_combination h2' - h1)

end Signs

theorem det_J (m : ℕ) : (J (Fin m) K).det = 1 := by
  have h : J (Fin m) K = fromBlocks 1 (-1) 0 1 * fromBlocks 1 0 1 1 * fromBlocks 1 (-1) 0 1 := by
    simp only [J, fromBlocks_multiply]
    simp
  rw [h, det_mul, det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂]
  simp

end FourGroupOddBilinear

open FourGroupOddBilinear

theorem bilinear_isometry_projective_four_group {K : Type*} [Field K]
    (hK : ringChar K ≠ 2) {n : ℕ} (hn : 3 ≤ n) (R : GL (Fin n) K)
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = R ∨ (R : Matrix (Fin n) (Fin n) K)ᵀ = -R) :
    ∃ V : Subgroup (LinearFlag.projectiveSL n K),
      V ≤ (isometrySL (R : Matrix (Fin n) (Fin n) K)).map (LinearFlag.proj n K) ∧
        CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  classical
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hn0 : 0 < n := by omega
  set B := Matrix.toBilin' (R : Matrix (Fin n) (Fin n) K) with hBdef
  have hB : ∀ x y, B x y = x ⬝ᵥ ((R : Matrix (Fin n) (Fin n) K) *ᵥ y) := fun x y =>
    Matrix.toBilin'_apply' _ x y
  rcases hR with hR | hR
  ·
    have : Invertible (2 : K) := invertibleOfNonzero h2
    have hsymm : LinearMap.IsSymm B := ⟨fun x y => by
      simp only [RingHom.id_apply, hB]
      rw [dotProduct_comm, ← vecMul_transpose, hR, dotProduct_mulVec]⟩
    obtain ⟨c, hc⟩ := LinearMap.BilinForm.exists_orthogonal_basis hsymm
    have hfin : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
    let i₀ : Fin (Module.finrank K (Fin n → K)) := ⟨0, by omega⟩
    let i₁ : Fin (Module.finrank K (Fin n → K)) := ⟨1, by omega⟩
    let i₂ : Fin (Module.finrank K (Fin n → K)) := ⟨2, by omega⟩
    have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
    have h02 : i₀ ≠ i₂ := by simp [i₀, i₂, Fin.ext_iff]
    have h12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
    let M : Matrix (Fin (Module.finrank K (Fin n → K))) (Fin (Module.finrank K (Fin n → K))) K :=
      Matrix.of fun i j => c i ⬝ᵥ ((R : Matrix (Fin n) (Fin n) K) *ᵥ c j)
    have hMij : ∀ i j, M i j = c i ⬝ᵥ ((R : Matrix (Fin n) (Fin n) K) *ᵥ c j) := fun i j => rfl
    have hMdiag : ∀ i j, M i j ≠ 0 → i = j := fun i j h => by
      by_contra hij
      exact h (by rw [hMij, ← hB]; exact hc hij)
    have hdiag : ∀ S : Finset (Fin (Module.finrank K (Fin n → K))), ∀ i j, M i j ≠ 0 →
        (i ∈ S ↔ j ∈ S) := fun S i j h => by rw [hMdiag i j h]
    refine exists_four_of_model hn0 c R M hMij
      (X := signDiag {i₀, i₁}) (Y := signDiag {i₀, i₂}) (signDiag_conj (hdiag _))
      (signDiag_conj (hdiag _)) (by rw [det_signDiag, Finset.card_pair h01]; norm_num)
      (by rw [det_signDiag, Finset.card_pair h02]; norm_num)
      ⟨1, by rw [signDiag_mul_self, one_smul]⟩ ⟨1, by rw [signDiag_mul_self, one_smul]⟩
      ⟨1, by rw [signDiag_comm, one_smul]⟩
      (signDiag_ne_smul h2 (S := {i₀, i₁}) (i := i₀) (j := i₂) (by simp)
        (by simp [h02.symm, h12.symm]))
      (signDiag_ne_smul h2 (S := {i₀, i₂}) (i := i₀) (j := i₁) (by simp) (by simp [h01.symm, h12]))
      (fun a h => ?_)
    have h0 := congrFun (congrFun h i₀) i₀
    have h1 := congrFun (congrFun h i₁) i₁
    rw [signDiag_mul_signDiag_apply_self, Matrix.smul_apply, one_apply_eq, smul_eq_mul,
      mul_one] at h0 h1
    simp only [Finset.mem_insert, Finset.mem_singleton, h01.symm, h12, h01, true_or,
      or_false, or_true, ↓reduceIte] at h0 h1
    exact h2 (by linear_combination h0 - h1)
  ·
    have halt : B.IsAlt := fun x => by
      rw [hB]
      have h : x ⬝ᵥ (R : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ x =
          x ⬝ᵥ (R : Matrix (Fin n) (Fin n) K) *ᵥ x := by
        rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]
      rw [hR, neg_mulVec, dotProduct_neg] at h
      have h' : (2 : K) * (x ⬝ᵥ (R : Matrix (Fin n) (Fin n) K) *ᵥ x) = 0 := by
        linear_combination -h
      exact (mul_eq_zero.1 h').resolve_left h2
    have hnd : B.Nondegenerate := by
      rw [hBdef, LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero]
      exact (Matrix.isUnit_iff_isUnit_det _).1 R.isUnit |>.ne_zero
    obtain ⟨m, c, hdim, hcJ⟩ :=
      CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_symplectic_basis B halt hnd
    have hm : 2 ≤ m := by
      rw [Module.finrank_fin_fun] at hdim
      omega
    have hM : ∀ i j, J (Fin m) K i j = c i ⬝ᵥ ((R : Matrix (Fin n) (Fin n) K) *ᵥ c j) := by
      intro i j
      rw [← hcJ, LinearMap.BilinForm.toMatrix_apply, hB]
    let p0 : Fin m := ⟨0, by omega⟩
    let p1 : Fin m := ⟨1, by omega⟩
    have h01 : p0 ≠ p1 := by simp [p0, p1, Fin.ext_iff]
    set S : Finset (Fin m ⊕ Fin m) := {Sum.inl p0, Sum.inr p0}
    have hJS : ∀ i j, J (Fin m) K i j ≠ 0 → (i ∈ S ↔ j ∈ S) := by
      intro i j h
      rcases i with i | i <;> rcases j with j | j <;>
        simp only [J, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
          fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, one_apply, ne_eq] at h <;>
        first
        | exact absurd rfl h
        | (by_cases hij : i = j
           · subst hij; simp [S]
           · simp [hij] at h)
    have hXJ : signDiag S * J (Fin m) K = J (Fin m) K * signDiag S := signDiag_mul_comm hJS
    refine exists_four_of_model hn0 c R (J (Fin m) K) hM (X := signDiag S) (Y := J (Fin m) K)
      (signDiag_conj hJS) ?_ (by rw [det_signDiag, Finset.card_pair (by simp)]; norm_num)
      (det_J m) ⟨1, by rw [signDiag_mul_self, one_smul]⟩ ⟨-1, by rw [J_squared, neg_one_smul]⟩
      ⟨1, by rw [hXJ, one_smul]⟩
      (signDiag_ne_smul h2 (S := S) (i := Sum.inl p0) (j := Sum.inl p1) (by simp [S])
        (by simp [S, h01.symm]))
      (fun a h => ?_) (fun a h => ?_)
    · rw [J_transpose, Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_assoc, J_squared,
        Matrix.mul_neg, Matrix.mul_one, neg_neg]
    · have := congrFun (congrFun h (Sum.inr p0)) (Sum.inl p0)
      simp [J] at this
    · have := congrFun (congrFun h (Sum.inr p0)) (Sum.inl p0)
      simp [signDiag, J, diagonal_mul, S] at this

theorem odd_bilinear_isometry_projective_four_group {K : Type*} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) {n : ℕ} (hn : 3 ≤ n) (R : GL (Fin n) K)
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = R ∨ (R : Matrix (Fin n) (Fin n) K)ᵀ = -R) :
    ∃ V : Subgroup (LinearFlag.projectiveSL n K),
      V ≤ (isometrySL (R : Matrix (Fin n) (Fin n) K)).map (LinearFlag.proj n K) ∧
        CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 :=
  bilinear_isometry_projective_four_group hK hn R hR

end CFSG.LocalAnalysis.ComponentInitial
