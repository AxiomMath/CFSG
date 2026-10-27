module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aDual
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped MatrixGroups Matrix

open CFSG.QuasithinUnique.Setup.X7

section Twist

variable {F : Type} [Field F] (k : Type) [Field k] [Algebra F k] [CharP k 2]

@[expose] def twistGL (i : ℕ) (A : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) k :=
  (frK k i).mapMatrix A

theorem twistGL_mul (i : ℕ) (A B : Matrix (Fin 3) (Fin 3) F) :
    twistGL k i (A * B) = twistGL k i A * twistGL k i B :=
  map_mul (frK k i).mapMatrix A B

theorem twistMat_eq_twistGL (i : ℕ) (g : SL(3, F)) :
    twistMat k i g = twistGL k i (g : Matrix (Fin 3) (Fin 3) F) := rfl

theorem twistGL_inv_mul (i : ℕ) (A : GL (Fin 3) F) :
    twistGL k i (A⁻¹).val * twistGL k i A.val = 1 := by
  rw [← twistGL_mul, Units.inv_mul]
  exact map_one (frK k i).mapMatrix

theorem twistGL_mul_inv (i : ℕ) (A : GL (Fin 3) F) :
    twistGL k i A.val * twistGL k i (A⁻¹).val = 1 := by
  rw [← twistGL_mul, Units.mul_inv]
  exact map_one (frK k i).mapMatrix

theorem twistMat_conj (i : ℕ) (A : GL (Fin 3) F) (g : SL(3, F)) :
    twistMat k i (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A g) =
      twistGL k i A.val * twistMat k i g * twistGL k i (A⁻¹).val := by
  rw [twistMat_eq_twistGL, twistMat_eq_twistGL,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix, twistGL_mul,
    twistGL_mul]

end Twist

section Adj

variable {F : Type} [Field F] (k : Type) [Field k] [Algebra F k] [CharP k 2]

@[expose] noncomputable def adjAd (B B' : Matrix (Fin 3) (Fin 3) k) :
    (Fin 8 → k) →ₗ[k] (Fin 8 → k) :=
  coL k ∘ₗ ((LinearMap.mulLeft k B) ∘ₗ (LinearMap.mulRight k B')) ∘ₗ XmL k

omit [CharP k 2] in
theorem adjAd_apply (B B' : Matrix (Fin 3) (Fin 3) k) (c : Fin 8 → k) :
    adjAd k B B' c = co (B * Xm c * B') := by
  simp [adjAd, coL_apply, XmL_apply, Matrix.mul_assoc]

omit [CharP k 2] in
theorem trace_conj_eq (C C' X : Matrix (Fin 3) (Fin 3) k) (h : C' * C = 1) :
    (C * X * C').trace = X.trace := by
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, h, Matrix.mul_one]

theorem adjAd_comp (B B' C C' : Matrix (Fin 3) (Fin 3) k) (h : C' * C = 1) (c : Fin 8 → k) :
    adjAd k B B' (adjAd k C C' c) = adjAd k (B * C) (C' * B') c := by
  rw [adjAd_apply, adjAd_apply, adjAd_apply,
    Xm_co k (by rw [trace_conj_eq k C C' _ h]; exact trace_Xm k c)]
  congr 1
  simp only [Matrix.mul_assoc]

omit [CharP k 2] in
theorem adjAd_one (c : Fin 8 → k) : adjAd k 1 1 c = c := by
  rw [adjAd_apply, Matrix.one_mul, Matrix.mul_one, co_Xm]

@[expose] noncomputable def adjAdMat (B B' : Matrix (Fin 3) (Fin 3) k) : Matrix (Fin 8) (Fin 8) k :=
  LinearMap.toMatrix' (adjAd k B B')

omit [CharP k 2] in
theorem adjAdMat_mulVec (B B' : Matrix (Fin 3) (Fin 3) k) (c : Fin 8 → k) :
    (adjAdMat k B B').mulVec c = adjAd k B B' c := by
  have := Matrix.toLin'_apply (adjAdMat k B B') c
  rw [adjAdMat, Matrix.toLin'_toMatrix'] at this
  exact this.symm

theorem adjAdMat_mul (B B' C C' : Matrix (Fin 3) (Fin 3) k) (h : C' * C = 1) :
    adjAdMat k B B' * adjAdMat k C C' = adjAdMat k (B * C) (C' * B') := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun c => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, adjAdMat_mulVec,
    adjAdMat_mulVec, adjAdMat_mulVec, adjAd_comp k B B' C C' h]

omit [CharP k 2] in
theorem adjAdMat_one : adjAdMat k 1 1 = 1 := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun c => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, adjAdMat_mulVec, adjAd_one, Matrix.one_mulVec]

theorem adjEnd_conj (i : ℕ) (A : GL (Fin 3) F) (g : SL(3, F)) (c : Fin 8 → k) :
    adjEnd k i (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A g)
        c =
      adjAd k (twistGL k i A.val) (twistGL k i (A⁻¹).val)
        (adjEnd k i g (adjAd k (twistGL k i (A⁻¹).val) (twistGL k i A.val) c)) := by
  have h1 : twistGL k i A.val * twistGL k i (A⁻¹).val = 1 := twistGL_mul_inv k i A
  have h2 : twistGL k i (A⁻¹).val * twistGL k i A.val = 1 := twistGL_inv_mul k i A
  have hinv : twistMat k i
      ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A g)⁻¹) =
      twistGL k i A.val * twistMat k i g⁻¹ * twistGL k i (A⁻¹).val := by
    rw [← map_inv, twistMat_conj]
  have hX1 : Xm (adjAd k (twistGL k i (A⁻¹).val) (twistGL k i A.val) c) =
      twistGL k i (A⁻¹).val * Xm c * twistGL k i A.val := by
    rw [adjAd_apply, Xm_co k (by rw [trace_conj_eq k _ _ _ h1]; exact trace_Xm k c)]
  have hX2 : Xm (adjEnd k i g (adjAd k (twistGL k i (A⁻¹).val) (twistGL k i A.val) c)) =
      conjMat k i g (twistGL k i (A⁻¹).val * Xm c * twistGL k i A.val) := by
    rw [adjEnd_apply, hX1, Xm_co k (by
      rw [trace_conjMat, trace_conj_eq k _ _ _ h1]; exact trace_Xm k c)]
  rw [adjEnd_apply, conjMat, hinv, twistMat_conj, adjAd_apply, hX2, conjMat]
  congr 1
  simp only [Matrix.mul_assoc]

end Adj

section Local

variable {F : Type} [Field F] (k : Type) [Field k] [Algebra F k] [CharP k 2] {f : ℕ}

@[expose] noncomputable def locConjP (A : GL (Fin 3) F) :
    (a b : Bool) → ℕ → Matrix (Fin (locDim a b)) (Fin (locDim a b)) k
  | false, false => fun _ => 1
  | true, false => fun i => twistGL k i (A⁻¹).val
  | false, true => fun i => (twistGL k i A.val)ᵀ
  | true, true => fun i => adjAdMat k (twistGL k i (A⁻¹).val) (twistGL k i A.val)

@[expose] noncomputable def locConjQ (A : GL (Fin 3) F) :
    (a b : Bool) → ℕ → Matrix (Fin (locDim a b)) (Fin (locDim a b)) k
  | false, false => fun _ => 1
  | true, false => fun i => twistGL k i A.val
  | false, true => fun i => (twistGL k i (A⁻¹).val)ᵀ
  | true, true => fun i => adjAdMat k (twistGL k i A.val) (twistGL k i (A⁻¹).val)

theorem locConjP_mul_Q (A : GL (Fin 3) F) (a b : Bool) (i : ℕ) :
    locConjP k A a b i * locConjQ k A a b i = 1 := by
  cases a <;> cases b
  · exact Matrix.one_mul (1 : Matrix (Fin 1) (Fin 1) k)
  · show (twistGL k i A.val)ᵀ * (twistGL k i (A⁻¹).val)ᵀ = 1
    rw [← Matrix.transpose_mul, twistGL_inv_mul k i A, Matrix.transpose_one]
  · exact twistGL_inv_mul k i A
  · show adjAdMat k (twistGL k i (A⁻¹).val) (twistGL k i A.val) *
      adjAdMat k (twistGL k i A.val) (twistGL k i (A⁻¹).val) = 1
    rw [adjAdMat_mul k _ _ _ _ (twistGL_inv_mul k i A), twistGL_inv_mul k i A, adjAdMat_one]

theorem locConjQ_mul_P (A : GL (Fin 3) F) (a b : Bool) (i : ℕ) :
    locConjQ k A a b i * locConjP k A a b i = 1 := by
  cases a <;> cases b
  · exact Matrix.one_mul (1 : Matrix (Fin 1) (Fin 1) k)
  · show (twistGL k i (A⁻¹).val)ᵀ * (twistGL k i A.val)ᵀ = 1
    rw [← Matrix.transpose_mul, twistGL_mul_inv k i A, Matrix.transpose_one]
  · exact twistGL_mul_inv k i A
  · show adjAdMat k (twistGL k i A.val) (twistGL k i (A⁻¹).val) *
      adjAdMat k (twistGL k i (A⁻¹).val) (twistGL k i A.val) = 1
    rw [adjAdMat_mul k _ _ _ _ (twistGL_mul_inv k i A), twistGL_mul_inv k i A, adjAdMat_one]

theorem locConjP_comm (A : GL (Fin 3) F) (a b : Bool) (i : ℕ) (g : SL(3, F)) :
    locConjP k A a b i * locRep k a b i
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A g) =
      locRep k a b i g * locConjP k A a b i := by
  have h1 : twistGL k i A.val * twistGL k i (A⁻¹).val = 1 := twistGL_mul_inv k i A
  have h2 : twistGL k i (A⁻¹).val * twistGL k i A.val = 1 := twistGL_inv_mul k i A
  cases a <;> cases b
  · rw [locRep_ff]
    simp [locConjP]
  · show (twistGL k i A.val)ᵀ * dualRep k i
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A g) =
      dualRep k i g * (twistGL k i A.val)ᵀ
    have h3 : (twistGL k i A.val)ᵀ * (twistGL k i (A⁻¹).val)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, h2, Matrix.transpose_one]
    rw [dualRep_apply, dualRep_apply, ← map_inv, twistMat_conj, Matrix.transpose_mul,
      Matrix.transpose_mul, ← Matrix.mul_assoc (twistGL k i A.val)ᵀ, h3, Matrix.one_mul]
  · show twistGL k i (A⁻¹).val * natRep k i
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A g) =
      natRep k i g * twistGL k i (A⁻¹).val
    rw [natRep_apply, natRep_apply, twistMat_conj, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2,
      Matrix.one_mul]
  · show adjAdMat k (twistGL k i (A⁻¹).val) (twistGL k i A.val) * adjRep k i
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A g) =
      adjRep k i g * adjAdMat k (twistGL k i (A⁻¹).val) (twistGL k i A.val)
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun c => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      adjAdMat_mulVec, adjRep_mulVec, adjRep_mulVec, adjAdMat_mulVec, ← adjEnd_apply,
      ← adjEnd_apply, adjEnd_conj, adjAd_comp k _ _ _ _ h2, h2, adjAd_one]

end Local

section Tensor

variable {F : Type} [Field F] (k : Type) [Field k] [Algebra F k] [CharP k 2] {f : ℕ}

theorem tensorRep_comp_conj (A : GL (Fin 3) F) (a b : Fin f → Bool) :
    MatIso ((tensorRep (F := F) k a b).comp
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A).toMonoidHom)
      (tensorRep k a b) (kron fun i : Fin f => locConjP k A (a i) (b i) (i : ℕ))
      (kron fun i : Fin f => locConjQ k A (a i) (b i) (i : ℕ)) := by
  refine ⟨?_, ?_, fun g => ?_⟩
  · rw [← kron_mul]
    simp_rw [locConjP_mul_Q]
    exact kron_one
  · rw [← kron_mul]
    simp_rw [locConjQ_mul_P]
    exact kron_one
  · change kron (fun i : Fin f => locConjP k A (a i) (b i) (i : ℕ)) *
      kron (fun i : Fin f => locRep k (a i) (b i) (i : ℕ)
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A g)) =
        kron (fun i : Fin f => locRep k (a i) (b i) (i : ℕ) g) *
          kron (fun i : Fin f => locConjP k A (a i) (b i) (i : ℕ))
    rw [← kron_mul, ← kron_mul]
    congr 1
    funext i
    exact locConjP_comm k A (a i) (b i) (i : ℕ) g

end Tensor

end CFSG.QuasithinUnique.Setup.X7a
