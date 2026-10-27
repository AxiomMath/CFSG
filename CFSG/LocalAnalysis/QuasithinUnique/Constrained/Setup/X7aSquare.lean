module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aDual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bFlag
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped MatrixGroups Matrix

open Matrix
open CFSG.QuasithinUnique.Setup.X7 (matRep)

section MatrixLevel

variable {k : Type} [Field k]

@[expose] def actL3 (H : Matrix (Fin 3) (Fin 3) k) :
    Matrix (Fin 3) (Fin 3) k →ₗ[k] Matrix (Fin 3) (Fin 3) k where
  toFun X := H * X * Hᵀ
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp

theorem actL3_apply (H X : Matrix (Fin 3) (Fin 3) k) : actL3 H X = H * X * Hᵀ := rfl

@[expose] def crossL3 (k : Type) [Field k] : Matrix (Fin 3) (Fin 3) k →ₗ[k] (Fin 3 → k) where
  toFun X := ![X 1 2, X 0 2, X 0 1]
  map_add' X Y := by
    ext i
    fin_cases i <;> rfl
  map_smul' c X := by
    ext i
    fin_cases i <;> rfl

@[expose] def diagL3 (k : Type) [Field k] : Matrix (Fin 3) (Fin 3) k →ₗ[k] (Fin 3 → k) where
  toFun X := fun i => X i i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[expose] def pMap3 (k : Type) [Field k] : Matrix (Fin 3) (Fin 3) k →ₗ[k] Matrix (Fin 3) (Fin 3) k where
  toFun X := X + Xᵀ
  map_add' X Y := by
    rw [Matrix.transpose_add]
    abel
  map_smul' c X := by
    rw [Matrix.transpose_smul, smul_add]
    rfl

theorem crossL3_apply (X : Matrix (Fin 3) (Fin 3) k) : crossL3 k X = ![X 1 2, X 0 2, X 0 1] := rfl

theorem diagL3_apply (X : Matrix (Fin 3) (Fin 3) k) (i : Fin 3) : diagL3 k X i = X i i := rfl

theorem pMap3_apply (X : Matrix (Fin 3) (Fin 3) k) : pMap3 k X = X + Xᵀ := rfl

@[expose] def symSub3 (k : Type) [Field k] : Submodule k (Matrix (Fin 3) (Fin 3) k) :=
  LinearMap.ker (pMap3 k)

@[expose] def altSub3 (k : Type) [Field k] : Submodule k (Matrix (Fin 3) (Fin 3) k) :=
  symSub3 k ⊓ LinearMap.ker (diagL3 k)

variable [CharP k 2]

theorem mem_symSub3 {X : Matrix (Fin 3) (Fin 3) k} : X ∈ symSub3 k ↔ ∀ i j, X j i = X i j := by
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    simp only [pMap3_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.zero_apply] at this
    exact (CharTwo.add_eq_zero.mp this).symm
  · intro h
    show X + Xᵀ = 0
    ext i j
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.zero_apply]
    rw [h i j]
    exact CharTwo.add_self_eq_zero _

theorem mem_altSub3 {X : Matrix (Fin 3) (Fin 3) k} :
    X ∈ altSub3 k ↔ (∀ i j, X j i = X i j) ∧ ∀ i, X i i = 0 := by
  rw [altSub3, Submodule.mem_inf, mem_symSub3]
  simp only [LinearMap.mem_ker]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i => congrFun h2 i⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, funext h2⟩

theorem conj_diag3_apply (H X : Matrix (Fin 3) (Fin 3) k) (hX : ∀ i j, X j i = X i j) (a : Fin 3) :
    (H * X * Hᵀ) a a = H a 0 ^ 2 * X 0 0 + H a 1 ^ 2 * X 1 1 + H a 2 ^ 2 * X 2 2 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, hX 0 1, hX 0 2, hX 1 2]
  linear_combination (H a 0 * H a 1 * X 0 1 + H a 0 * H a 2 * X 0 2 + H a 1 * H a 2 * X 1 2) * h2

theorem conj_cross3 (H X : Matrix (Fin 3) (Fin 3) k) (hX : ∀ i j, X j i = X i j)
    (hd : ∀ i, X i i = 0) :
    crossL3 k (H * X * Hᵀ) = (H.adjugate)ᵀ *ᵥ crossL3 k X := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  funext i
  fin_cases i
  · simp only [crossL3_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, hd,
      hX 0 1, hX 0 2, hX 1 2, Matrix.mulVec, dotProduct, Matrix.adjugate_fin_three]
    simp
    linear_combination (X 0 1 * H 1 1 * H 2 0 + X 0 2 * H 1 0 * H 2 2 + X 1 2 * H 1 2 * H 2 1) * h2
  · simp only [crossL3_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, hd,
      hX 0 1, hX 0 2, hX 1 2, Matrix.mulVec, dotProduct, Matrix.adjugate_fin_three]
    simp
    linear_combination (X 0 1 * H 0 0 * H 2 1 + X 0 2 * H 0 2 * H 2 0 + X 1 2 * H 0 1 * H 2 2) * h2
  · simp only [crossL3_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, hd,
      hX 0 1, hX 0 2, hX 1 2, Matrix.mulVec, dotProduct, Matrix.adjugate_fin_three]
    simp
    linear_combination (X 0 1 * H 0 1 * H 1 0 + X 0 2 * H 0 0 * H 1 2 + X 1 2 * H 0 2 * H 1 1) * h2

end MatrixLevel

section Invariance

variable {k : Type} [Field k] {H : Matrix (Fin 3) (Fin 3) k}

theorem pMap3_actL3 (H X : Matrix (Fin 3) (Fin 3) k) :
    pMap3 k (actL3 H X) = actL3 H (pMap3 k X) := by
  simp only [pMap3_apply, actL3_apply, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

theorem actL3_mem_symSub3 {X : Matrix (Fin 3) (Fin 3) k} (hX : X ∈ symSub3 k) :
    actL3 H X ∈ symSub3 k := by
  have h : pMap3 k X = 0 := hX
  show pMap3 k (actL3 H X) = 0
  rw [pMap3_actL3, h, map_zero]

variable [CharP k 2]

theorem actL3_mem_altSub3 {X : Matrix (Fin 3) (Fin 3) k} (hX : X ∈ altSub3 k) :
    actL3 H X ∈ altSub3 k := by
  obtain ⟨hs, hd⟩ := mem_altSub3.mp hX
  have hs' := mem_symSub3.mp (actL3_mem_symSub3 (H := H) (mem_symSub3.mpr hs))
  refine mem_altSub3.mpr ⟨hs', fun i => ?_⟩
  rw [actL3_apply, conj_diag3_apply H X hs i, hd 0, hd 1, hd 2]
  ring

theorem pMap3_mem_altSub3 (X : Matrix (Fin 3) (Fin 3) k) : pMap3 k X ∈ altSub3 k := by
  refine mem_altSub3.mpr ⟨fun i j => ?_, fun i => ?_⟩
  · simp only [pMap3_apply, Matrix.add_apply, Matrix.transpose_apply]
    ring
  · simp only [pMap3_apply, Matrix.add_apply, Matrix.transpose_apply]
    exact CharTwo.add_self_eq_zero _

theorem eqv0 (hdet : H.det = 1) {X : Matrix (Fin 3) (Fin 3) k} (hX : X ∈ altSub3 k) :
    crossL3 k (actL3 H X) = (H⁻¹)ᵀ *ᵥ crossL3 k X := by
  obtain ⟨hs, hd⟩ := mem_altSub3.mp hX
  have hinv : H⁻¹ = H.adjugate := by
    rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  rw [hinv, actL3_apply]
  exact conj_cross3 H X hs hd

theorem eqv1 {X : Matrix (Fin 3) (Fin 3) k} (hX : X ∈ symSub3 k) :
    diagL3 k (actL3 H X) = (H.map fun x => x ^ 2) *ᵥ diagL3 k X := by
  have hs := mem_symSub3.mp hX
  funext a
  rw [diagL3_apply, actL3_apply, conj_diag3_apply H X hs a]
  simp only [Matrix.mulVec, dotProduct, diagL3_apply, Fin.sum_univ_three, Matrix.map_apply]

theorem eqv2 (hdet : H.det = 1) (X : Matrix (Fin 3) (Fin 3) k) :
    crossL3 k (pMap3 k (actL3 H X)) = (H⁻¹)ᵀ *ᵥ crossL3 k (pMap3 k X) := by
  rw [pMap3_actL3]
  exact eqv0 hdet (pMap3_mem_altSub3 X)

end Invariance

section KerSurj

variable {k : Type} [Field k] [CharP k 2]

theorem ker0 {X : Matrix (Fin 3) (Fin 3) k} (hX : X ∈ altSub3 k) :
    crossL3 k X = 0 ↔ X ∈ (⊥ : Submodule k (Matrix (Fin 3) (Fin 3) k)) := by
  obtain ⟨hs, hd⟩ := mem_altSub3.mp hX
  rw [Submodule.mem_bot]
  constructor
  · intro h
    have h0 : X 1 2 = 0 := congrFun h 0
    have h1 : X 0 2 = 0 := congrFun h 1
    have h2 : X 0 1 = 0 := congrFun h 2
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hd, h0, h1, h2, hs 0 1, hs 0 2, hs 1 2]
  · intro h
    rw [h]
    funext i
    fin_cases i <;> simp [crossL3_apply]

theorem surj0 (y : Fin 3 → k) : ∃ X ∈ altSub3 k, crossL3 k X = y := by
  refine ⟨!![0, y 2, y 1; y 2, 0, y 0; y 1, y 0, 0], ?_, ?_⟩
  · refine mem_altSub3.mpr ⟨fun i j => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp
    · fin_cases i <;> simp
  · funext i
    fin_cases i <;> simp [crossL3_apply]

omit [CharP k 2] in
theorem ker1 {X : Matrix (Fin 3) (Fin 3) k} (hX : X ∈ symSub3 k) :
    diagL3 k X = 0 ↔ X ∈ altSub3 k := by
  rw [altSub3, Submodule.mem_inf]
  simp only [LinearMap.mem_ker]
  exact ⟨fun h => ⟨hX, h⟩, fun h => h.2⟩

theorem surj1 (y : Fin 3 → k) : ∃ X ∈ symSub3 k, diagL3 k X = y := by
  refine ⟨Matrix.diagonal y, mem_symSub3.mpr fun i j => ?_, ?_⟩
  · by_cases h : i = j
    · subst h
      rfl
    · simp [h, Ne.symm h]
  · funext i
    simp [diagL3_apply]

theorem ker2 (X : Matrix (Fin 3) (Fin 3) k) :
    crossL3 k (pMap3 k X) = 0 ↔ X ∈ symSub3 k := by
  constructor
  · intro h
    have := (ker0 (pMap3_mem_altSub3 X)).mp h
    exact this
  · intro h
    have h0 : pMap3 k X = 0 := h
    rw [h0, map_zero]

omit [CharP k 2] in
theorem surj2 (y : Fin 3 → k) : ∃ X ∈ (⊤ : Submodule k (Matrix (Fin 3) (Fin 3) k)),
    crossL3 k (pMap3 k X) = y := by
  refine ⟨!![0, y 2, y 1; 0, 0, y 0; 0, 0, 0], Submodule.mem_top, ?_⟩
  funext i
  fin_cases i <;> simp [crossL3_apply, pMap3_apply]

end KerSurj

section Rep

open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply dualMat dualMat_apply)
open CFSG.QuasithinUnique.Setup.X7b (FRep FlagTop Chain flagTop_of_chain)

variable {G : Type} [Group G] {k : Type} [Field k] [CharP k 2]

@[expose] noncomputable def sqRep3 (R : G →* Matrix (Fin 3) (Fin 3) k) :
    Representation k G (Matrix (Fin 3) (Fin 3) k) where
  toFun g := actL3 (R g)
  map_one' := by
    refine LinearMap.ext fun X => ?_
    simp [actL3_apply]
  map_mul' g h := by
    refine LinearMap.ext fun X => ?_
    simp [actL3_apply, map_mul, Matrix.transpose_mul, Matrix.mul_assoc]

@[expose] noncomputable def frobMat3 (R : G →* Matrix (Fin 3) (Fin 3) k) :
    G →* Matrix (Fin 3) (Fin 3) k :=
  matMap (iterateFrobenius k 2 1) R

theorem frobMat3_apply (R : G →* Matrix (Fin 3) (Fin 3) k) (g : G) :
    frobMat3 R g = (R g).map fun x => x ^ 2 := by
  ext a b
  simp [frobMat3, matMap_apply, frobenius_def]

omit [CharP k 2] in
theorem inv_eq_of_det_one (R : G →* Matrix (Fin 3) (Fin 3) k) (g : G) :
    (R g)⁻¹ = R g⁻¹ :=
  Matrix.inv_eq_right_inv (by rw [← map_mul, mul_inv_cancel, map_one])

@[expose] noncomputable def sqQ3 (R : G →* Matrix (Fin 3) (Fin 3) k) : Fin 3 → FRep k G :=
  fun s => ⟨Fin 3 → k, matRep (![dualMat R, frobMat3 R, dualMat R] s)⟩

@[expose] noncomputable def sqPhi3 (k : Type) [Field k] :
    Fin 3 → (Matrix (Fin 3) (Fin 3) k →ₗ[k] (Fin 3 → k)) :=
  ![crossL3 k, diagL3 k, crossL3 k ∘ₗ pMap3 k]

noncomputable def sqChainData3 (R : G →* Matrix (Fin 3) (Fin 3) k) (hdet : ∀ g, (R g).det = 1) :
    Chain (sqRep3 R) (sqQ3 R) where
  W := ![⊥, altSub3 k, symSub3 k, ⊤]
  inv := by
    intro s g x hx
    show actL3 (R g) x ∈ _
    fin_cases s
    · have h0 : x = 0 := hx
      show actL3 (R g) x ∈ (⊥ : Submodule k (Matrix (Fin 3) (Fin 3) k))
      rw [h0, map_zero]
      exact Submodule.zero_mem _
    · exact actL3_mem_altSub3 hx
    · exact actL3_mem_symSub3 hx
    · exact Submodule.mem_top
  bot := rfl
  top := rfl
  mono := by
    intro s
    fin_cases s
    · exact bot_le
    · exact inf_le_left
    · exact le_top
  φ := sqPhi3 k
  surj := by
    intro s y
    fin_cases s
    · exact surj0 (k := k) y
    · exact surj1 (k := k) y
    · exact surj2 (k := k) y
  ker := by
    intro s x hx
    fin_cases s
    · exact ker0 (k := k) hx
    · exact ker1 (k := k) hx
    · exact ker2 (k := k) x
  comm := by
    intro s g x hx
    fin_cases s
    · show crossL3 k (actL3 (R g) x) = (matRep (dualMat R) g) (crossL3 k x)
      rw [matRep_apply, dualMat_apply, ← inv_eq_of_det_one R g]
      exact eqv0 (hdet g) hx
    · show diagL3 k (actL3 (R g) x) = (matRep (frobMat3 R) g) (diagL3 k x)
      rw [matRep_apply, frobMat3_apply]
      exact eqv1 hx
    · show crossL3 k (pMap3 k (actL3 (R g) x)) = (matRep (dualMat R) g) (crossL3 k (pMap3 k x))
      rw [matRep_apply, dualMat_apply, ← inv_eq_of_det_one R g]
      exact eqv2 (hdet g) x

omit [CharP k 2] in
theorem actL3_vecMulVec (H : Matrix (Fin 3) (Fin 3) k) (w v : Fin 3 → k) :
    actL3 H (Matrix.vecMulVec w v) = Matrix.vecMulVec (H *ᵥ w) (H *ᵥ v) := by
  rw [actL3_apply, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

@[expose] noncomputable def sqEquiv3 (R : G →* Matrix (Fin 3) (Fin 3) k) :
    Representation.Equiv (Representation.tprod (matRep R) (matRep R)) (sqRep3 R) :=
  Representation.Equiv.mk (TensorProduct.piScalarRight k k (Fin 3 → k) (Fin 3)) (fun g => by
    refine TensorProduct.ext' fun v w => ?_
    simp only [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul]
    show Matrix.vecMulVec ((R g).mulVec w) ((R g).mulVec v) =
      actL3 (R g) (Matrix.vecMulVec w v)
    rw [actL3_vecMulVec])

theorem sq_filtration3 (R : G →* Matrix (Fin 3) (Fin 3) k) (hdet : ∀ g, (R g).det = 1) :
    FlagTop (Representation.tprod (matRep R) (matRep R))
      [⟨Fin 3 → k, matRep (dualMat R)⟩, ⟨Fin 3 → k, matRep (frobMat3 R)⟩,
        ⟨Fin 3 → k, matRep (dualMat R)⟩] := by
  have h := flagTop_of_chain 3 (sqRep3 R) (sqQ3 R) (sqChainData3 R hdet)
  have hl : (List.ofFn (sqQ3 R)).reverse = [⟨Fin 3 → k, matRep (dualMat R)⟩,
      ⟨Fin 3 → k, matRep (frobMat3 R)⟩, ⟨Fin 3 → k, matRep (dualMat R)⟩] := by
    simp [sqQ3, List.ofFn_succ]
  rw [hl] at h
  exact CFSG.QuasithinUnique.Setup.X7b.FlagTop.congr _ (sqEquiv3 R).symm h

end Rep

section Specialize

open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply dualMat dualMat_apply
  dualMat_dualMat)
open CFSG.QuasithinUnique.Setup.X7b (FRep FlagTop Chain flagTop_of_chain)

variable {F : Type} [Field F] (k : Type) [Field k] [Algebra F k] [CharP k 2]

theorem twistMat_succ (i : ℕ) (g : SL(3, F)) :
    twistMat k (i + 1) g = (twistMat k i g).map fun x => x ^ 2 := by
  ext a b
  simp [twistMat_apply, frK_apply, pow_succ, pow_mul]

theorem natRep_det (i : ℕ) (g : SL(3, F)) : (natRep k i g).det = 1 := by
  rw [natRep_apply]
  exact twistMat_det k i g

theorem dualRep_det (i : ℕ) (g : SL(3, F)) : (dualRep k i g).det = 1 := by
  rw [dualRep_apply, Matrix.det_transpose]
  exact twistMat_det k i g⁻¹

theorem dualMat_natRep (i : ℕ) : dualMat (natRep (F := F) k i) = dualRep k i :=
  MonoidHom.ext fun _ => rfl

theorem dualMat_dualRep (i : ℕ) : dualMat (dualRep (F := F) k i) = natRep k i := by
  rw [← dualMat_natRep, dualMat_dualMat]

theorem frobMat3_natRep (i : ℕ) : frobMat3 (natRep (F := F) k i) = natRep k (i + 1) :=
  MonoidHom.ext fun g => by
    rw [frobMat3_apply]
    exact (twistMat_succ k i g).symm

theorem frobMat3_dualRep (i : ℕ) : frobMat3 (dualRep (F := F) k i) = dualRep k (i + 1) :=
  MonoidHom.ext fun g => by
    rw [frobMat3_apply, dualRep_apply, dualRep_apply, twistMat_succ k i g⁻¹, Matrix.transpose_map]

@[expose] noncomputable def natFRep (i : ℕ) : FRep k SL(3, F) := ⟨Fin 3 → k, matRep (natRep k i)⟩

@[expose] noncomputable def dualFRep (i : ℕ) : FRep k SL(3, F) :=
  ⟨Fin 3 → k, matRep (dualRep k i)⟩

@[expose] noncomputable def adjFRep (i : ℕ) : FRep k SL(3, F) :=
  ⟨Fin 8 → k, matRep (adjRep k i)⟩

@[expose] noncomputable def unitFRep : FRep k SL(3, F) :=
  ⟨Fin 1 → k, matRep (1 : SL(3, F) →* Matrix (Fin 1) (Fin 1) k)⟩

theorem natRep_square_filtration (i : ℕ) :
    FlagTop (Representation.tprod (matRep (natRep (F := F) k i)) (matRep (natRep k i)))
      [dualFRep k i, natFRep k (i + 1), dualFRep k i] := by
  have h := sq_filtration3 (natRep (F := F) k i) (natRep_det k i)
  rw [dualMat_natRep, frobMat3_natRep] at h
  exact h

theorem dualRep_square_filtration (i : ℕ) :
    FlagTop (Representation.tprod (matRep (dualRep (F := F) k i)) (matRep (dualRep k i)))
      [natFRep k i, dualFRep k (i + 1), natFRep k i] := by
  have h := sq_filtration3 (dualRep (F := F) k i) (dualRep_det k i)
  rw [dualMat_dualRep, frobMat3_dualRep] at h
  exact h

end Specialize

section Trace

open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply)
open CFSG.QuasithinUnique.Setup.X7b (FRep FlagTop Chain flagTop_of_chain)

variable {F : Type} [Field F] (k : Type) [Field k] [Algebra F k] [CharP k 2]

@[expose] noncomputable def endRep (i : ℕ) :
    Representation k SL(3, F) (Matrix (Fin 3) (Fin 3) k) where
  toFun g := conjLin k i g
  map_one' := by
    refine LinearMap.ext fun X => ?_
    simp [conjLin_apply, conjMat_one]
  map_mul' g h := by
    refine LinearMap.ext fun X => ?_
    simp [conjLin_apply, conjMat_mul]

@[expose] def trZero3 (k : Type) [Field k] : Submodule k (Matrix (Fin 3) (Fin 3) k) :=
  LinearMap.ker (Matrix.traceLinearMap (Fin 3) k k)

omit [CharP k 2] in
theorem mem_trZero3 {X : Matrix (Fin 3) (Fin 3) k} : X ∈ trZero3 k ↔ X.trace = 0 := by
  simp [trZero3, LinearMap.mem_ker]

@[expose] noncomputable def endQ (i : ℕ) : Fin 2 → FRep k SL(3, F) :=
  ![adjFRep k i, unitFRep k]

@[expose] noncomputable def endPhi (i : ℕ) :
    ∀ s : Fin 2, Matrix (Fin 3) (Fin 3) k →ₗ[k] (endQ (F := F) k i s).V :=
  Fin.cons (coL k) (Fin.cons (LinearMap.pi fun _ : Fin 1 => Matrix.traceLinearMap (Fin 3) k k)
    finZeroElim)

noncomputable def endChainData (i : ℕ) : Chain (endRep (F := F) k i) (endQ k i) where
  W := ![⊥, trZero3 k, ⊤]
  inv := by
    intro s g x hx
    show conjLin k i g x ∈ _
    fin_cases s
    · have h0 : x = 0 := hx
      show conjLin k i g x ∈ (⊥ : Submodule k (Matrix (Fin 3) (Fin 3) k))
      rw [h0, map_zero]
      exact Submodule.zero_mem _
    · have hx' : x.trace = 0 := (mem_trZero3 k).mp hx
      refine (mem_trZero3 k).mpr ?_
      rw [conjLin_apply, trace_conjMat, hx']
    · exact Submodule.mem_top
  bot := rfl
  top := rfl
  mono := by
    intro s
    fin_cases s
    · exact bot_le
    · exact le_top
  φ := endPhi k i
  surj := by
    intro s y
    fin_cases s
    · refine ⟨Xm y, (mem_trZero3 k).mpr (trace_Xm k y), ?_⟩
      exact co_Xm y
    · refine ⟨Matrix.diagonal ![y 0, 0, 0], Submodule.mem_top, ?_⟩
      funext r
      have hr : r = 0 := Subsingleton.elim _ _
      subst hr
      show Matrix.trace (Matrix.diagonal ![y 0, 0, 0]) = y 0
      simp [Matrix.trace, Fin.sum_univ_three]
  ker := by
    intro s x hx
    fin_cases s
    · have hx' : x.trace = 0 := (mem_trZero3 k).mp hx
      show co x = 0 ↔ x ∈ (⊥ : Submodule k (Matrix (Fin 3) (Fin 3) k))
      rw [Submodule.mem_bot]
      constructor
      · intro h
        rw [← Xm_co k hx', h]
        ext a b
        fin_cases a <;> fin_cases b <;> simp [Xm]
      · intro h
        rw [h]
        funext r
        fin_cases r <;> simp [co]
    · show (fun _ : Fin 1 => x.trace) = 0 ↔ x ∈ trZero3 k
      rw [mem_trZero3]
      constructor
      · intro h
        exact congrFun h 0
      · intro h
        funext r
        exact h
  comm := by
    intro s g x hx
    fin_cases s
    · have hx' : x.trace = 0 := (mem_trZero3 k).mp (by simpa using hx)
      show co (conjLin k i g x) = (matRep (adjRep k i) g) (co x)
      rw [matRep_apply, adjRep_mulVec, Xm_co k hx', conjLin_apply]
    · show (fun _ : Fin 1 => (conjLin k i g x).trace) =
        (matRep (1 : SL(3, F) →* Matrix (Fin 1) (Fin 1) k) g) (fun _ : Fin 1 => x.trace)
      rw [conjLin_apply, trace_conjMat, matRep_apply, MonoidHom.one_apply, Matrix.one_mulVec]

@[expose] noncomputable def endEquiv (i : ℕ) :
    Representation.Equiv (Representation.tprod (matRep (dualRep (F := F) k i))
      (matRep (natRep (F := F) k i))) (endRep k i) :=
  Representation.Equiv.mk (TensorProduct.piScalarRight k k (Fin 3 → k) (Fin 3)) (fun g => by
    refine TensorProduct.ext' fun w v => ?_
    simp only [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul]
    show Matrix.vecMulVec ((natRep k i g).mulVec v) ((dualRep k i g).mulVec w) =
      conjLin k i g (Matrix.vecMulVec v w)
    rw [conjLin_apply, conjMat, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, natRep_apply,
      dualRep_apply, Matrix.mulVec_transpose])

theorem trace_flag_dual_nat (i : ℕ) :
    FlagTop (Representation.tprod (matRep (dualRep (F := F) k i)) (matRep (natRep (F := F) k i)))
      [unitFRep k, adjFRep k i] := by
  have h := flagTop_of_chain 2 (endRep (F := F) k i) (endQ k i) (endChainData k i)
  have hl : (List.ofFn (endQ (F := F) k i)).reverse = [unitFRep k, adjFRep k i] := by
    simp [endQ, List.ofFn_succ]
  rw [hl] at h
  exact CFSG.QuasithinUnique.Setup.X7b.FlagTop.congr _ (endEquiv k i).symm h

theorem trace_flag_nat_dual (i : ℕ) :
    FlagTop (Representation.tprod (matRep (natRep (F := F) k i)) (matRep (dualRep (F := F) k i)))
      [unitFRep k, adjFRep k i] :=
  CFSG.QuasithinUnique.Setup.X7b.FlagTop.congr _ (Representation.TensorProduct.comm _ _).symm
    (trace_flag_dual_nat k i)

end Trace

end CFSG.QuasithinUnique.Setup.X7a
