module

public import CFSG.HardMathSupport.GuralnickMalle.ElemAbelianTwoHom
public import Mathlib.LinearAlgebra.TensorProduct.Matrix
public import Mathlib.RingTheory.Flat.Equalizer

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

open Matrix Module
open scoped TensorProduct
open CFSG.HardMathSupport.GuralnickMalle

@[expose] def matFix {k I : Type*} [Field k] [Fintype I] [DecidableEq I] {r : ℕ}
    (T : Fin r → Matrix I I k) : Submodule k (I → k) :=
  ⨅ i, LinearMap.ker (Matrix.toLin' (T i) - LinearMap.id)

theorem mem_matFix {k I : Type*} [Field k] [Fintype I] [DecidableEq I] {r : ℕ}
    (T : Fin r → Matrix I I k) (v : I → k) :
    v ∈ matFix T ↔ ∀ i, T i *ᵥ v = v := by
  simp only [matFix, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, Matrix.toLin'_apply]

@[expose] def matFixStack {F I : Type*} [Field F] [DecidableEq I] {r : ℕ}
    (T : Fin r → Matrix I I F) :
    Matrix (Fin r × I) I F :=
  Matrix.of fun p j => (T p.1 - 1) p.2 j

theorem ker_matFixStack {F I : Type*} [Field F] [Fintype I] [DecidableEq I] {r : ℕ}
    (T : Fin r → Matrix I I F) :
    matFix T = LinearMap.ker (Matrix.mulVecLin (matFixStack T)) := by
  ext v
  rw [mem_matFix, LinearMap.mem_ker]
  have hstack (i : Fin r) (j : I) :
      (Matrix.mulVecLin (matFixStack T) v) (i, j) = ((T i) *ᵥ v) j - v j := by
    change (matFixStack T *ᵥ v) (i, j) = ((T i) *ᵥ v) j - v j
    rw [show (matFixStack T *ᵥ v) (i, j) = ((T i - 1) *ᵥ v) j from rfl,
      Matrix.sub_mulVec, Matrix.one_mulVec]
    simp
  constructor
  · intro h
    funext p
    obtain ⟨i, j⟩ := p
    rw [hstack, congrFun (h i) j, sub_self]
    simp
  · intro h i
    funext j
    have hp := congrFun h (i, j)
    rw [hstack, Pi.zero_apply, sub_eq_zero] at hp
    exact hp

theorem toLin_eq_conj_of_basisEquiv {R : Type*} [CommSemiring R] {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {M N : Type*} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (b : Basis ι R M) (c : Basis ι R N) (A : Matrix ι ι R) (e : M ≃ₗ[R] N)
    (he : ∀ i, e (b i) = c i) :
    Matrix.toLin b b A = e.symm.toLinearMap ∘ₗ Matrix.toLin c c A ∘ₗ e.toLinearMap := by
  apply b.ext
  intro i
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [Matrix.toLin_self b b A i]
  change ∑ j, A j i • b j =
    e.symm (Matrix.toLin c c A (e.toLinearMap (b i)))
  rw [show e.toLinearMap (b i) = c i from he i]
  rw [Matrix.toLin_self c c A i, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, show e.symm (c j) = b j from by
    rw [← he j, LinearEquiv.symm_apply_apply]]

theorem piScalarRight_baseChange_mulVec {F k : Type*} [Field F] [Field k] [Algebra F k]
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n F) (t : k ⊗[F] (n → F)) :
    TensorProduct.piScalarRight F k k m ((Matrix.mulVecLin A).baseChange k t) =
      A.map (algebraMap F k) *ᵥ TensorProduct.piScalarRight F k k n t := by
  classical
  have htmul_m : ∀ (a : k) (x : m → F),
      TensorProduct.piScalarRight F k k m (a ⊗ₜ[F] x) =
        fun i => algebraMap F k (x i) * a := by
    intro a x
    simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    funext i
    rw [Algebra.smul_def]
  have htmul_n : ∀ (a : k) (x : n → F),
      TensorProduct.piScalarRight F k k n (a ⊗ₜ[F] x) =
        fun i => algebraMap F k (x i) * a := by
    intro a x
    simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    funext i
    rw [Algebra.smul_def]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t₁ t₂ h₁ h₂ =>
      rw [map_add, map_add, map_add, h₁, h₂, Matrix.mulVec_add]
  | tmul a x =>
      rw [LinearMap.baseChange_tmul, htmul_m, htmul_n]
      ext i
      simp only [Matrix.mulVecLin_apply]
      rw [RingHom.map_mulVec (algebraMap F k) A x i]
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Function.comp_apply,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

theorem finrank_matFix_kronecker_le {k I J : Type*} [Field k] [CharP k 2] [Fintype I]
    [DecidableEq I] [Fintype J] [DecidableEq J] {r : ℕ} (T : Fin r → Matrix I I k)
    (U : Fin r → Matrix J J k)
    (hT2 : ∀ i, T i * T i = 1) (hTc : ∀ i j, T i * T j = T j * T i)
    (hU2 : ∀ i, U i * U i = 1) (hUc : ∀ i j, U i * U j = U j * U i) :
    finrank k (matFix fun i => Matrix.kroneckerMap (· * ·) (T i) (U i)) ≤
      finrank k (matFix T) * Fintype.card J := by
  classical
  let T' : Fin r → (I → k) ≃ₗ[k] (I → k) := fun i =>
    LinearEquiv.ofLinearMap (Matrix.toLin' (T i)) (Matrix.toLin' (T i))
      (by
        apply LinearMap.ext
        intro v
        rw [LinearMap.comp_apply, ← Matrix.toLin'_mul_apply, hT2 i, Matrix.toLin'_one])
      (by
        apply LinearMap.ext
        intro v
        rw [LinearMap.comp_apply, ← Matrix.toLin'_mul_apply, hT2 i, Matrix.toLin'_one])
  let U' : Fin r → (J → k) ≃ₗ[k] (J → k) := fun i =>
    LinearEquiv.ofLinearMap (Matrix.toLin' (U i)) (Matrix.toLin' (U i))
      (by
        apply LinearMap.ext
        intro v
        rw [LinearMap.comp_apply, ← Matrix.toLin'_mul_apply, hU2 i, Matrix.toLin'_one])
      (by
        apply LinearMap.ext
        intro v
        rw [LinearMap.comp_apply, ← Matrix.toLin'_mul_apply, hU2 i, Matrix.toLin'_one])
  have hT'2 : ∀ i, T' i * T' i = 1 := by
    intro i
    apply LinearEquiv.ext
    intro v
    simp only [LinearEquiv.mul_apply, LinearEquiv.one_eq_refl, LinearEquiv.refl_apply]
    simp only [T', LinearEquiv.coe_ofLinearMap]
    rw [← Matrix.toLin'_mul_apply, hT2 i, Matrix.toLin'_one]
    rfl
  have hT'c : ∀ i j, T' i * T' j = T' j * T' i := by
    intro i j
    apply LinearEquiv.ext
    intro v
    simp only [LinearEquiv.mul_apply]
    simp only [T', LinearEquiv.coe_ofLinearMap]
    simp only [← Matrix.toLin'_mul_apply]
    rw [hTc i j]
  have hU'2 : ∀ i, U' i * U' i = 1 := by
    intro i
    apply LinearEquiv.ext
    intro v
    simp only [LinearEquiv.mul_apply, LinearEquiv.one_eq_refl, LinearEquiv.refl_apply]
    simp only [U', LinearEquiv.coe_ofLinearMap]
    rw [← Matrix.toLin'_mul_apply, hU2 i, Matrix.toLin'_one]
    rfl
  have hU'c : ∀ i j, U' i * U' j = U' j * U' i := by
    intro i j
    apply LinearEquiv.ext
    intro v
    simp only [LinearEquiv.mul_apply]
    simp only [U', LinearEquiv.coe_ofLinearMap]
    simp only [← Matrix.toLin'_mul_apply]
    rw [hUc i j]
  let b : Basis (I × J) k ((I → k) ⊗[k] (J → k)) :=
    (Pi.basisFun k I).tensorProduct (Pi.basisFun k J)
  let e : ((I → k) ⊗[k] (J → k)) ≃ₗ[k] (I × J → k) :=
    b.equiv (Pi.basisFun k (I × J)) (Equiv.refl (I × J))
  have he : ∀ p : I × J, e (b p) = Pi.basisFun k (I × J) p := by
    intro p
    simp [e]
  have hconj : ∀ i : Fin r,
      Matrix.toLin' (Matrix.kroneckerMap (· * ·) (T i) (U i)) =
        e.toLinearMap ∘ₗ TensorProduct.map (T' i : (I → k) →ₗ[k] (I → k))
          (U' i : (J → k) →ₗ[k] (J → k)) ∘ₗ e.symm.toLinearMap := by
    intro i
    have hb : Matrix.toLin b b (Matrix.kroneckerMap (· * ·) (T i) (U i)) =
        TensorProduct.map (T' i : (I → k) →ₗ[k] (I → k))
          (U' i : (J → k) →ₗ[k] (J → k)) := by
      simpa [b, Matrix.toLin_eq_toLin', T', U', LinearEquiv.coe_ofLinearMap] using
        (Matrix.toLin_kronecker (R := k)
          (bM := Pi.basisFun k I) (bN := Pi.basisFun k J)
          (bM' := Pi.basisFun k I) (bN' := Pi.basisFun k J) (T i) (U i))
    have hbc := toLin_eq_conj_of_basisEquiv b (Pi.basisFun k (I × J))
      (Matrix.kroneckerMap (· * ·) (T i) (U i)) e he
    rw [hb, Matrix.toLin_eq_toLin'] at hbc
    calc
      Matrix.toLin' (Matrix.kroneckerMap (· * ·) (T i) (U i)) =
          e.toLinearMap ∘ₗ
            (e.symm.toLinearMap ∘ₗ
              Matrix.toLin' (Matrix.kroneckerMap (· * ·) (T i) (U i)) ∘ₗ
                e.toLinearMap) ∘ₗ e.symm.toLinearMap := by
            ext x
            simp
      _ = e.toLinearMap ∘ₗ TensorProduct.map (T' i : (I → k) →ₗ[k] (I → k))
            (U' i : (J → k) →ₗ[k] (J → k)) ∘ₗ e.symm.toLinearMap := by
            rw [← hbc]
  have hfix : Submodule.map e.toLinearMap (tensorFixed T' U') =
      matFix (fun i => Matrix.kroneckerMap (· * ·) (T i) (U i)) := by
    ext y
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [mem_matFix]
      intro i
      have hxmem : TensorProduct.map (T' i : (I → k) →ₗ[k] (I → k))
          (U' i : (J → k) →ₗ[k] (J → k)) x = x := by
        have hxall : ∀ i, x ∈ LinearMap.ker
            (TensorProduct.map (T' i : (I → k) →ₗ[k] (I → k))
              (U' i : (J → k) →ₗ[k] (J → k)) - 1) := by
          simpa [tensorFixed, Submodule.mem_iInf] using hx
        have h := hxall i
        simpa [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] using h
      have hc := congrFun (congrArg DFunLike.coe (hconj i)) (e x)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        LinearEquiv.symm_apply_apply, hxmem] at hc
      simpa [Matrix.toLin'_apply] using hc
    · intro hy
      rw [mem_matFix] at hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      rw [tensorFixed, Submodule.mem_iInf]
      intro i
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
      have hc := congrFun (congrArg DFunLike.coe (hconj i)) y
      simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at hc
      rw [Matrix.toLin'_apply, hy i] at hc
      have hc' := congrArg e.symm hc
      simpa using hc'.symm
  have hL : finrank k (tensorFixed T' U') =
      finrank k (matFix fun i => Matrix.kroneckerMap (· * ·) (T i) (U i)) := by
    rw [← hfix, LinearEquiv.finrank_map_eq]
  have hiter : iterFixed T' r = matFix T := by
    ext v
    rw [mem_iterFixed, mem_matFix]
    constructor
    · intro h i
      simpa [T', LinearEquiv.coe_ofLinearMap, Matrix.toLin'_apply] using h i i.2
    · intro h i hi
      simpa [T', LinearEquiv.coe_ofLinearMap, Matrix.toLin'_apply] using h i
  have hmain := finrank_fixed_tensor_le_zm_elemAbelian (K := k) (V := I → k) (W := J → k)
    T' U' hT'2 hT'c hU'2 hU'c
  rw [hL, hiter, Module.finrank_fintype_fun_eq_card] at hmain
  exact hmain

theorem finrank_matFix_map {F k I : Type*} [Field F] [Field k] [Fintype I] [DecidableEq I]
    (φ : F →+* k) {r : ℕ} (T : Fin r → Matrix I I F) :
    finrank k (matFix fun i => (T i).map φ) = finrank F (matFix T) := by
  classical
  let : Algebra F k := φ.toAlgebra
  have : Module.Free F k := Module.Free.of_divisionRing F k
  have : Module.Flat F k := Module.Flat.of_free
  let f : (I → F) →ₗ[F] (Fin r × I → F) := Matrix.mulVecLin (matFixStack T)
  let g : (I → k) →ₗ[k] (Fin r × I → k) := Matrix.mulVecLin ((matFixStack T).map φ)
  have hfix : matFix T = LinearMap.ker f := by
    simpa [f] using ker_matFixStack T
  have hstack_map : (matFixStack T).map φ = matFixStack (fun i => (T i).map φ) := by
    ext p j
    obtain ⟨i, x⟩ := p
    by_cases h : x = j <;> simp [matFixStack, Matrix.map_apply, Matrix.one_apply, h]
  have hfixK : matFix (fun i => (T i).map φ) = LinearMap.ker g := by
    simpa [g, ← hstack_map] using ker_matFixStack (F := k) (fun i => (T i).map φ)
  let eI : k ⊗[F] (I → F) ≃ₗ[k] (I → k) := TensorProduct.piScalarRight F k k I
  let eP : k ⊗[F] (Fin r × I → F) ≃ₗ[k] (Fin r × I → k) :=
    TensorProduct.piScalarRight F k k (Fin r × I)
  have hbase : ∀ t : k ⊗[F] (I → F), eP (f.baseChange k t) = g (eI t) := by
    intro t
    have h := piScalarRight_baseChange_mulVec (F := F) (k := k) (m := Fin r × I) (n := I)
      (matFixStack T) t
    simpa [f, g, eP, eI, RingHom.algebraMap_toAlgebra] using h
  have hker : LinearMap.ker g = (LinearMap.ker (f.baseChange k)).map eI.toLinearMap := by
    ext y
    rw [LinearMap.mem_ker, Submodule.mem_map_equiv, LinearMap.mem_ker]
    have h := hbase (eI.symm y)
    rw [eI.apply_symm_apply] at h
    rw [← h, eP.map_eq_zero_iff]
  have hfinrank : finrank k (LinearMap.ker (f.baseChange k)) = finrank F (LinearMap.ker f) := by
    rw [show LinearMap.ker (f.baseChange k) =
        LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor k k f) from rfl]
    rw [← (LinearMap.tensorKerEquiv k k f).finrank_eq, Module.finrank_baseChange]
  rw [hfixK, hker, LinearEquiv.finrank_map_eq, hfinrank, hfix]

end CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
