module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityAlternating
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBIsometry

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix CFSG.LocalAnalysis.ComponentInitial FourGroupEvenCanonical UnitaryHigher
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open LinearMap (BilinForm)

variable {K : Type} [Field K] {n : ℕ}

theorem mem_matrixIsometryGroup_iff_inverseTranspose (C g : GL (Fin n) K) :
    g ∈ matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K) ↔
      GeneralLinearGroup.inverseTranspose g = C * g * C⁻¹ := by
  rw [mem_matrixIsometryGroup]
  have hgg : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * g = 1 := Units.inv_mul g
  have hgg' : (g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 := Units.mul_inv g
  have hCC : (C : Matrix (Fin n) (Fin n) K) * ((C⁻¹ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 := Units.mul_inv C
  have hCC' : ((C⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (C : Matrix (Fin n) (Fin n) K) = 1 := Units.inv_mul C
  constructor
  · intro h
    apply Units.ext
    rw [GeneralLinearGroup.coe_inverseTranspose, Units.val_mul, Units.val_mul]
    calc ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ
        _ = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *
            ((g : Matrix (Fin n) (Fin n) K)ᵀ * C * g * ((C⁻¹ : GL (Fin n) K) :
              Matrix (Fin n) (Fin n) K)) := by
          rw [h, hCC, Matrix.mul_one]
        _ = ((g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K))ᵀ * C * g * ((C⁻¹ : GL (Fin n) K) :
              Matrix (Fin n) (Fin n) K) := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [hgg', transpose_one, Matrix.one_mul]
  · intro h
    have h1 := congrArg (fun X : GL (Fin n) K => (X : Matrix (Fin n) (Fin n) K)) h
    simp only [GeneralLinearGroup.coe_inverseTranspose, Units.val_mul] at h1
    calc (g : Matrix (Fin n) (Fin n) K)ᵀ * C * g
        _ = (g : Matrix (Fin n) (Fin n) K)ᵀ * ((C : Matrix (Fin n) (Fin n) K) * g *
            ((C⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * C := by
          simp only [Matrix.mul_assoc, hCC', Matrix.mul_one]
        _ = (g : Matrix (Fin n) (Fin n) K)ᵀ * ((g⁻¹ : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K)ᵀ * C := by rw [← h1]
        _ = C := by rw [← transpose_mul, hgg, transpose_one, Matrix.one_mul]

structure IsCanonicalGram (C : Matrix (Fin n) (Fin n) K) : Prop where
  symm : Cᵀ = C
  sq : C * C = 1
  entries : ∀ i j, C i j = 0 ∨ C i j = 1

theorem isCanonicalGram_one : IsCanonicalGram (1 : Matrix (Fin n) (Fin n) K) :=
  ⟨transpose_one, Matrix.one_mul 1, fun i j => by
    by_cases h : i = j
    · exact Or.inr (by rw [h, one_apply_eq])
    · exact Or.inl (one_apply_ne h)⟩

theorem blockSwapJ_transpose {r : ℕ} :
    (blockSwapJ n r : Matrix (Fin n) (Fin n) K)ᵀ = blockSwapJ n r := by
  ext i j
  simp only [transpose_apply, blockSwapJ, of_apply]
  congr 1
  exact propext or_comm

theorem isCanonicalGram_blockSwapJ [CharP K 2] {r : ℕ} (hr : r + r = n) :
    IsCanonicalGram (blockSwapJ n r : Matrix (Fin n) (Fin n) K) :=
  ⟨blockSwapJ_transpose, blockSwapJ_mul_self hr, fun i j => by
    simp only [blockSwapJ, of_apply]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl⟩

theorem blockSwapJ_apply_self {r : ℕ} (hr : 1 ≤ r) (i : Fin n) :
    (blockSwapJ n r : Matrix (Fin n) (Fin n) K) i i = 0 := by
  simp only [blockSwapJ, of_apply]
  rw [ite_eq_right_iff]
  intro h
  omega

section Canonical

variable {C : GL (Fin n) K} (hC : IsCanonicalGram (C : Matrix (Fin n) (Fin n) K))
include hC

theorem IsCanonicalGram.inv_eq : C⁻¹ = C :=
  inv_eq_of_mul_eq_one_right (Units.ext hC.sq)

theorem IsCanonicalGram.inverseTranspose_eq : GeneralLinearGroup.inverseTranspose C = C := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_inverseTranspose, hC.inv_eq, hC.symm]

theorem IsCanonicalGram.map_eq (φ : K →+* K) : GeneralLinearGroup.map φ C = C :=
  GeneralLinearGroup.ext fun i j => by
    rw [GeneralLinearGroup.map_apply]
    rcases hC.entries i j with h | h
    · rw [h, map_zero]
    · rw [h, map_one]

theorem IsCanonicalGram.mem : C ∈ matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K) := by
  rw [mem_matrixIsometryGroup_iff_inverseTranspose, hC.inverseTranspose_eq, mul_inv_cancel_right]

theorem IsCanonicalGram.matrix_map (φ : K →+* K) :
    (C : Matrix (Fin n) (Fin n) K).map φ = C :=
  congrArg Units.val (hC.map_eq φ)

end Canonical

theorem det_eq_one_of_mem_matrixIsometryGroup [CharP K 2] {C : GL (Fin n) K} {g : GL (Fin n) K}
    (hg : g ∈ matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)) :
    (g : Matrix (Fin n) (Fin n) K).det = 1 := by
  have h1 := congrArg Matrix.det hg
  rw [det_mul, det_mul, det_transpose] at h1
  have hC0 : (C : Matrix (Fin n) (Fin n) K).det ≠ 0 := (Matrix.isUnits_det_units C).ne_zero
  have h2 : (g : Matrix (Fin n) (Fin n) K).det * (g : Matrix (Fin n) (Fin n) K).det = 1 := by
    apply mul_right_cancel₀ hC0
    linear_combination h1
  have h3 : ((g : Matrix (Fin n) (Fin n) K).det - 1) ^ 2 = 0 := by
    have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h2 + (1 - (g : Matrix (Fin n) (Fin n) K).det) * h22
  exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h3)

theorem eq_one_of_scalar_mem_matrixIsometryGroup [CharP K 2] [NeZero n] {C : GL (Fin n) K}
    {c : Kˣ} (hc : GeneralLinearGroup.scalar (Fin n) c ∈
      matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)) : c = 1 := by
  rw [mem_matrixIsometryGroup, GeneralLinearGroup.coe_scalar, scalar_apply,
    diagonal_transpose, ← smul_one_eq_diagonal] at hc
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul] at hc
  have h1 : ((c : K) * c - 1) • (C : Matrix (Fin n) (Fin n) K) = 0 := by
    rw [sub_smul, hc, one_smul, sub_self]
  have hC0 : (C : Matrix (Fin n) (Fin n) K) ≠ 0 := fun h0 => by
    have := Matrix.isUnits_det_units C
    rw [h0, det_zero] at this
    exact not_isUnit_zero this
  have h2 : (c : K) * c - 1 = 0 := (smul_eq_zero.mp h1).resolve_right hC0
  have h3 : ((c : K) - 1) ^ 2 = 0 := by
    have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h2 + (1 - (c : K)) * h22
  exact Units.ext (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h3))

@[expose] def transvMatrix (C : Matrix (Fin n) (Fin n) K) (u : Fin n → K) (s : K) :
    Matrix (Fin n) (Fin n) K :=
  1 + s • vecMulVec u (C *ᵥ u)

theorem vecMulVec_isotropic_sq {C : Matrix (Fin n) (Fin n) K} {u : Fin n → K}
    (hu : u ⬝ᵥ (C *ᵥ u) = 0) :
    vecMulVec u (C *ᵥ u) * vecMulVec u (C *ᵥ u) = 0 := by
  rw [vecMulVec_mul_vecMulVec, dotProduct_comm, hu, zero_smul]
  ext i j
  simp [vecMulVec_apply]

theorem transvMatrix_mul_self [CharP K 2] {C : Matrix (Fin n) (Fin n) K} {u : Fin n → K}
    (hu : u ⬝ᵥ (C *ᵥ u) = 0) (s : K) : transvMatrix C u s * transvMatrix C u s = 1 := by
  simp only [transvMatrix, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, vecMulVec_isotropic_sq hu, smul_zero, add_zero]
  rw [add_assoc, ← two_smul K (s • vecMulVec u (C *ᵥ u)), CharTwo.two_eq_zero, zero_smul,
    add_zero]

@[expose] def transvGL [CharP K 2] (C : Matrix (Fin n) (Fin n) K) {u : Fin n → K}
    (hu : u ⬝ᵥ (C *ᵥ u) = 0) (s : K) : GL (Fin n) K :=
  ⟨transvMatrix C u s, transvMatrix C u s, transvMatrix_mul_self hu s,
    transvMatrix_mul_self hu s⟩

theorem coe_transvGL [CharP K 2] (C : Matrix (Fin n) (Fin n) K) {u : Fin n → K}
    (hu : u ⬝ᵥ (C *ᵥ u) = 0) (s : K) :
    (transvGL C hu s : Matrix (Fin n) (Fin n) K) = transvMatrix C u s := rfl

theorem transvGL_unipotent [CharP K 2] (C : Matrix (Fin n) (Fin n) K) {u : Fin n → K}
    (hu : u ⬝ᵥ (C *ᵥ u) = 0) (s : K) :
    ((transvGL C hu s : Matrix (Fin n) (Fin n) K) - 1) *
      ((transvGL C hu s : Matrix (Fin n) (Fin n) K) - 1) = 0 := by
  rw [coe_transvGL, transvMatrix, add_sub_cancel_left, Matrix.smul_mul, Matrix.mul_smul,
    vecMulVec_isotropic_sq hu, smul_zero, smul_zero]

theorem transvGL_mem [CharP K 2] {C : Matrix (Fin n) (Fin n) K} (hCs : Cᵀ = C)
    {u : Fin n → K} (hu : u ⬝ᵥ (C *ᵥ u) = 0) (s : K) :
    transvGL C hu s ∈ matrixIsometryGroup C := by
  rw [mem_matrixIsometryGroup, coe_transvGL, transvMatrix]
  set N := vecMulVec u (C *ᵥ u) with hN
  set M := vecMulVec (C *ᵥ u) (C *ᵥ u) with hM
  have h1 : Nᵀ * C = M := by
    rw [hN, transpose_vecMulVec, vecMulVec_mul, ← mulVec_transpose, hCs]
  have h2 : C * N = M := mul_vecMulVec _ _ _
  have h3 : M * N = 0 := by
    rw [hM, hN, vecMulVec_mul_vecMulVec, dotProduct_comm, hu, zero_smul]
    ext i j
    simp [vecMulVec_apply]
  have expand : (1 + s • N)ᵀ * C * (1 + s • N) =
      C + s • (Nᵀ * C) + s • (C * N) + (s * s) • (Nᵀ * C * N) := by
    simp only [transpose_add, transpose_one, transpose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul]
    module
  rw [expand, h1, h2, h3, smul_zero, add_zero, add_assoc, ← two_smul K (s • M),
    CharTwo.two_eq_zero, zero_smul, add_zero]

theorem conj_transvGL [CharP K 2] {C g : GL (Fin n) K}
    (hg : g ∈ matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)) {u : Fin n → K}
    (hu : u ⬝ᵥ ((C : Matrix (Fin n) (Fin n) K) *ᵥ u) = 0)
    (hgu : (g : Matrix (Fin n) (Fin n) K) *ᵥ u ⬝ᵥ
      ((C : Matrix (Fin n) (Fin n) K) *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ u)) = 0) (s : K) :
    g * transvGL (C : Matrix (Fin n) (Fin n) K) hu s * g⁻¹ =
      transvGL (C : Matrix (Fin n) (Fin n) K) hgu s := by
  have hinv := (mem_matrixIsometryGroup_iff_inverseTranspose C g).mp hg
  have hinvm : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ =
      (C : Matrix (Fin n) (Fin n) K) * g * ((C⁻¹ : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) := by
    have := congrArg (fun X : GL (Fin n) K => (X : Matrix (Fin n) (Fin n) K)) hinv
    simpa only [GeneralLinearGroup.coe_inverseTranspose, Units.val_mul] using this
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_transvGL, coe_transvGL, transvMatrix, transvMatrix,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.mul_inv, Matrix.mul_smul,
    Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul]
  congr 3
  rw [← mulVec_transpose, hinvm, mulVec_mulVec, Matrix.mul_assoc (_ * _), Units.inv_mul,
    Matrix.mul_one, ← mulVec_mulVec]

theorem eq_of_transvGL_eq [CharP K 2] {C : GL (Fin n) K} {a b : Fin n → K}
    (ha : a ⬝ᵥ ((C : Matrix (Fin n) (Fin n) K) *ᵥ a) = 0)
    (hb : b ⬝ᵥ ((C : Matrix (Fin n) (Fin n) K) *ᵥ b) = 0)
    (h : transvGL (C : Matrix (Fin n) (Fin n) K) ha 1 =
      transvGL (C : Matrix (Fin n) (Fin n) K) hb 1) (hCs : (C : Matrix (Fin n) (Fin n) K)ᵀ = C) :
    a = b := by
  have h1 := congrArg (fun X : GL (Fin n) K => (X : Matrix (Fin n) (Fin n) K)) h
  simp only [coe_transvGL, transvMatrix, one_smul, add_right_inj] at h1
  have h2 : vecMulVec a a = vecMulVec b b := by
    have := congrArg (· * ((C⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h1
    simp only [vecMulVec_mul] at this
    have hc : ∀ v : Fin n → K, ((C : Matrix (Fin n) (Fin n) K) *ᵥ v) ᵥ*
        ((C⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = v := fun v => by
      have hCt : ((C⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *
          (C : Matrix (Fin n) (Fin n) K) = 1 := by
        conv_lhs => rw [← hCs]
        rw [← transpose_mul, Units.mul_inv, transpose_one]
      rw [← mulVec_transpose, mulVec_mulVec, hCt, one_mulVec]
    rw [hc, hc] at this
    exact this
  funext i
  have h3 := congrFun (congrFun h2 i) i
  simp only [vecMulVec_apply] at h3
  have h4 : (a i + b i) ^ 2 = 0 := by
    have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h3 + (a i * b i + b i * b i) * h22
  have h5 := (pow_eq_zero_iff two_ne_zero).mp h4
  rwa [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h5

theorem dotProduct_mulVec_self_eq_zero [CharP K 2] {C : Matrix (Fin n) (Fin n) K}
    (hCs : Cᵀ = C) (hdiag : ∀ i, C i i = 0) (x : Fin n → K) : x ⬝ᵥ (C *ᵥ x) = 0 := by
  have hsum : x ⬝ᵥ (C *ᵥ x) = ∑ q : Fin n × Fin n, x q.1 * C q.1 q.2 * x q.2 := by
    rw [Fintype.sum_prod_type]
    simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rw [hsum]
  refine Finset.sum_ninvolution Prod.swap (fun q => ?_) (fun q hq => ?_)
    (fun q => Finset.mem_univ _) (fun q => Prod.swap_swap q)
  · have hC : C q.2 q.1 = C q.1 q.2 := by rw [← transpose_apply C q.1 q.2, hCs]
    simp only [Prod.fst_swap, Prod.snd_swap, hC]
    have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination (x q.1 * C q.1 q.2 * x q.2) * h22
  · intro heq
    apply hq
    have h1 : q.1 = q.2 := (Prod.ext_iff.mp heq).2
    rw [h1, hdiag, mul_zero, zero_mul]

@[expose] def matrixIsometryGroupEquiv (C : GL (Fin n) K) :
    matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K) ≃*
      isometryGroup (Matrix.toBilin' (C : Matrix (Fin n) (Fin n) K)) :=
  (MulEquiv.subgroupCongr (by
    ext g
    rw [mem_matrixIsometryGroup, CatalogueBGraphForm.mem_isometryGroup])).trans
    (CatalogueBLinearHigherB.isometryGroupEquiv C).symm

theorem oddCore_matrixIsometryGroup_blockSwapJ {f r : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 3 ≤ n) (hr : n = 2 * r) {C : GL (Fin n) K}
    (hC : (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r) :
    CFSG.oddCore (matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)) = ⊥ := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have halt : (Matrix.toBilin' (C : Matrix (Fin n) (Fin n) K)).IsAlt := fun x => by
    rw [Matrix.toBilin'_apply']
    exact dotProduct_mulVec_self_eq_zero (by rw [hC, blockSwapJ_transpose])
      (fun i => by rw [hC]; exact blockSwapJ_apply_self (by omega) i) x
  have h := oddCore_isometryGroup_eq_bot_of_isAlt hf hK _ halt
    (CatalogueBLinearHigherB.matrixForm_nondegenerate C) (r := r)
    (by rw [Module.finrank_fin_fun]; exact hr) (by omega) (Or.inl (by omega))
  exact EvenCatalog.oddCore_eq_bot_of_mulEquiv (matrixIsometryGroupEquiv C).symm h

section Restrict

variable [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]

theorem sq_injective_of_charTwo {a b : K} (h : a ^ 2 = b ^ 2) : a = b := by
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h1 : (a - b) ^ 2 = 0 := by linear_combination h + (b * b - a * b) * h22
  exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h1)

variable (B : BilinForm K V) (d : V)

theorem isometry_apply_of_sq (hsq : ∀ x, B x x = B d x ^ 2) {g : V ≃ₗ[K] V}
    (hg : g ∈ isometryGroup B) (x : V) : B d (g x) = B d x := by
  apply sq_injective_of_charTwo
  rw [← hsq, ← hsq]
  exact (mem_isometryGroup_iff B g).mp hg x x

theorem isometry_fixes_of_sq (hsq : ∀ x, B x x = B d x ^ 2) (hnd : B.SeparatingLeft)
    {g : V ≃ₗ[K] V} (hg : g ∈ isometryGroup B) : g d = d := by
  have h1 : ∀ y, B (g d - d) y = 0 := by
    intro y
    have e1 : B (g d) y = B d (g.symm y) := by
      have := (mem_isometryGroup_iff B g).mp hg d (g.symm y)
      rwa [g.apply_symm_apply] at this
    have e2 : B d (g.symm y) = B d y := by
      have := isometry_apply_of_sq B d hsq (inv_mem hg) y
      exact this
    rw [map_sub, LinearMap.sub_apply, e1, e2, sub_self]
  exact sub_eq_zero.mp (hnd _ h1)

omit [CharP K 2] in
theorem isCompl_span_ker (hdd : B d d = 1) : IsCompl (K ∙ d) (LinearMap.ker (B d)) := by
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx hxk
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [LinearMap.mem_ker, map_smul, hdd, smul_eq_mul, mul_one] at hxk
    rw [hxk, zero_smul]
  · rw [codisjoint_iff]
    exact LinearMap.span_singleton_sup_ker_eq_top (B d) (by rw [hdd]; exact one_ne_zero)

omit [CharP K 2] in
theorem sub_smul_mem_ker (hdd : B d d = 1) (x : V) : x - B d x • d ∈ LinearMap.ker (B d) := by
  rw [LinearMap.mem_ker, map_sub, map_smul, hdd, smul_eq_mul, mul_one, sub_self]

omit [CharP K 2] in
theorem restrict_ker_isAlt (hsq : ∀ x, B x x = B d x ^ 2) :
    (B.restrict (LinearMap.ker (B d))).IsAlt := fun w => by
  rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, hsq,
    LinearMap.mem_ker.mp w.2, zero_pow two_ne_zero]

omit [CharP K 2] in
theorem restrict_ker_nondegenerate (hBs : ∀ x y, B x y = B y x) (hnd : B.SeparatingLeft)
    (hdd : B d d = 1) : (B.restrict (LinearMap.ker (B d))).Nondegenerate := by
  have key : ∀ w : LinearMap.ker (B d), (∀ w' : LinearMap.ker (B d), B w w' = 0) → w = 0 := by
    intro w hw
    apply Subtype.ext
    apply hnd
    intro x
    have h1 := hw ⟨_, sub_smul_mem_ker B d hdd x⟩
    have h2 : B w d = 0 := by
      rw [hBs]
      exact LinearMap.mem_ker.mp w.2
    calc B w x = B w (B d x • d + (x - B d x • d)) := by rw [add_sub_cancel]
      _ = 0 := by
        rw [map_add, map_smul, h2, smul_zero, zero_add]
        exact h1
  refine ⟨fun w hw => key w fun w' => ?_, fun w hw => key w fun w' => ?_⟩
  · simpa [LinearMap.BilinForm.restrict_apply] using hw w'
  · rw [hBs]
    simpa [LinearMap.BilinForm.restrict_apply] using hw w'

omit [CharP K 2] in
theorem finrank_ker_add_one [FiniteDimensional K V] (hdd : B d d = 1) :
    Module.finrank K (LinearMap.ker (B d)) + 1 = Module.finrank K V := by
  have h1 := Submodule.finrank_add_eq_of_isCompl (isCompl_span_ker B d hdd)
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp at hdd
  rw [finrank_span_singleton hd0] at h1
  omega

theorem map_ker_eq_of_sq (hsq : ∀ x, B x x = B d x ^ 2) {g : V ≃ₗ[K] V}
    (hg : g ∈ isometryGroup B) :
    (LinearMap.ker (B d)).map (g : V →ₗ[K] V) = LinearMap.ker (B d) := by
  ext x
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [isometry_apply_of_sq B d hsq hg, hy]
  · intro hx
    refine ⟨g.symm x, ?_, g.apply_symm_apply x⟩
    rw [← isometry_apply_of_sq B d hsq hg, g.apply_symm_apply, hx]

@[expose] def isometryRestrict (hsq : ∀ x, B x x = B d x ^ 2) :
    isometryGroup B →* isometryGroup (B.restrict (LinearMap.ker (B d))) where
  toFun g := ⟨(g : V ≃ₗ[K] V).ofSubmodules _ _ (map_ker_eq_of_sq B d hsq g.2),
    (mem_isometryGroup_iff _ _).mpr fun x y => by
      simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
        LinearEquiv.ofSubmodules_apply]
      exact (mem_isometryGroup_iff B _).mp g.2 x y⟩
  map_one' := Subtype.ext (LinearEquiv.ext fun w => Subtype.ext rfl)
  map_mul' g h := Subtype.ext (LinearEquiv.ext fun w => Subtype.ext rfl)

theorem isometryRestrict_apply (hsq : ∀ x, B x x = B d x ^ 2) (g : isometryGroup B)
    (w : LinearMap.ker (B d)) :
    ((isometryRestrict B d hsq g : LinearMap.ker (B d) ≃ₗ[K] LinearMap.ker (B d)) w : V) =
      (g : V ≃ₗ[K] V) w := rfl

theorem isometryRestrict_bijective [FiniteDimensional K V] (hsq : ∀ x, B x x = B d x ^ 2)
    (hBs : ∀ x y, B x y = B y x) (hnd : B.SeparatingLeft) (hdd : B d d = 1) :
    Function.Bijective (isometryRestrict B d hsq) := by
  have hc := isCompl_span_ker B d hdd
  have hperp : ∀ a ∈ (K ∙ d), ∀ z ∈ LinearMap.ker (B d), B a z = 0 ∧ B z a = 0 := by
    intro a ha z hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
    have h1 : B (c • d) z = 0 := by
      rw [map_smul, LinearMap.smul_apply, LinearMap.mem_ker.mp hz, smul_zero]
    exact ⟨h1, by rw [hBs]; exact h1⟩
  refine ⟨(injective_iff_map_eq_one _).mpr fun g hg => ?_, fun h => ?_⟩
  · have hW : ∀ w ∈ LinearMap.ker (B d), (g : V ≃ₗ[K] V) w = w := fun w hw => by
      have := congrArg (fun e : isometryGroup (B.restrict (LinearMap.ker (B d))) =>
        (((e : LinearMap.ker (B d) ≃ₗ[K] LinearMap.ker (B d)) ⟨w, hw⟩ : LinearMap.ker (B d)) :
          V)) hg
      exact this
    have hd := isometry_fixes_of_sq B d hsq hnd g.2
    refine Subtype.ext (LinearEquiv.ext fun x => ?_)
    have hx : x = B d x • d + (x - B d x • d) := by rw [add_sub_cancel]
    rw [hx, map_add, map_smul, hd, hW _ (sub_smul_mem_ker B d hdd x)]
    rfl
  ·
    set f : V →ₗ[K] V := LinearMap.ofIsCompl hc (K ∙ d).subtype
      ((LinearMap.ker (B d)).subtype ∘ₗ
        ((h : LinearMap.ker (B d) ≃ₗ[K] LinearMap.ker (B d)) :
          LinearMap.ker (B d) →ₗ[K] LinearMap.ker (B d))) with hfdef
    have hfa : ∀ a : (K ∙ d), f a = a := fun a => by
      rw [hfdef, LinearMap.ofIsCompl_apply_left]
      rfl
    have hfw : ∀ w : LinearMap.ker (B d),
        f w = ((h : LinearMap.ker (B d) ≃ₗ[K] LinearMap.ker (B d)) w : V) := fun w => by
      rw [hfdef, LinearMap.ofIsCompl_apply_right]
      rfl
    have hhw : ∀ w w' : LinearMap.ker (B d),
        B ((h : LinearMap.ker (B d) ≃ₗ[K] LinearMap.ker (B d)) w : V)
          ((h : LinearMap.ker (B d) ≃ₗ[K] LinearMap.ker (B d)) w' : V) = B w w' := by
      intro w w'
      have := (mem_isometryGroup_iff _ _).mp h.2 w w'
      simpa [LinearMap.BilinForm.restrict_apply] using this
    have hiso : TauCeti.BilinForm.IsIsometry B f := by
      rw [TauCeti.BilinForm.isIsometry_iff]
      intro x y
      obtain ⟨a, w, hx, -⟩ := Submodule.existsUnique_add_of_isCompl hc x
      obtain ⟨a', w', hy, -⟩ := Submodule.existsUnique_add_of_isCompl hc y
      subst hx hy
      have ex : f ((a : V) + w) =
          a + ((h : LinearMap.ker (B d) ≃ₗ[K] LinearMap.ker (B d)) w : V) := by
        rw [map_add, hfa, hfw]
      have ey : f ((a' : V) + w') =
          a' + ((h : LinearMap.ker (B d) ≃ₗ[K] LinearMap.ker (B d)) w' : V) := by
        rw [map_add, hfa, hfw]
      rw [ex, ey]
      simp only [map_add, LinearMap.add_apply]
      rw [(hperp a a.2 _ (((h : LinearMap.ker (B d) ≃ₗ[K] LinearMap.ker (B d)) w').2)).1,
        (hperp a' a'.2 _ (((h : LinearMap.ker (B d) ≃ₗ[K] LinearMap.ker (B d)) w).2)).2,
        (hperp a a.2 _ w'.2).1, (hperp a' a'.2 _ w.2).2, hhw]
    refine ⟨hiso.toIsometryGroup hnd, Subtype.ext (LinearEquiv.ext fun w => Subtype.ext ?_)⟩
    rw [isometryRestrict_apply, TauCeti.BilinForm.IsIsometry.toIsometryGroup_apply, hfw]

@[expose] def isometryGroupRestrictEquiv [FiniteDimensional K V] (hsq : ∀ x, B x x = B d x ^ 2)
    (hBs : ∀ x y, B x y = B y x) (hnd : B.SeparatingLeft) (hdd : B d d = 1) :
    isometryGroup B ≃* isometryGroup (B.restrict (LinearMap.ker (B d))) :=
  MulEquiv.ofBijective _ (isometryRestrict_bijective B d hsq hBs hnd hdd)

end Restrict

theorem oddCore_matrixIsometryGroup_one {f r : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hr : n = 2 * r + 1) (hr1 : 1 ≤ r) (h : 2 ≤ r ∨ 4 ≤ Nat.card K) :
    CFSG.oddCore (matrixIsometryGroup ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = ⊥ := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  set B : BilinForm K (Fin n → K) := Matrix.toBilin' ((1 : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K) with hBdef
  have hB : ∀ x y, B x y = x ⬝ᵥ y := fun x y => by
    rw [hBdef, Matrix.toBilin'_apply', Units.val_one, one_mulVec]
  set d : Fin n → K := fun _ => 1 with hd
  have hsq : ∀ x, B x x = B d x ^ 2 := by
    intro x
    rw [hB, hB]
    simp only [dotProduct, hd, one_mul]
    rw [sum_pow_char]
    simp only [sq]
  have hdd : B d d = 1 := by
    rw [hB]
    simp only [dotProduct, hd, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    rw [hr, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, CharTwo.two_eq_zero, zero_mul,
      zero_add, Nat.cast_one]
  have hBs : ∀ x y, B x y = B y x := fun x y => by rw [hB, hB, dotProduct_comm]
  have hnd : B.SeparatingLeft := (CatalogueBLinearHigherB.matrixForm_nondegenerate 1).1
  have hdim := finrank_ker_add_one B d hdd
  rw [Module.finrank_fin_fun] at hdim
  have hW := oddCore_isometryGroup_eq_bot_of_isAlt hf hK _ (restrict_ker_isAlt B d hsq)
    (restrict_ker_nondegenerate B d hBs hnd hdd) (r := r) (by omega) hr1 h
  exact EvenCatalog.oddCore_eq_bot_of_mulEquiv
    ((matrixIsometryGroupEquiv 1).trans (isometryGroupRestrictEquiv B d hsq hBs hnd hdd)).symm hW

end CFSG.ComponentClassification.UnbalancedCatalog
