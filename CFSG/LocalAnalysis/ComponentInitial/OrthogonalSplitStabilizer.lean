module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitRootData

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module Matrix CFSG.LieType.Universal.Spin
open scoped Pointwise

variable {r : ℕ} {K : Type*} [Field K]

theorem quadPlus_eq_dotProduct (v : Fin r ⊕ Fin r → K) :
    quadPlus r K v = (v ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inr) := by
  rw [quadPlus_apply]
  rfl

theorem mem_flag_top {v : Fin r ⊕ Fin r → K} : v ∈ flag r K r ↔ ∀ i, v (.inr i) = 0 := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, -, rfl⟩ := hx
      intro i
      simp
    | zero => simp
    | add x y _ _ hx hy => intro i; simp [hx i, hy i]
    | smul a x _ hx => intro i; simp [hx i]
  · intro hv
    have hsum : v = ∑ j : Fin r, v (.inl j) • (Pi.single (Sum.inl j) (1 : K) :
        Fin r ⊕ Fin r → K) := by
      ext c
      rcases c with c | c
      · simp [Finset.sum_apply, Pi.single_apply]
      · simp [Finset.sum_apply, hv c]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, j.2, rfl⟩)

theorem mem_stabilizer_iff_map {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    {S : Submodule K (Fin r ⊕ Fin r → K)} :
    g ∈ MulAction.stabilizer ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) S ↔
      S.map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = S :=
  Iff.rfl

theorem mulVec_dotProduct_self_eq_zero {C : Matrix (Fin r) (Fin r) K} (hC : Cᵀ = -C)
    (hd : ∀ i, C i i = 0) (y : Fin r → K) : (C *ᵥ y) ⬝ᵥ y = 0 := by
  set U : Matrix (Fin r) (Fin r) K := Matrix.of fun i j => if i < j then C i j else 0 with hU
  have hCU : C = U - Uᵀ := by
    ext i j
    have hji : C j i = -C i j := by
      have := congrFun (congrFun hC i) j
      simpa using this
    simp only [hU, Matrix.sub_apply, Matrix.transpose_apply, Matrix.of_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, h.not_gt]
    · simp [hd]
    · simp [h, h.not_gt, hji]
  rw [hCU, Matrix.sub_mulVec, sub_dotProduct, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec,
    dotProduct_comm y, sub_self]

theorem alternating_of_mulVec_dotProduct_self {C : Matrix (Fin r) (Fin r) K}
    (h : ∀ y, (C *ᵥ y) ⬝ᵥ y = 0) : Cᵀ = -C ∧ ∀ i, C i i = 0 := by
  have hd : ∀ i, C i i = 0 := fun i => by
    have := h (Pi.single i 1)
    simpa [Matrix.mulVec_single_one] using this
  refine ⟨?_, hd⟩
  ext i j
  have := h (Pi.single i 1 + Pi.single j 1)
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, Matrix.mulVec_single_one] at this
  have h1 := h (Pi.single i 1)
  have h2 := h (Pi.single j 1)
  simp only [Matrix.mulVec_single_one] at h1 h2
  simp only [Matrix.transpose_apply, Matrix.neg_apply]
  simp only [dotProduct_single, Matrix.col_apply, mul_one] at this h1 h2
  linear_combination this - h1 - h2

@[expose] noncomputable def blockDiagInv (A : Matrix (Fin r) (Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  fromBlocks A 0 0 (A⁻¹)ᵀ

theorem blockDiagInv_mul (A B : Matrix (Fin r) (Fin r) K) :
    blockDiagInv (A * B) = blockDiagInv A * blockDiagInv B := by
  rw [blockDiagInv, blockDiagInv, blockDiagInv, fromBlocks_multiply, Matrix.mul_inv_rev,
    Matrix.transpose_mul]
  simp

theorem blockDiagInv_one : blockDiagInv (1 : Matrix (Fin r) (Fin r) K) = 1 := by
  rw [blockDiagInv, inv_one, transpose_one, fromBlocks_one]

@[expose] def blockUnip (C : Matrix (Fin r) (Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  fromBlocks 1 C 0 1

theorem blockUnip_add (C C' : Matrix (Fin r) (Fin r) K) :
    blockUnip (C + C') = blockUnip C * blockUnip C' := by
  rw [blockUnip, blockUnip, blockUnip, fromBlocks_multiply]
  simp [add_comm]

theorem blockUnip_zero : blockUnip (0 : Matrix (Fin r) (Fin r) K) = 1 := by
  rw [blockUnip, fromBlocks_one]

theorem fromBlocks_eq_blockDiagInv_mul (A : GL (Fin r) K) (C : Matrix (Fin r) (Fin r) K) :
    fromBlocks (A : Matrix (Fin r) (Fin r) K) ((A : Matrix (Fin r) (Fin r) K) * C) 0 ((A⁻¹ : GL (Fin r) K) :
      Matrix (Fin r) (Fin r) K)ᵀ = blockDiagInv (A : Matrix (Fin r) (Fin r) K) * blockUnip C := by
  rw [blockDiagInv, blockUnip, fromBlocks_multiply, Matrix.coe_units_inv]
  simp

theorem fromBlocks_mulVec_apply (A B C D : Matrix (Fin r) (Fin r) K) (v : Fin r ⊕ Fin r → K) :
    fromBlocks A B C D *ᵥ v =
      Sum.elim (A *ᵥ (v ∘ Sum.inl) + B *ᵥ (v ∘ Sum.inr))
        (C *ᵥ (v ∘ Sum.inl) + D *ᵥ (v ∘ Sum.inr)) :=
  fromBlocks_mulVec A B C D v

variable (r K) in
@[expose] noncomputable def maxStab : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) ⊓
    MulAction.stabilizer ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (flag r K r)

theorem mem_maxStab {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} :
    g ∈ maxStab r K ↔ g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) ∧
      (flag r K r).map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = flag r K r :=
  Iff.rfl

theorem apply_eq_toMatrix'_mulVec (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))
    (v : Fin r ⊕ Fin r → K) :
    g v = LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) *ᵥ v :=
  (LinearMap.toMatrix'_mulVec _ v).symm

theorem mem_maxStab_of_toMatrix' {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (A : GL (Fin r) K) (C : Matrix (Fin r) (Fin r) K) (hC : Cᵀ = -C) (hd : ∀ i, C i i = 0)
    (hg : LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
      fromBlocks (A : Matrix (Fin r) (Fin r) K) ((A : Matrix (Fin r) (Fin r) K) * C) 0
        ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ) :
    g ∈ maxStab r K := by
  have happ : ∀ v, g v = Sum.elim ((A : Matrix (Fin r) (Fin r) K) *ᵥ
      (v ∘ Sum.inl + C *ᵥ (v ∘ Sum.inr)))
      (((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ *ᵥ (v ∘ Sum.inr)) := fun v => by
    rw [apply_eq_toMatrix'_mulVec, hg, fromBlocks_mulVec_apply, Matrix.zero_mulVec, zero_add,
      Matrix.mulVec_add, Matrix.mulVec_mulVec]
  refine ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun v => ?_, ?_⟩
  · rw [happ, quadPlus_eq_dotProduct, quadPlus_eq_dotProduct]
    change ((A : Matrix (Fin r) (Fin r) K) *ᵥ (v ∘ Sum.inl + C *ᵥ (v ∘ Sum.inr))) ⬝ᵥ
      (((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ *ᵥ (v ∘ Sum.inr)) = _
    rw [Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one, dotProduct_add,
      dotProduct_comm (v ∘ Sum.inr) (C *ᵥ _), mulVec_dotProduct_self_eq_zero hC hd, add_zero,
      dotProduct_comm]
  · have hle : (flag r K r).map (g : (Fin r ⊕ Fin r → K) →ₗ[K] _) ≤ flag r K r := by
      rintro _ ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe, mem_flag_top] at hv
      rw [mem_flag_top]
      intro i
      have hy : v ∘ Sum.inr = 0 := funext hv
      change g v (Sum.inr i) = 0
      rw [happ, Sum.elim_inr, hy, Matrix.mulVec_zero, Pi.zero_apply]
    exact Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq g _)

theorem exists_toMatrix'_of_mem_maxStab {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hg : g ∈ maxStab r K) :
    ∃ (A : GL (Fin r) K) (C : Matrix (Fin r) (Fin r) K), Cᵀ = -C ∧ (∀ i, C i i = 0) ∧
      LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
        fromBlocks (A : Matrix (Fin r) (Fin r) K) ((A : Matrix (Fin r) (Fin r) K) * C) 0
          ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ := by
  obtain ⟨hO, hX⟩ := mem_maxStab.1 hg
  set M := LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) with hM
  set P := M.toBlocks₁₁
  set R := M.toBlocks₁₂
  set S := M.toBlocks₂₁
  set U := M.toBlocks₂₂
  have hMb : M = fromBlocks P R S U := (fromBlocks_toBlocks M).symm
  have hcol : ∀ c d, M d c = g (Pi.single c 1) d := fun c d => by
    rw [apply_eq_toMatrix'_mulVec, ← hM, Matrix.mulVec_single_one, Matrix.col_apply]
  have hS : S = 0 := by
    ext i j
    have hmem : g (Pi.single (Sum.inl j) 1) ∈ flag r K r := by
      rw [← hX]
      exact Submodule.mem_map_of_mem (mem_flag_top.2 fun i => by simp)
    change M (Sum.inr i) (Sum.inl j) = 0
    rw [hcol]
    exact mem_flag_top.1 hmem i
  have hPU : Pᵀ * U = 1 := by
    ext j k
    have h := polar_map_of_mem hO (Pi.single (Sum.inl j) 1) (Pi.single (Sum.inr k) 1)
    rw [polar_quadPlus_single_inr, polar_quadPlus] at h
    have hrhs : (Pi.single (Sum.inl j) (1 : K) : Fin r ⊕ Fin r → K) (Sum.inl k) =
        if j = k then 1 else 0 := by
      by_cases hjk : j = k
      · subst hjk
        simp
      · rw [Pi.single_eq_of_ne (by simpa using Ne.symm hjk)]
        simp [hjk]
    rw [Matrix.mul_apply, Matrix.one_apply, ← hrhs, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hcol, ← hcol, ← hcol, ← hcol]
    have hSi : M (Sum.inr i) (Sum.inl j) = 0 := by
      change S i j = 0
      rw [hS, Matrix.zero_apply]
    rw [hSi, mul_zero, add_zero]
    rfl
  have hUP : Uᵀ * P = 1 := by
    have := congrArg Matrix.transpose hPU
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have hPU' : P * Uᵀ = 1 := mul_eq_one_comm.1 hUP
  let A : GL (Fin r) K := ⟨P, Uᵀ, hPU', hUP⟩
  have hAinv : ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = Uᵀ := rfl
  set C := Uᵀ * R with hCdef
  have hquad : ∀ y, (C *ᵥ y) ⬝ᵥ y = 0 := by
    intro y
    have h := map_of_mem hO (Sum.elim 0 y)
    rw [quadPlus_eq_dotProduct, quadPlus_eq_dotProduct, apply_eq_toMatrix'_mulVec, ← hM, hMb,
      fromBlocks_mulVec_apply] at h
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_zero, zero_add,
      zero_dotProduct] at h
    change (R *ᵥ y) ⬝ᵥ (U *ᵥ y) = 0 at h
    rw [hCdef, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
    exact h
  obtain ⟨hCt, hCd⟩ := alternating_of_mulVec_dotProduct_self hquad
  refine ⟨A, C, hCt, hCd, ?_⟩
  rw [hMb, hS, hAinv, Matrix.transpose_transpose]
  congr 1
  change R = P * (Uᵀ * R)
  rw [← Matrix.mul_assoc, hPU', Matrix.one_mul]

theorem fromBlocks_params_unique {A A' : GL (Fin r) K} {C C' : Matrix (Fin r) (Fin r) K}
    (h : fromBlocks (A : Matrix (Fin r) (Fin r) K) ((A : Matrix (Fin r) (Fin r) K) * C) 0
        ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ =
      fromBlocks (A' : Matrix (Fin r) (Fin r) K) ((A' : Matrix (Fin r) (Fin r) K) * C') 0
        ((A'⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ) :
    A = A' ∧ C = C' := by
  obtain ⟨h1, h2, -, -⟩ := fromBlocks_inj.1 h
  have hA : A = A' := Units.ext h1
  subst hA
  refine ⟨rfl, ?_⟩
  have := congrArg (fun M => ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) * M) h2
  simpa only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul] using this

theorem det_fromBlocks_params (A : GL (Fin r) K) (C : Matrix (Fin r) (Fin r) K) :
    (fromBlocks (A : Matrix (Fin r) (Fin r) K) ((A : Matrix (Fin r) (Fin r) K) * C) 0
      ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ).det = 1 := by
  rw [det_fromBlocks_zero₂₁, det_transpose, ← det_mul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, det_one]

theorem quadPlus_single_inl (i : Fin r) :
    quadPlus r K (Pi.single (Sum.inl i) 1) = 0 :=
  quadPlus_single (Sum.inl i)

theorem toMatrix'_eichler_inl_inr {i j : Fin r} (hij : i ≠ j) (t : K) :
    LinearMap.toMatrix' ((eichler (quadPlus r K) (Pi.single (Sum.inl i) 1)
      ((-t) • Pi.single (Sum.inr j) 1) : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
        (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
      fromBlocks (1 + t • Matrix.single i j 1) 0 0 (1 - t • Matrix.single j i 1) := by
  have hv : polar (quadPlus r K) (Pi.single (Sum.inl i) 1) ((-t) • Pi.single (Sum.inr j) 1) = 0 :=
    polar_single_smul_single (by simpa using Ne.symm hij) _
  ext a b
  rw [LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, eichler_apply (quadPlus_single_inl i) hv]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [polar_single, Pi.single_apply, Matrix.single_apply, Matrix.one_apply, map_smul_eq_sq,
      quadPlus_single] <;> split_ifs <;> simp_all

theorem toMatrix'_eichler_inl_inl {i j : Fin r} (hij : i ≠ j) (t : K) :
    LinearMap.toMatrix' ((eichler (quadPlus r K) (Pi.single (Sum.inl i) 1)
      ((-t) • Pi.single (Sum.inl j) 1) : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
        (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
      fromBlocks 1 (t • (Matrix.single i j 1 - Matrix.single j i 1)) 0 1 := by
  have hv : polar (quadPlus r K) (Pi.single (Sum.inl i) 1) ((-t) • Pi.single (Sum.inl j) 1) = 0 :=
    polar_single_smul_single (by simp) _
  ext a b
  rw [LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, eichler_apply (quadPlus_single_inl i) hv]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [polar_single, Pi.single_apply, Matrix.single_apply, Matrix.one_apply, map_smul_eq_sq,
      quadPlus_single] <;> split_ifs <;> simp_all

theorem toMatrix'_torusElt (d : Fin r → Kˣ) :
    LinearMap.toMatrix' ((torusElt r K d : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
        (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
      fromBlocks (diagonal fun i => (d i : K)) 0 0 (diagonal fun i => ((d i)⁻¹ : Kˣ)) := by
  ext a b
  rw [LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, torusElt_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Pi.single_apply, diagonal_apply, eq_comm]

variable (r K) in
@[expose] def maxStabGens : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  Set.range (torusElt r K) ∪
    {g | ∃ (i j : Fin r) (t : K), i ≠ j ∧
      g = eichler (quadPlus r K) (Pi.single (Sum.inl i) 1) ((-t) • Pi.single (Sum.inr j) 1)} ∪
    {g | ∃ (i j : Fin r) (t : K), i < j ∧
      g = eichler (quadPlus r K) (Pi.single (Sum.inl i) 1) ((-t) • Pi.single (Sum.inl j) 1)}

theorem transvection_inv {i j : Fin r} (hij : i ≠ j) (c : K) :
    (transvection i j c)⁻¹ = transvection i j (-c) :=
  Matrix.inv_eq_left_inv (by rw [transvection_mul_transvection_same i j hij, neg_add_cancel,
    transvection_zero])

theorem blockDiagInv_transvection {i j : Fin r} (hij : i ≠ j) (c : K) :
    blockDiagInv (transvection i j c) = LinearMap.toMatrix'
      ((eichler (quadPlus r K) (Pi.single (Sum.inl i) 1) ((-c) • Pi.single (Sum.inr j) 1) :
        (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
          (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) := by
  rw [toMatrix'_eichler_inl_inr hij, blockDiagInv, transvection_inv hij, transvection,
    transvection, transpose_add, transpose_one, transpose_single]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.single_apply, sub_eq_add_neg]
  split_ifs <;> simp

theorem blockDiagInv_diagonal {D : Fin r → K} (hD : ∀ i, D i ≠ 0) :
    blockDiagInv (diagonal D) = LinearMap.toMatrix'
      ((torusElt r K fun i => Units.mk0 (D i) (hD i) :
        (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
          (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) := by
  have hinv : (diagonal D)⁻¹ = diagonal fun i => (D i)⁻¹ :=
    Matrix.inv_eq_left_inv (by rw [diagonal_mul_diagonal]; simp [hD])
  rw [toMatrix'_torusElt, blockDiagInv, hinv, diagonal_transpose]
  simp

theorem blockUnip_single {i j : Fin r} (hij : i ≠ j) (t : K) :
    blockUnip (t • (Matrix.single i j 1 - Matrix.single j i 1)) = LinearMap.toMatrix'
      ((eichler (quadPlus r K) (Pi.single (Sum.inl i) 1) ((-t) • Pi.single (Sum.inl j) 1) :
        (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
          (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) := by
  rw [toMatrix'_eichler_inl_inl hij, blockUnip]

theorem eq_sum_of_alternating {C : Matrix (Fin r) (Fin r) K} (hC : Cᵀ = -C)
    (hd : ∀ i, C i i = 0) :
    C = ∑ p ∈ Finset.univ.filter (fun p : Fin r × Fin r => p.1 < p.2),
      C p.1 p.2 • (Matrix.single p.1 p.2 1 - Matrix.single p.2 p.1 1) := by
  ext a b
  have hba : C b a = -C a b := by
    have := congrFun (congrFun hC a) b
    simpa using this
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply, smul_eq_mul, mul_sub,
    mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
  have h1 : ∀ x : Fin r × Fin r, (if x.1 = a ∧ x.2 = b then C x.1 x.2 else 0) =
      if x = (a, b) then C a b else 0 := by
    rintro ⟨x1, x2⟩
    simp only [Prod.mk.injEq]
    split_ifs with h <;> simp_all
  have h2 : ∀ x : Fin r × Fin r, (if x.2 = a ∧ x.1 = b then C x.1 x.2 else 0) =
      if x = (b, a) then C b a else 0 := by
    rintro ⟨x1, x2⟩
    simp only [Prod.mk.injEq]
    split_ifs with h h' h' <;> simp_all
  simp only [h1, h2, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h, h.not_gt]
  · simp [hd]
  · simp [h, h.not_gt, hba]

theorem det_prod_transvection (L : List (TransvectionStruct (Fin r) K)) :
    (L.map TransvectionStruct.toMatrix).prod.det = 1 := by
  induction L with
  | nil => simp
  | cons T L ih => rw [List.map_cons, List.prod_cons, det_mul, ih, mul_one, T.det]

theorem maxStab_eq_closure : maxStab r K = Subgroup.closure (maxStabGens r K) := by
  apply le_antisymm
  · intro g hg
    let InH : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K → Prop := fun M =>
      ∃ h ∈ Subgroup.closure (maxStabGens r K),
        LinearMap.toMatrix' (h : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = M
    have hmul : ∀ M N, InH M → InH N → InH (M * N) := by
      rintro _ _ ⟨h₁, h₁H, rfl⟩ ⟨h₂, h₂H, rfl⟩
      exact ⟨h₁ * h₂, mul_mem h₁H h₂H, by
        rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix'_mul]⟩
    have hone : InH 1 := ⟨1, one_mem _, by
      rw [← LinearMap.toMatrix'_id]
      rfl⟩
    have hgen : ∀ h ∈ maxStabGens r K,
        InH (LinearMap.toMatrix' (h : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K))) :=
      fun h hh => ⟨h, Subgroup.subset_closure hh, rfl⟩
    have hlist : ∀ L : List (TransvectionStruct (Fin r) K),
        InH (blockDiagInv (L.map TransvectionStruct.toMatrix).prod) := by
      intro L
      induction L with
      | nil =>
        rw [List.map_nil, List.prod_nil, blockDiagInv_one]
        exact hone
      | cons T L ih =>
        rw [List.map_cons, List.prod_cons, blockDiagInv_mul]
        refine hmul _ _ ?_ ih
        rw [TransvectionStruct.toMatrix, blockDiagInv_transvection T.hij]
        exact hgen _ (Or.inl (Or.inr ⟨T.i, T.j, T.c, T.hij, rfl⟩))
    have hdiag : ∀ D : Fin r → K, (∀ i, D i ≠ 0) → InH (blockDiagInv (diagonal D)) :=
      fun D hD => by
        rw [blockDiagInv_diagonal hD]
        exact hgen _ (Or.inl (Or.inl ⟨_, rfl⟩))
    have hGL : ∀ A : GL (Fin r) K, InH (blockDiagInv (A : Matrix (Fin r) (Fin r) K)) := by
      intro A
      obtain ⟨L, L', D, hA⟩ :=
        Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec (A : Matrix (Fin r) (Fin r) K)
      have hdet : (A : Matrix (Fin r) (Fin r) K).det ≠ 0 := (Matrix.isUnits_det_units A).ne_zero
      have hD : ∀ i, D i ≠ 0 := by
        rw [hA, det_mul, det_mul, det_prod_transvection, det_prod_transvection, det_diagonal,
          one_mul, mul_one] at hdet
        exact fun i => Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ i)
      rw [hA, blockDiagInv_mul, blockDiagInv_mul]
      exact hmul _ _ (hmul _ _ (hlist L) (hdiag D hD)) (hlist L')
    have hunip : ∀ C : Matrix (Fin r) (Fin r) K, Cᵀ = -C → (∀ i, C i i = 0) →
        InH (blockUnip C) := by
      intro C hC hd
      rw [eq_sum_of_alternating hC hd]
      refine Finset.sum_induction _ (fun C => InH (blockUnip C))
        (fun a b ha hb => by rw [blockUnip_add]; exact hmul _ _ ha hb)
        (by rw [blockUnip_zero]; exact hone) fun p hp => ?_
      have hp' : p.1 < p.2 := (Finset.mem_filter.1 hp).2
      change InH (blockUnip (C p.1 p.2 • (Matrix.single p.1 p.2 1 - Matrix.single p.2 p.1 1)))
      rw [blockUnip_single hp'.ne]
      exact hgen _ (Or.inr ⟨p.1, p.2, _, hp', rfl⟩)
    obtain ⟨A, C, hC, hd, hgM⟩ := exists_toMatrix'_of_mem_maxStab hg
    obtain ⟨h, hH, hh⟩ := hmul _ _ (hGL A) (hunip C hC hd)
    rw [← fromBlocks_eq_blockDiagInv_mul, ← hgM] at hh
    have hhg : h = g := LinearEquiv.toLinearMap_injective (LinearMap.toMatrix'.injective hh)
    rw [← hhg]
    exact hH
  · rw [Subgroup.closure_le]
    rintro g ((⟨d, rfl⟩ | ⟨i, j, t, hij, rfl⟩) | ⟨i, j, t, hij, rfl⟩)
    ·
      let A : GL (Fin r) K := ⟨diagonal fun i => (d i : K), diagonal fun i => ((d i)⁻¹ : Kˣ),
        by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩
      refine mem_maxStab_of_toMatrix' A 0 (by simp) (by simp) ?_
      rw [toMatrix'_torusElt]
      simp [A]
    ·
      have hEE : Matrix.single i j (1 : K) * Matrix.single i j 1 = 0 :=
        single_mul_single_of_ne (1 : K) i j i hij.symm 1
      let A : GL (Fin r) K := ⟨1 + t • Matrix.single i j 1, 1 - t • Matrix.single i j 1,
        by
          rw [add_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, smul_mul_smul_comm, hEE,
            smul_zero, sub_zero]
          abel,
        by
          rw [sub_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul_comm, hEE,
            smul_zero, add_zero]
          abel⟩
      refine mem_maxStab_of_toMatrix' A 0 (by simp) (by simp) ?_
      rw [toMatrix'_eichler_inl_inr hij]
      simp [A, transpose_single]
    ·
      refine mem_maxStab_of_toMatrix' 1 (t • (Matrix.single i j 1 - Matrix.single j i 1)) ?_
        ?_ ?_
      · rw [transpose_smul, transpose_sub, transpose_single, transpose_single, ← neg_sub,
          smul_neg]
      · intro k
        by_cases h1 : i = k <;> by_cases h2 : j = k <;> simp [h1, h2]
      · rw [toMatrix'_eichler_inl_inl hij.ne]
        simp

theorem orthogonal_geometry_split_maximal_stabilizer_matrices :
    (∀ g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K),
      g ∈ maxStab r K ↔ ∃ (A : GL (Fin r) K) (C : Matrix (Fin r) (Fin r) K), Cᵀ = -C ∧
        (∀ i, C i i = 0) ∧
        LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
          fromBlocks (A : Matrix (Fin r) (Fin r) K) ((A : Matrix (Fin r) (Fin r) K) * C) 0
            ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ) ∧
    (∀ (A : GL (Fin r) K) (C : Matrix (Fin r) (Fin r) K), Cᵀ = -C → (∀ i, C i i = 0) →
      ∃ g ∈ maxStab r K,
        LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
          fromBlocks (A : Matrix (Fin r) (Fin r) K) ((A : Matrix (Fin r) (Fin r) K) * C) 0
            ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ) ∧
    (∀ (A A' : GL (Fin r) K) (C C' : Matrix (Fin r) (Fin r) K),
      fromBlocks (A : Matrix (Fin r) (Fin r) K) ((A : Matrix (Fin r) (Fin r) K) * C) 0
          ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ =
        fromBlocks (A' : Matrix (Fin r) (Fin r) K) ((A' : Matrix (Fin r) (Fin r) K) * C') 0
          ((A'⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ → A = A' ∧ C = C') ∧
    (∀ (A : GL (Fin r) K) (C : Matrix (Fin r) (Fin r) K),
      (fromBlocks (A : Matrix (Fin r) (Fin r) K) ((A : Matrix (Fin r) (Fin r) K) * C) 0
        ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ).det = 1) ∧
    maxStab r K = Subgroup.closure (maxStabGens r K) ∧
    (∀ d : Fin r → Kˣ,
      LinearMap.toMatrix' ((torusElt r K d : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
          (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
        fromBlocks (diagonal fun i => (d i : K)) 0 0 (diagonal fun i => ((d i)⁻¹ : Kˣ))) ∧
    (∀ (i j : Fin r) (t : K), i ≠ j →
      LinearMap.toMatrix' ((eichler (quadPlus r K) (Pi.single (Sum.inl i) 1)
        ((-t) • Pi.single (Sum.inr j) 1) : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
          (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
        fromBlocks (1 + t • Matrix.single i j 1) 0 0 (1 - t • Matrix.single j i 1)) ∧
    ∀ (i j : Fin r) (t : K), i ≠ j →
      LinearMap.toMatrix' ((eichler (quadPlus r K) (Pi.single (Sum.inl i) 1)
        ((-t) • Pi.single (Sum.inl j) 1) : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
          (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
        fromBlocks 1 (t • (Matrix.single i j 1 - Matrix.single j i 1)) 0 1 := by
  refine ⟨fun g => ⟨exists_toMatrix'_of_mem_maxStab,
      fun ⟨A, C, hC, hd, hg⟩ => mem_maxStab_of_toMatrix' A C hC hd hg⟩,
    fun A C hC hd => ?_, fun A A' C C' h => fromBlocks_params_unique h, det_fromBlocks_params,
    maxStab_eq_closure, toMatrix'_torusElt, fun i j t hij => toMatrix'_eichler_inl_inr hij t,
    fun i j t hij => toMatrix'_eichler_inl_inl hij t⟩
  set M := fromBlocks (A : Matrix (Fin r) (Fin r) K) ((A : Matrix (Fin r) (Fin r) K) * C) 0
    ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ with hM
  have hMu : IsUnit M :=
    (Matrix.isUnit_iff_isUnit_det M).2 (by rw [hM, det_fromBlocks_params]; exact isUnit_one)
  let _ : Invertible M := hMu.invertible
  have hmat : LinearMap.toMatrix' ((Matrix.toLinearEquiv' M ‹_› :
      (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
        (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = M := by
    rw [Matrix.toLinearEquiv'_apply, LinearMap.toMatrix'_toLin']
  exact ⟨_, mem_maxStab_of_toMatrix' A C hC hd hmat, hmat⟩

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
