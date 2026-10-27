module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.OrthFrame

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
open QuadraticMap Module Matrix

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [CharP K 2]
  {σ : K ≃+* K} {Q : QuadraticForm K V} {T : V →ₛₗ[(σ : K →+* K)] V} {r : ℕ}

@[expose] def Frame.coeffs (F : Frame Q T r) : V →ₗ[K] (Fin r → K) × (Fin r → K) :=
  (LinearMap.pi fun i => (polarBilin Q).flip (F.f i)).prod
    (LinearMap.pi fun i => (polarBilin Q).flip (F.e i))

@[expose] def Frame.expand (F : Frame Q T r) : (Fin r → K) × (Fin r → K) →ₗ[K] V :=
  (Fintype.linearCombination K F.e).coprod (Fintype.linearCombination K F.f)

theorem Frame.coeffs_apply (F : Frame Q T r) (v : V) :
    F.coeffs v = (fun i => polar Q v (F.f i), fun i => polar Q v (F.e i)) := by
  refine Prod.ext ?_ ?_ <;> funext i <;> simp [Frame.coeffs, polarBilin_apply_apply]

theorem Frame.expand_apply (F : Frame Q T r) (a b : Fin r → K) :
    F.expand (a, b) = ∑ i, a i • F.e i + ∑ i, b i • F.f i := by
  simp [Frame.expand, Fintype.linearCombination_apply]

theorem polar_finsetSum_smul_left {ι : Type*} (s : Finset ι) (Q : QuadraticForm K V) (c : ι → K)
    (x : ι → V) (y : V) : polar Q (∑ i ∈ s, c i • x i) y = ∑ i ∈ s, c i * polar Q (x i) y := by
  have h : ∀ v, polar Q v y = (polarBilin Q).flip y v := fun v => by
    simp [LinearMap.flip_apply, polarBilin_apply_apply]
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← h, polar_smul_left, smul_eq_mul]

theorem Q_sum_smul_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : QuadraticForm K V)
    (x : ι → V) (hQ : ∀ i, Q (x i) = 0) (hB : ∀ i j, polar Q (x i) (x j) = 0) (a : ι → K) :
    Q (∑ i, a i • x i) = 0 := by
  have : ∀ s : Finset ι, Q (∑ i ∈ s, a i • x i) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, add_comm, QuadraticMap.map_add Q, ih, QuadraticMap.map_smul, hQ,
        polar_smul_right]
      have h0 : polar Q (∑ i ∈ s, a i • x i) (x j) = 0 := by
        rw [polar_finsetSum_smul_left]
        simp [hB]
      simp [h0]
  exact this _

theorem Frame.Q_expand (F : Frame Q T r) (a b : Fin r → K) :
    Q (F.expand (a, b)) = a ⬝ᵥ b := by
  rw [Frame.expand_apply, QuadraticMap.map_add Q, Q_sum_smul_zero Q F.e F.Qe F.ee,
    Q_sum_smul_zero Q F.f F.Qf F.ff, zero_add, zero_add, polar_sum_smul_left]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [polar_sum_smul_right]
  simp [F.ef]

theorem Frame.coeffs_expand (F : Frame Q T r) (c : (Fin r → K) × (Fin r → K)) :
    F.coeffs (F.expand c) = c := by
  obtain ⟨a, b⟩ := c
  rw [Frame.coeffs_apply, Frame.expand_apply]
  refine Prod.ext ?_ ?_ <;> funext j
  · simp only
    rw [polar_add_left, polar_sum_smul_left, polar_sum_smul_left]
    simp [F.ef, F.ff]
  · simp only
    rw [polar_add_left, polar_sum_smul_left, polar_sum_smul_left]
    simp [F.ee, polar_comm Q (F.f _) (F.e j), F.ef]

@[expose] def blockAct (M M' : Matrix (Fin r) (Fin r) K) :
    (Fin r → K) × (Fin r → K) →ₗ[K] (Fin r → K) × (Fin r → K) :=
  (Matrix.mulVecLin M).prodMap (Matrix.mulVecLin M'ᵀ)

theorem blockAct_apply (M M' : Matrix (Fin r) (Fin r) K) (c : (Fin r → K) × (Fin r → K)) :
    blockAct M M' c = (M *ᵥ c.1, M'ᵀ *ᵥ c.2) := rfl

@[expose] def blockDelta (M M' : Matrix (Fin r) (Fin r) K) :
    (Fin r → K) × (Fin r → K) →ₗ[K] (Fin r → K) × (Fin r → K) :=
  blockAct M M' - LinearMap.id

theorem blockDelta_apply (M M' : Matrix (Fin r) (Fin r) K) (c : (Fin r → K) × (Fin r → K)) :
    blockDelta M M' c = (M *ᵥ c.1 - c.1, M'ᵀ *ᵥ c.2 - c.2) := rfl

@[expose] def Frame.levi (F : Frame Q T r) (M M' : Matrix (Fin r) (Fin r) K) : V →ₗ[K] V :=
  LinearMap.id + F.expand ∘ₗ blockDelta M M' ∘ₗ F.coeffs

theorem Frame.levi_apply (F : Frame Q T r) (M M' : Matrix (Fin r) (Fin r) K) (v : V) :
    F.levi M M' v = v + F.expand (blockDelta M M' (F.coeffs v)) := rfl

theorem Frame.coeffs_levi (F : Frame Q T r) (M M' : Matrix (Fin r) (Fin r) K) (v : V) :
    F.coeffs (F.levi M M' v) = blockAct M M' (F.coeffs v) := by
  rw [Frame.levi_apply, map_add, Frame.coeffs_expand]
  simp [blockDelta]

theorem Frame.levi_levi (F : Frame Q T r) (M₁ M₁' M₂ M₂' : Matrix (Fin r) (Fin r) K) (v : V) :
    F.levi M₁ M₁' (F.levi M₂ M₂' v) = F.levi (M₁ * M₂) (M₂' * M₁') v := by
  rw [Frame.levi_apply, Frame.coeffs_levi, Frame.levi_apply, Frame.levi_apply, add_assoc,
    ← map_add]
  congr 2
  ext <;> simp [blockDelta_apply, blockAct_apply, Matrix.mulVec_mulVec, Matrix.transpose_mul]

theorem Frame.polar_expand (F : Frame Q T r) (v : V) (c : (Fin r → K) × (Fin r → K)) :
    polar Q v (F.expand c) = c.1 ⬝ᵥ (F.coeffs v).2 + c.2 ⬝ᵥ (F.coeffs v).1 := by
  obtain ⟨a, b⟩ := c
  rw [Frame.expand_apply, polar_add_right, polar_sum_smul_right, polar_sum_smul_right,
    Frame.coeffs_apply]
  simp [dotProduct]

theorem dot_block (M M' : Matrix (Fin r) (Fin r) K) (hMM : M' * M = 1) (a b : Fin r → K) :
    (M *ᵥ a) ⬝ᵥ (M'ᵀ *ᵥ b) = a ⬝ᵥ b := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, hMM,
    Matrix.one_mulVec]

theorem Frame.Q_levi (F : Frame Q T r) (M M' : Matrix (Fin r) (Fin r) K) (hMM : M' * M = 1)
    (v : V) : Q (F.levi M M' v) = Q v := by
  rw [Frame.levi_apply, QuadraticMap.map_add Q, Frame.Q_expand, Frame.polar_expand]
  set x := F.coeffs v with hx
  obtain ⟨a, b⟩ := x
  simp only [blockDelta_apply]
  have hkey := dot_block M M' hMM a b
  simp only [sub_dotProduct, dotProduct_sub]
  rw [dotProduct_comm (M'ᵀ *ᵥ b) a]
  linear_combination hkey + dotProduct_comm a b

theorem Frame.levi_one (F : Frame Q T r) (v : V) : F.levi 1 1 v = v := by
  rw [Frame.levi_apply]
  have : blockDelta (1 : Matrix (Fin r) (Fin r) K) 1 (F.coeffs v) = 0 := by
    refine Prod.ext ?_ ?_ <;> simp [blockDelta_apply]
  rw [this, map_zero, add_zero]

theorem Frame.eq_one_of_levi_eq_id (F : Frame Q T r) (M M' : Matrix (Fin r) (Fin r) K)
    (h : ∀ v, F.levi M M' v = v) : M = 1 := by
  ext i j
  have h1 := h (F.e j)
  rw [Frame.levi_apply] at h1
  have h2 : F.expand (blockDelta M M' (F.coeffs (F.e j))) = 0 := by
    have := congrArg (fun x => x - F.e j) h1
    simpa using this
  have h3 := congrArg (fun x => (F.coeffs x).1 i) h2
  simp only [Frame.coeffs_expand, map_zero, Prod.fst_zero, Pi.zero_apply] at h3
  rw [Frame.coeffs_apply, blockDelta_apply] at h3
  simp only [F.ef] at h3
  have hpi : (fun i => if j = i then (1 : K) else 0) = Pi.single j 1 := by
    funext k; simp [Pi.single_apply, eq_comm]
  rw [hpi, Matrix.mulVec_single_one] at h3
  simp only [Pi.sub_apply, Matrix.col_apply, Pi.single_apply] at h3
  rw [Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simpa [sub_eq_zero] using h3
  · simpa [hij, Ne.symm hij, sub_eq_zero] using h3

theorem Frame.coeffs_T (hTQ : ∀ v, Q (T v) = σ (Q v)) (F : Frame Q T r) (v : V) :
    F.coeffs (T v) = ((fun i => σ ((F.coeffs v).1 i)), (fun i => σ ((F.coeffs v).2 i))) := by
  rw [Frame.coeffs_apply, Frame.coeffs_apply]
  refine Prod.ext ?_ ?_ <;> funext i <;> simp only
  · rw [← F.Tf i, polar_semilinear T hTQ, F.Tf]
  · rw [← F.Te i, polar_semilinear T hTQ, F.Te]

theorem Frame.T_expand (F : Frame Q T r) (a b : Fin r → K) :
    T (F.expand (a, b)) = F.expand ((fun i => σ (a i)), (fun i => σ (b i))) := by
  rw [Frame.expand_apply, Frame.expand_apply, map_add, map_sum, map_sum]
  simp only [map_smulₛₗ, RingHom.coe_coe, F.Te, F.Tf]

theorem Frame.T_levi (hTQ : ∀ v, Q (T v) = σ (Q v)) (F : Frame Q T r)
    (M M' : Matrix (Fin r) (Fin r) K) (v : V) :
    T (F.levi M M' v) = F.levi (M.map σ) (M'.map σ) (T v) := by
  rw [Frame.levi_apply, Frame.levi_apply, map_add, Frame.coeffs_T hTQ]
  congr 1
  obtain ⟨a, b⟩ := F.coeffs v
  rw [blockDelta_apply]
  simp only
  rw [Frame.T_expand]
  congr 1
  rw [blockDelta_apply]
  refine Prod.ext ?_ ?_ <;> funext i
  · simp only [Pi.sub_apply, map_sub]
    have h := RingHom.map_mulVec (σ : K →+* K) M a i
    simp only [RingEquiv.coe_toRingHom, Function.comp_def] at h
    rw [h]
  · simp only [Pi.sub_apply, map_sub]
    have h := RingHom.map_mulVec (σ : K →+* K) M'ᵀ b i
    simp only [RingEquiv.coe_toRingHom, Function.comp_def, Matrix.transpose_map] at h
    rw [h]

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
