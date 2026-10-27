module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open CFSG.Open
open Module
open scoped Matrix

@[expose] def slMatrices (m : ℕ) (K : Type) [Field K] :
    Submodule K (Matrix (Fin m) (Fin m) K) :=
  LinearMap.ker (Matrix.traceLinearMap (Fin m) K K)

@[expose] def slScalars (m : ℕ) (K : Type) [Field K] : Submodule K (slMatrices m K) :=
  (Submodule.span K {(1 : Matrix (Fin m) (Fin m) K)}).comap (slMatrices m K).subtype

abbrev AdjointHeart (m : ℕ) (K : Type) [Field K] :=
  slMatrices m K ⧸ slScalars m K

@[expose] noncomputable def conjMatricesLinearMap (m : ℕ) (K : Type) [Field K]
    (g : GL (Fin m) K) :
    Matrix (Fin m) (Fin m) K →ₗ[K] Matrix (Fin m) (Fin m) K :=
  (LinearMap.mulLeft K (g : Matrix (Fin m) (Fin m) K)) ∘ₗ
    (LinearMap.mulRight K ((g⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K))

theorem conjMatricesLinearMap_apply (m : ℕ) (K : Type) [Field K] (g : GL (Fin m) K)
    (X : Matrix (Fin m) (Fin m) K) :
    conjMatricesLinearMap m K g X =
      (g : Matrix (Fin m) (Fin m) K) * X *
        ((g⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
  simp [conjMatricesLinearMap, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, mul_assoc]

theorem conj_mem_slMatrices {m : ℕ} {K : Type} [Field K] (g : GL (Fin m) K)
    {X : Matrix (Fin m) (Fin m) K} (hX : X ∈ slMatrices m K) :
    (g : Matrix (Fin m) (Fin m) K) * X *
        ((g⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) ∈ slMatrices m K := by
  rw [slMatrices, LinearMap.mem_ker, Matrix.traceLinearMap_apply] at hX ⊢
  rw [Matrix.trace_units_conj, hX]

@[expose] noncomputable def adjointMatricesRep (m : ℕ) (K : Type) [Field K] :
    Representation K (GL (Fin m) K) (slMatrices m K) where
  toFun g :=
    (conjMatricesLinearMap m K g).restrict
      (fun X hX => by simpa [conjMatricesLinearMap_apply] using conj_mem_slMatrices g hX)
  map_one' := by
    apply LinearMap.ext
    intro X
    apply Subtype.ext
    simp [conjMatricesLinearMap_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro X
    apply Subtype.ext
    simp [conjMatricesLinearMap_apply, mul_assoc]

theorem adjointMatricesRep_mem_slScalars (m : ℕ) (K : Type) [Field K]
    (g : GL (Fin m) K) {X : slMatrices m K} (hX : X ∈ slScalars m K) :
    adjointMatricesRep m K g X ∈ slScalars m K := by
  rw [slScalars, Submodule.mem_comap] at hX ⊢
  rw [Submodule.mem_span_singleton] at hX ⊢
  obtain ⟨c, hc⟩ := hX
  refine ⟨c, ?_⟩
  change c • 1 = conjMatricesLinearMap m K g (X : Matrix (Fin m) (Fin m) K)
  rw [conjMatricesLinearMap_apply]
  have hX' : (X : Matrix (Fin m) (Fin m) K) = c • 1 := hc.symm
  rw [hX']
  simp

@[expose] noncomputable def adjointHeartRep (m : ℕ) (K : Type) [Field K] :
    Representation K (GL (Fin m) K) (AdjointHeart m K) :=
  (adjointMatricesRep m K).quotient (slScalars m K)
    (fun g _ hX => adjointMatricesRep_mem_slScalars m K g hX)

theorem adjointHeartRep_mk {m : ℕ} {K : Type} [Field K] (g : GL (Fin m) K)
    (X : slMatrices m K) :
    adjointHeartRep m K g (Submodule.Quotient.mk X) =
      Submodule.Quotient.mk ⟨(g : Matrix (Fin m) (Fin m) K) *
        (X : Matrix (Fin m) (Fin m) K) *
        ((g⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K),
        conj_mem_slMatrices g X.2⟩ := by
  rw [adjointHeartRep, Representation.quotient_apply, Submodule.mapQ_apply]
  congr 1
  apply Subtype.ext
  simp [adjointMatricesRep, conjMatricesLinearMap_apply]

theorem adjointHeartRep_sub_one_mk (m : ℕ) (K : Type) [Field K] (g : GL (Fin m) K)
    (X : slMatrices m K) :
    (adjointHeartRep m K g - 1) (Submodule.Quotient.mk X) =
      Submodule.Quotient.mk ⟨(g : Matrix (Fin m) (Fin m) K) *
          (X : Matrix (Fin m) (Fin m) K) *
          ((g⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) -
        (X : Matrix (Fin m) (Fin m) K),
        Submodule.sub_mem (slMatrices m K) (conj_mem_slMatrices g X.2) X.2⟩ := by
  rw [LinearMap.sub_apply, adjointHeartRep_mk, Module.End.one_apply,
    ← Submodule.Quotient.mk_sub]
  congr 1

theorem adjointHeartRep_mul_sub_one_mk (m : ℕ) (K : Type) [Field K]
    (a b : GL (Fin m) K) (X : slMatrices m K) :
    ((adjointHeartRep m K a - 1) * (adjointHeartRep m K b - 1))
        (Submodule.Quotient.mk X) =
      Submodule.Quotient.mk ⟨(a : Matrix (Fin m) (Fin m) K) *
            ((b : Matrix (Fin m) (Fin m) K) * (X : Matrix (Fin m) (Fin m) K) *
              ((b⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) *
            ((a⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) -
          ((b : Matrix (Fin m) (Fin m) K) * (X : Matrix (Fin m) (Fin m) K) *
            ((b⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) -
          ((a : Matrix (Fin m) (Fin m) K) * (X : Matrix (Fin m) (Fin m) K) *
            ((a⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) +
          (X : Matrix (Fin m) (Fin m) K),
        Submodule.add_mem (slMatrices m K)
          (Submodule.sub_mem (slMatrices m K)
            (Submodule.sub_mem (slMatrices m K)
              (conj_mem_slMatrices a
                (conj_mem_slMatrices b X.2))
              (conj_mem_slMatrices b X.2))
            (conj_mem_slMatrices a X.2))
          X.2⟩ := by
  rw [Module.End.mul_apply, adjointHeartRep_sub_one_mk, adjointHeartRep_sub_one_mk]
  congr 1
  apply Subtype.ext
  noncomm_ring

theorem adjointHeartRep_quadratic_iff {m : ℕ} {K : Type} [Field K]
    (a b : GL (Fin m) K) :
    (adjointHeartRep m K a - 1) * (adjointHeartRep m K b - 1) = 0 ↔
      ∀ X ∈ slMatrices m K, ∃ c : K,
        (a : Matrix (Fin m) (Fin m) K) *
            ((b : Matrix (Fin m) (Fin m) K) * X *
              ((b⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) *
            ((a⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) -
          (b : Matrix (Fin m) (Fin m) K) * X *
            ((b⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) -
          (a : Matrix (Fin m) (Fin m) K) * X *
            ((a⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) +
          X = c • 1 := by
  constructor
  · intro h X hX
    let Xs : slMatrices m K := ⟨X, hX⟩
    have h0 : ((adjointHeartRep m K a - 1) * (adjointHeartRep m K b - 1))
        (Submodule.Quotient.mk Xs) = 0 := by rw [h]; rfl
    rw [adjointHeartRep_mul_sub_one_mk] at h0
    rw [Submodule.Quotient.mk_eq_zero] at h0
    rw [slScalars, Submodule.mem_comap, Submodule.mem_span_singleton] at h0
    obtain ⟨c, hc⟩ := h0
    refine ⟨c, ?_⟩
    simpa using hc.symm
  · intro h
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H X =>
      obtain ⟨c, hc⟩ := h (X : Matrix (Fin m) (Fin m) K) X.2
      rw [adjointHeartRep_mul_sub_one_mk, LinearMap.zero_apply,
        Submodule.Quotient.mk_eq_zero]
      rw [slScalars, Submodule.mem_comap, Submodule.mem_span_singleton]
      exact ⟨c, hc.symm⟩

theorem inv_eq_of_mul_self_eq_one {G : Type*} [Group G] {a : G} (h : a * a = 1) :
    a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right h

theorem matrix_add_self_eq_zero {K : Type*} [Field K] [CharP K 2] {m : ℕ}
    (X : Matrix (Fin m) (Fin m) K) : X + X = 0 := by
  ext i j
  exact CharTwo.add_self_eq_zero (X i j)

theorem matrix_sub_eq_add {K : Type*} [Field K] [CharP K 2] {m : ℕ}
    (X Y : Matrix (Fin m) (Fin m) K) : X - Y = X + Y := by
  ext i j
  exact CharTwo.sub_eq_add (X i j) (Y i j)

theorem sub_one_mul_self_eq_zero_of_mul_self_eq_one {K : Type*} [Field K] [CharP K 2]
    {m : ℕ} {a : GL (Fin m) K} (ha : a * a = 1) :
    ((a : Matrix (Fin m) (Fin m) K) - 1) *
        ((a : Matrix (Fin m) (Fin m) K) - 1) = 0 := by
  let A : Matrix (Fin m) (Fin m) K := (a : Matrix (Fin m) (Fin m) K)
  let N : Matrix (Fin m) (Fin m) K := A - 1
  have hA2 : A * A = 1 := by
    simpa [A] using congrArg (fun g : GL (Fin m) K => (g : Matrix (Fin m) (Fin m) K)) ha
  have hAeq : A = 1 + N := by
    dsimp [N]
    abel
  have hAA : (1 + N) * (1 + N) = 1 := by simpa [hAeq] using hA2
  have hexp : (1 + N) * (1 + N) = 1 + N * N := by
    calc (1 + N) * (1 + N) = 1 + (N + N) + N * N := by noncomm_ring
      _ = 1 + N * N := by rw [matrix_add_self_eq_zero, add_zero]
  rw [hexp] at hAA
  have hN2 : N * N = 0 := by
    have h : 1 + N * N = 1 + 0 := by simpa using hAA
    exact add_left_cancel h
  simpa [N, A] using hN2

theorem sub_one_mul_sub_one_comm_of_mul_comm {K : Type*} [Field K] {m : ℕ}
    {A B : Matrix (Fin m) (Fin m) K} (h : A * B = B * A) :
    (A - 1) * (B - 1) = (B - 1) * (A - 1) := by
  calc (A - 1) * (B - 1) = A * B - A - B + 1 := by noncomm_ring
    _ = B * A - A - B + 1 := by rw [h]
    _ = (B - 1) * (A - 1) := by noncomm_ring

theorem conj_sub_one_eq_of_eq_one_add {K : Type*} [Field K] [CharP K 2] {m : ℕ}
    {A N X : Matrix (Fin m) (Fin m) K} (hA : A = 1 + N) :
    A * X * A + X = N * X + X * N + N * X * N := by
  rw [hA]
  calc (1 + N) * X * (1 + N) + X = (X + X) + (N * X + X * N + N * X * N) := by
        noncomm_ring
    _ = N * X + X * N + N * X * N := by
        rw [matrix_add_self_eq_zero, zero_add]

theorem conj_sub_one_comp_eq_of_nilpotent {K : Type*} [Field K] [CharP K 2] {m : ℕ}
    {A B N M X : Matrix (Fin m) (Fin m) K} (hA : A = 1 + N) (hB : B = 1 + M)
    (hNM : N * M = 0) (hMN : M * N = 0) :
    A * (B * X * B) * A + B * X * B + A * X * A + X = N * X * M + M * X * N := by
  let Y : Matrix (Fin m) (Fin m) K := B * X * B + X
  have hY : Y = M * X + X * M + M * X * M := by
    dsimp [Y]
    rw [hB]
    exact conj_sub_one_eq_of_eq_one_add (A := 1 + M) (N := M) (X := X) rfl
  have hT : A * Y * A + Y = N * Y + Y * N + N * Y * N :=
    conj_sub_one_eq_of_eq_one_add (A := A) (N := N) (X := Y) hA
  have hL : A * (B * X * B) * A + B * X * B + A * X * A + X = A * Y * A + Y := by
    dsimp [Y]
    noncomm_ring
  rw [hL, hT, hY]
  simp only [mul_add, add_mul, ← mul_assoc, hNM, zero_mul,
    add_zero, zero_add]
  simp only [mul_assoc, hMN, mul_zero, add_zero]

theorem vecMulVec_mulVec_apply {K : Type*} [Field K] {m : ℕ}
    (w φ v : Fin m → K) :
    Matrix.vecMulVec w φ *ᵥ v = (φ ⬝ᵥ v) • w := by
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Finset.mul_sum,
    mul_comm, mul_left_comm]

theorem notMem_span_three_of_nilpotent {K : Type*} [Field K] {m : ℕ}
    (N M : Matrix (Fin m) (Fin m) K) (w : Fin m → K)
    (hN2 : N * N = 0) (hM2 : M * M = 0) (hNM : N * M = M * N)
    (hne : N *ᵥ (M *ᵥ w) ≠ 0) :
    N *ᵥ (M *ᵥ w) ∉
      Submodule.span K ({w, N *ᵥ w, M *ᵥ w} : Set (Fin m → K)) := by
  intro hmem
  let P : Matrix (Fin m) (Fin m) K := N * M
  let u : Fin m → K := N *ᵥ (M *ᵥ w)
  rw [show ({w, N *ᵥ w, M *ᵥ w} : Set (Fin m → K)) =
      insert w (insert (N *ᵥ w) {M *ᵥ w}) from rfl] at hmem
  rw [Submodule.mem_span_insert] at hmem
  obtain ⟨α, y, hy, hyeq⟩ := hmem
  rw [Submodule.mem_span_insert] at hy
  obtain ⟨β, z, hz, hzeq⟩ := hy
  rw [Submodule.mem_span_singleton] at hz
  obtain ⟨γ, hγ⟩ := hz
  have hrel : u = α • w + (β • (N *ᵥ w) + γ • (M *ᵥ w)) := by
    dsimp [u]
    rw [hyeq, hzeq, ← hγ]
  have hPw : P *ᵥ w = u := by
    dsimp [P, u]
    rw [← Matrix.mulVec_mulVec]
  have hPN : P * N = 0 := by
    dsimp [P]
    rw [mul_assoc, ← hNM, ← mul_assoc, hN2, zero_mul]
  have hPM : P * M = 0 := by
    dsimp [P]
    rw [mul_assoc, hM2, mul_zero]
  have hP2 : P * P = 0 := by
    dsimp [P]
    calc (N * M) * (N * M) = N * (M * N) * M := by noncomm_ring
      _ = N * (N * M) * M := by rw [hNM]
      _ = (N * N) * (M * M) := by noncomm_ring
      _ = 0 := by rw [hN2, zero_mul]
  have hLHS : P *ᵥ u = 0 := by
    rw [← hPw, Matrix.mulVec_mulVec, hP2, Matrix.zero_mulVec]
  have hNterm : P *ᵥ (N *ᵥ w) = 0 := by
    rw [Matrix.mulVec_mulVec, hPN, Matrix.zero_mulVec]
  have hMterm : P *ᵥ (M *ᵥ w) = 0 := by
    rw [Matrix.mulVec_mulVec, hPM, Matrix.zero_mulVec]
  have hαeq : P *ᵥ (α • w + (β • (N *ᵥ w) + γ • (M *ᵥ w))) =
      α • (P *ᵥ w) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hNterm, hMterm]
    simp
  have hPrel := congrArg (fun v => P *ᵥ v) hrel
  rw [hLHS, hαeq] at hPrel
  have hα0 : α = 0 := by
    rcases smul_eq_zero.mp hPrel.symm with h | h
    · exact h
    · exact absurd (hPw.symm.trans h) hne
  have hrel' : u = β • (N *ᵥ w) + γ • (M *ᵥ w) := by
    simpa [hα0] using hrel
  have hMM : M *ᵥ (M *ᵥ w) = 0 := by
    rw [Matrix.mulVec_mulVec, hM2, Matrix.zero_mulVec]
  have hMNterm : M *ᵥ (N *ᵥ w) = P *ᵥ w := by
    dsimp [P]
    rw [Matrix.mulVec_mulVec, ← hNM]
  have hM_u : M *ᵥ u = 0 := by
    dsimp [u]
    rw [Matrix.mulVec_mulVec, ← hNM]
    exact hMterm
  have hβeq : M *ᵥ (β • (N *ᵥ w) + γ • (M *ᵥ w)) = β • (P *ᵥ w) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hMNterm, hMM]
    simp
  have hMrel := congrArg (fun v => M *ᵥ v) hrel'
  rw [hM_u, hβeq] at hMrel
  have hβ0 : β = 0 := by
    rcases smul_eq_zero.mp hMrel.symm with h | h
    · exact h
    · exact absurd (hPw.symm.trans h) hne
  have hrel'' : u = γ • (M *ᵥ w) := by
    simpa [hβ0] using hrel'
  have hN_u : N *ᵥ u = 0 := by
    dsimp [u]
    rw [Matrix.mulVec_mulVec, hN2, Matrix.zero_mulVec]
  have hγeq : N *ᵥ (γ • (M *ᵥ w)) = γ • u := by
    rw [Matrix.mulVec_smul]
  have hNrel := congrArg (fun v => N *ᵥ v) hrel''
  rw [hN_u, hγeq] at hNrel
  have hγ0 : γ = 0 := by
    rcases smul_eq_zero.mp hNrel.symm with h | h
    · exact h
    · exact absurd h hne
  have hu0 : u = 0 := by simpa [hγ0] using hrel''
  have hune : u ≠ 0 := by simpa [u] using hne
  exact hune hu0

theorem LinearMap.exists_eq_smul_of_ker_le {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {f g : V →ₗ[K] K} (hf : f ≠ 0)
    (h : LinearMap.ker f ≤ LinearMap.ker g) :
    ∃ lam : K, g = lam • f := by
  have hex : ∃ u, f u ≠ 0 := by
    by_contra hnone
    push Not at hnone
    exact hf (LinearMap.ext fun u => by simpa using hnone u)
  obtain ⟨u, hu⟩ := hex
  refine ⟨g u / f u, ?_⟩
  apply LinearMap.ext
  intro v
  have hmem : v - (f v / f u) • u ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker]
    simp only [map_sub, map_smul, smul_eq_mul]
    field_simp [hu]
    ring
  have hgmem : g (v - (f v / f u) • u) = 0 := by
    simpa [LinearMap.mem_ker] using h hmem
  simp only [map_sub, map_smul, smul_eq_mul, LinearMap.smul_apply] at hgmem ⊢
  field_simp [hu] at hgmem ⊢
  ring_nf at hgmem ⊢
  linear_combination hgmem

theorem exists_smul_eq_of_forall_dotProduct_eq_zero {K : Type*} [Field K] {m : ℕ}
    {w z : Fin m → K} (hw : w ≠ 0)
    (h : ∀ φ : Fin m → K, φ ⬝ᵥ w = 0 → φ ⬝ᵥ z = 0) :
    ∃ lam : K, z = lam • w := by
  let f : Module.Dual K (Fin m → K) := (dotProductEquiv K (Fin m)) w
  let g : Module.Dual K (Fin m → K) := (dotProductEquiv K (Fin m)) z
  have hf : f ≠ 0 := by
    intro h0
    apply hw
    exact (dotProductEquiv K (Fin m)).injective (by simpa [f] using h0)
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have hv' : v ⬝ᵥ w = 0 := by
      rw [dotProduct_comm]
      simpa [f, dotProductEquiv_apply_apply] using hv
    have hz := h v hv'
    simpa [g, dotProductEquiv_apply_apply, dotProduct_comm] using hz
  obtain ⟨lam, hlam⟩ := LinearMap.exists_eq_smul_of_ker_le hf hker
  refine ⟨lam, ?_⟩
  apply dotProduct_eq
  intro v
  have hlamv := congrArg (fun φ : Module.Dual K (Fin m → K) => φ v) hlam
  simpa [f, g, dotProductEquiv_apply_apply, smul_dotProduct] using hlamv

theorem quadratic_mulVec_vecMulVec {K : Type*} [Field K] [CharP K 2] {m : ℕ}
    (A B N M : Matrix (Fin m) (Fin m) K) (w ℓ : Fin m → K)
    (hA : A = 1 + N) (hB : B = 1 + M) (hNM : N * M = M * N)
    (hw : ℓ ⬝ᵥ w = 0) (hNw : ℓ ⬝ᵥ (N *ᵥ w) = 0)
    (hMw : ℓ ⬝ᵥ (M *ᵥ w) = 0) (hNMw : ℓ ⬝ᵥ (N *ᵥ (M *ᵥ w)) = 1) :
    (A * (B * Matrix.vecMulVec w ℓ * B) * A + B * Matrix.vecMulVec w ℓ * B +
        A * Matrix.vecMulVec w ℓ * A + Matrix.vecMulVec w ℓ) *ᵥ w =
      w + N *ᵥ w + M *ᵥ w + (N * M) *ᵥ w := by
  let X : Matrix (Fin m) (Fin m) K := Matrix.vecMulVec w ℓ
  have hAw : A *ᵥ w = w + N *ᵥ w := by
    rw [hA, Matrix.add_mulVec, Matrix.one_mulVec]
  have hBw : B *ᵥ w = w + M *ᵥ w := by
    rw [hB, Matrix.add_mulVec, Matrix.one_mulVec]
  have hAN : A *ᵥ (M *ᵥ w) = M *ᵥ w + (N * M) *ᵥ w := by
    rw [hA, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]
  have hBN : B *ᵥ (N *ᵥ w) = N *ᵥ w + (M * N) *ᵥ w := by
    rw [hB, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]
  have hBAw : B *ᵥ (A *ᵥ w) = w + M *ᵥ w + N *ᵥ w + (N * M) *ᵥ w := by
    rw [hAw, Matrix.mulVec_add, hBw, hBN, ← hNM]
    abel
  have hXBA : X *ᵥ (B *ᵥ (A *ᵥ w)) = w := by
    have hNMw' : ℓ ⬝ᵥ ((N * M) *ᵥ w) = 1 := by simpa using hNMw
    dsimp [X]
    rw [vecMulVec_mulVec_apply, hBAw]
    simp [dotProduct_add, hw, hNw, hMw, hNMw', add_assoc]
  have hXw : X *ᵥ w = 0 := by
    dsimp [X]
    rw [vecMulVec_mulVec_apply, hw, zero_smul]
  have hXMw : X *ᵥ (M *ᵥ w) = 0 := by
    dsimp [X]
    rw [vecMulVec_mulVec_apply, hMw, zero_smul]
  have hXNw : X *ᵥ (N *ᵥ w) = 0 := by
    dsimp [X]
    rw [vecMulVec_mulVec_apply, hNw, zero_smul]
  have hXBw : X *ᵥ (B *ᵥ w) = 0 := by
    rw [hBw, Matrix.mulVec_add, hXw, hXMw, add_zero]
  have hXAw : X *ᵥ (A *ᵥ w) = 0 := by
    rw [hAw, Matrix.mulVec_add, hXw, hXNw, add_zero]
  have htop : (A * (B * X * B) * A) *ᵥ w =
      w + N *ᵥ w + M *ᵥ w + (N * M) *ᵥ w := by
    simp only [← Matrix.mulVec_mulVec]
    rw [hXBA, hBw, Matrix.mulVec_add, hAw, hAN]
    simp only [Matrix.mulVec_mulVec]
    abel
  have hBterm : (B * X * B) *ᵥ w = 0 := by
    simp only [← Matrix.mulVec_mulVec]
    rw [hXBw, Matrix.mulVec_zero]
  have hAterm : (A * X * A) *ᵥ w = 0 := by
    simp only [← Matrix.mulVec_mulVec]
    rw [hXAw, Matrix.mulVec_zero]
  change (A * (B * X * B) * A + B * X * B + A * X * A + X) *ᵥ w = _
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec,
    htop, hBterm, hAterm, hXw]
  simp

theorem sub_one_mul_sub_one_eq_zero_of_adjointHeart {K : Type} [Field K] [CharP K 2] {m : ℕ}
    {a b : GL (Fin m) K} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (hq : (adjointHeartRep m K a - 1) * (adjointHeartRep m K b - 1) = 0) :
    ((a : Matrix (Fin m) (Fin m) K) - 1) * ((b : Matrix (Fin m) (Fin m) K) - 1) = 0 := by
  by_contra hNM0
  let A : Matrix (Fin m) (Fin m) K := (a : Matrix (Fin m) (Fin m) K)
  let B : Matrix (Fin m) (Fin m) K := (b : Matrix (Fin m) (Fin m) K)
  let N : Matrix (Fin m) (Fin m) K := A - 1
  let M : Matrix (Fin m) (Fin m) K := B - 1
  have hA2 : A * A = 1 := by
    simpa [A] using congrArg (fun g : GL (Fin m) K => (g : Matrix (Fin m) (Fin m) K)) ha
  have hB2 : B * B = 1 := by
    simpa [B] using congrArg (fun g : GL (Fin m) K => (g : Matrix (Fin m) (Fin m) K)) hb
  have hN2 : N * N = 0 := by
    simpa [N, A] using sub_one_mul_self_eq_zero_of_mul_self_eq_one (K := K) (a := a) ha
  have hM2 : M * M = 0 := by
    simpa [M, B] using sub_one_mul_self_eq_zero_of_mul_self_eq_one (K := K) (a := b) hb
  have hAB : A * B = B * A := by
    simpa [A, B] using congrArg (fun g : GL (Fin m) K => (g : Matrix (Fin m) (Fin m) K)) hab
  have hNM : N * M = M * N := by
    simpa [N, M] using sub_one_mul_sub_one_comm_of_mul_comm hAB
  have hne_mat : N * M ≠ 0 := by simpa [N, M] using hNM0
  have hne_vec : ∃ w : Fin m → K, (N * M) *ᵥ w ≠ 0 := by
    by_contra h
    push Not at h
    apply hne_mat
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    simpa using h v
  obtain ⟨w, hw⟩ := hne_vec
  have hNMw : N *ᵥ (M *ᵥ w) ≠ 0 := by
    intro h0
    apply hw
    rw [← Matrix.mulVec_mulVec]
    exact h0
  have hnot := notMem_span_three_of_nilpotent N M w hN2 hM2 hNM hNMw
  obtain ⟨f, hfu, hfker⟩ := Submodule.exists_le_ker_of_notMem hnot
  let c0 : K := (f (N *ᵥ (M *ᵥ w)))⁻¹
  let f' : Module.Dual K (Fin m → K) := c0 • f
  let ℓ : Fin m → K := (dotProductEquiv K (Fin m)).symm f'
  have hℓ_apply (v : Fin m → K) : ℓ ⬝ᵥ v = f' v := by
    have h : (dotProductEquiv K (Fin m)) ℓ = f' := by simp [ℓ]
    simpa [dotProductEquiv_apply_apply] using congrArg (fun φ : Module.Dual K (Fin m → K) => φ v) h
  have hfw : f w = 0 := hfker (Submodule.subset_span (by simp))
  have hfNw : f (N *ᵥ w) = 0 := hfker (Submodule.subset_span (by simp))
  have hfMw : f (M *ᵥ w) = 0 := hfker (Submodule.subset_span (by simp))
  have hℓw : ℓ ⬝ᵥ w = 0 := by simp [hℓ_apply, f', hfw]
  have hℓNw : ℓ ⬝ᵥ (N *ᵥ w) = 0 := by simp [hℓ_apply, f', hfNw]
  have hℓMw : ℓ ⬝ᵥ (M *ᵥ w) = 0 := by simp [hℓ_apply, f', hfMw]
  have hℓNMw : ℓ ⬝ᵥ (N *ᵥ (M *ᵥ w)) = 1 := by
    rw [hℓ_apply]
    have hfu' : f ((N * M) *ᵥ w) ≠ 0 := by simpa [Matrix.mulVec_mulVec] using hfu
    have hc0 : c0 = (f ((N * M) *ᵥ w))⁻¹ := by simp [c0, Matrix.mulVec_mulVec]
    simp only [f', LinearMap.smul_apply, smul_eq_mul]
    rw [Matrix.mulVec_mulVec, hc0]
    exact inv_mul_cancel₀ hfu'
  let X : Matrix (Fin m) (Fin m) K := Matrix.vecMulVec w ℓ
  have hXmem : X ∈ slMatrices m K := by
    rw [slMatrices, LinearMap.mem_ker, Matrix.traceLinearMap_apply, Matrix.trace_vecMulVec]
    rw [dotProduct_comm]
    exact hℓw
  obtain ⟨cc, hcc⟩ := (adjointHeartRep_quadratic_iff a b).mp hq X hXmem
  have hAeq : A = 1 + N := by dsimp [N]; abel
  have hBeq : B = 1 + M := by dsimp [M]; abel
  have hainv : ((a⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = A := by
    have h := inv_eq_of_mul_self_eq_one ha
    simpa [A] using congrArg (fun g : GL (Fin m) K => (g : Matrix (Fin m) (Fin m) K)) h
  have hbinv : ((b⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = B := by
    have h := inv_eq_of_mul_self_eq_one hb
    simpa [B] using congrArg (fun g : GL (Fin m) K => (g : Matrix (Fin m) (Fin m) K)) h
  have hZplus : A * (B * X * B) * A + B * X * B + A * X * A + X = cc • 1 := by
    have hsub : A * (B * X * B) * A - B * X * B - A * X * A + X = cc • 1 := by
      simpa [hainv, hbinv] using hcc
    rw [matrix_sub_eq_add, matrix_sub_eq_add] at hsub
    exact hsub
  have hZw : (A * (B * X * B) * A + B * X * B + A * X * A + X) *ᵥ w =
      w + N *ᵥ w + M *ᵥ w + (N * M) *ᵥ w := by
    simpa [X] using quadratic_mulVec_vecMulVec A B N M w ℓ hAeq hBeq hNM
      hℓw hℓNw hℓMw hℓNMw
  have hℓNMw' : ℓ ⬝ᵥ ((N * M) *ᵥ w) = 1 := by simpa using hℓNMw
  have hbig : cc • w = w + N *ᵥ w + M *ᵥ w + (N * M) *ᵥ w := by
    calc cc • w = (cc • (1 : Matrix (Fin m) (Fin m) K)) *ᵥ w := by
          rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = (A * (B * X * B) * A + B * X * B + A * X * A + X) *ᵥ w := by
            rw [← hZplus]
      _ = w + N *ᵥ w + M *ᵥ w + (N * M) *ᵥ w := hZw
  have hdot := congrArg (fun v => ℓ ⬝ᵥ v) hbig
  simp [dotProduct_add, dotProduct_smul, hℓw, hℓNw, hℓMw, hℓNMw'] at hdot


theorem eq_of_add_eq_zero_of_charP_two {K V : Type*} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] {x y : V} (h : x + y = 0) : x = y := by
  have hy : -y = y := by
    have h2 : y + y = 0 := by
      have htwo : (2 : K) • y = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
      simpa [two_smul] using htwo
    exact (add_eq_zero_iff_eq_neg.mp h2).symm
  calc x = -y := add_eq_zero_iff_eq_neg.mp h
    _ = y := hy

theorem smul_eq_of_smul_eq_of_ne_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {a b : K} {v : V} (hv : v ≠ 0) (h : a • v = b • v) : a = b := by
  have hsub : (a - b) • v = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp hsub with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' hv

theorem dotProduct_eq_of_quadratic_adjointHeart {K : Type} [Field K] [CharP K 2] {m : ℕ}
    {a0 b : GL (Fin m) K} {A B N M : Matrix (Fin m) (Fin m) K}
    (hN2 : N * N = 0) (hNM0 : N * M = 0) (hMN0 : M * N = 0)
    (hAeq : A = 1 + N) (hBeq : B = 1 + M)
    (ha0 : ((a0 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = A)
    (hb0 : ((b : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = B)
    (hainv : ((a0⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = A)
    (hbinv : ((b⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = B)
    (hq : (adjointHeartRep m K a0 - 1) * (adjointHeartRep m K b - 1) = 0)
    (hNne : N ≠ 0) :
    ∀ (w φ v : Fin m → K), φ ⬝ᵥ w = 0 →
      (φ ⬝ᵥ (M *ᵥ v)) • (N *ᵥ w) = (φ ⬝ᵥ (N *ᵥ v)) • (M *ᵥ w) := by
  intro w φ v hφw
  let X : Matrix (Fin m) (Fin m) K := Matrix.vecMulVec w φ
  have hXmem : X ∈ slMatrices m K := by
    rw [slMatrices, LinearMap.mem_ker, Matrix.traceLinearMap_apply, Matrix.trace_vecMulVec]
    rw [dotProduct_comm]
    exact hφw
  obtain ⟨c, hc⟩ := (adjointHeartRep_quadratic_iff a0 b).mp hq X hXmem
  have hZc : N * X * M + M * X * N = c • 1 := by
    have hsub : A * (B * X * B) * A - B * X * B - A * X * A + X = c • 1 := by
      simpa [ha0, hb0, hainv, hbinv] using hc
    rw [matrix_sub_eq_add, matrix_sub_eq_add,
      conj_sub_one_comp_eq_of_nilpotent hAeq hBeq hNM0 hMN0] at hsub
    exact hsub
  have hex : ∃ y : Fin m → K, N *ᵥ y ≠ 0 := by
    by_contra h
    push Not at h
    apply hNne
    apply Matrix.ext_iff_mulVec.mpr
    intro y
    simpa using h y
  obtain ⟨y, hy⟩ := hex
  have hZkill : (N * X * M + M * X * N) * N = 0 := by
    noncomm_ring [hMN0, hN2]
  have hZim : (N * X * M + M * X * N) *ᵥ (N *ᵥ y) = 0 := by
    rw [Matrix.mulVec_mulVec, hZkill, Matrix.zero_mulVec]
  have hZcval := congrArg (fun Y => Y *ᵥ (N *ᵥ y)) hZc
  rw [hZim, Matrix.smul_mulVec, Matrix.one_mulVec] at hZcval
  have hc0 : c = 0 := by
    rcases smul_eq_zero.mp hZcval.symm with h | h
    · exact h
    · exact absurd h hy
  have hZ0 : N * X * M + M * X * N = 0 := by rw [hZc, hc0, zero_smul]
  have hZv : (N * X * M + M * X * N) *ᵥ v = 0 := by rw [hZ0, Matrix.zero_mulVec]
  have hZv' : (φ ⬝ᵥ (M *ᵥ v)) • (N *ᵥ w) +
      (φ ⬝ᵥ (N *ᵥ v)) • (M *ᵥ w) = 0 := by
    simpa [X, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul,
      vecMulVec_mulVec_apply] using hZv
  exact (eq_of_add_eq_zero_of_charP_two (K := K) (V := Fin m → K)) hZv'

theorem exists_smul_eq_of_quadratic_of_nilpotent {K : Type*} [Field K] [CharP K 2] {m : ℕ}
    {N M : Matrix (Fin m) (Fin m) K} (hN2 : N * N = 0)
    (hNM0 : N * M = 0) (hNne : N ≠ 0)
    (hstar : ∀ (w φ v : Fin m → K), φ ⬝ᵥ w = 0 →
      (φ ⬝ᵥ (M *ᵥ v)) • (N *ᵥ w) = (φ ⬝ᵥ (N *ᵥ v)) • (M *ᵥ w)) :
    ∃ μ : K, M = μ • N := by
  have hex : ∃ w0 : Fin m → K, N *ᵥ w0 ≠ 0 := by
    by_contra h
    push Not at h
    apply hNne
    apply Matrix.ext_iff_mulVec.mpr
    intro y
    simpa using h y
  obtain ⟨w0, hNw0⟩ := hex
  have hw0 : w0 ≠ 0 := by
    rintro rfl
    exact hNw0 (Matrix.mulVec_zero N)
  have hexφ : ∃ φ : Fin m → K, φ ⬝ᵥ w0 = 0 ∧ φ ⬝ᵥ (N *ᵥ w0) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨lam, hlam⟩ := exists_smul_eq_of_forall_dotProduct_eq_zero hw0
      (fun φ hφ => h φ hφ)
    have h1 : N *ᵥ (N *ᵥ w0) = 0 := by
      rw [Matrix.mulVec_mulVec, hN2, Matrix.zero_mulVec]
    have h2 : N *ᵥ (N *ᵥ w0) = (lam * lam) • w0 := by
      rw [hlam, Matrix.mulVec_smul, hlam, smul_smul]
    have hlam2 : (lam * lam) • w0 = 0 := by rw [← h2, h1]
    have hlam0 : lam = 0 := by
      rcases smul_eq_zero.mp hlam2 with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact h''
        · exact h''
      · exact absurd h' hw0
    exact hNw0 (by rw [hlam, hlam0, zero_smul])
  obtain ⟨φ, hφw, hφN⟩ := hexφ
  let μ : K := (φ ⬝ᵥ (N *ᵥ w0))⁻¹ * (φ ⬝ᵥ (M *ᵥ w0))
  have hMspan : M *ᵥ w0 = μ • (N *ᵥ w0) := by
    have hstar0 := hstar w0 φ w0 hφw
    rw [show μ • (N *ᵥ w0) =
        (φ ⬝ᵥ (N *ᵥ w0))⁻¹ • ((φ ⬝ᵥ (M *ᵥ w0)) • (N *ᵥ w0)) by
      dsimp [μ]
      rw [smul_smul]]
    rw [eq_inv_smul_iff₀ hφN]
    exact hstar0.symm
  have hMall : ∀ v : Fin m → K, M *ᵥ v = μ • (N *ᵥ v) := by
    intro v
    have horth : ∀ φ : Fin m → K, φ ⬝ᵥ w0 = 0 →
        φ ⬝ᵥ (M *ᵥ v - μ • (N *ᵥ v)) = 0 := by
      intro φ hφ
      have hsv := hstar w0 φ v hφ
      rw [hMspan] at hsv
      have hsv' : (φ ⬝ᵥ (M *ᵥ v)) • (N *ᵥ w0) =
          (μ * (φ ⬝ᵥ (N *ᵥ v))) • (N *ᵥ w0) := by
        simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using hsv
      have hscalar : φ ⬝ᵥ (M *ᵥ v) = μ * (φ ⬝ᵥ (N *ᵥ v)) :=
        smul_eq_of_smul_eq_of_ne_zero hNw0 hsv'
      simp [dotProduct_sub, dotProduct_smul, hscalar]
    obtain ⟨lam, hlamv⟩ := exists_smul_eq_of_forall_dotProduct_eq_zero hw0
      (fun φ hφ => horth φ hφ)
    have hNlam : N *ᵥ (M *ᵥ v - μ • (N *ᵥ v)) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, hNM0, hN2]
      simp
    have hlam0 : lam = 0 := by
      have hval : lam • (N *ᵥ w0) = 0 := by
        rw [hlamv] at hNlam
        simpa [Matrix.mulVec_smul] using hNlam
      rcases smul_eq_zero.mp hval with h | h
      · exact h
      · exact absurd h hNw0
    have hzero : M *ᵥ v - μ • (N *ᵥ v) = 0 := by simpa [hlam0] using hlamv
    exact sub_eq_zero.mp hzero
  refine ⟨μ, ?_⟩
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [Matrix.smul_mulVec]
  exact hMall v


theorem exists_smul_eq_of_adjointHeart {K : Type} [Field K] [CharP K 2] {m : ℕ}
    {A : Subgroup (GL (Fin m) K)} (hA : IsElemAbelian 2 A)
    (hq : ∀ a ∈ A, ∀ b ∈ A, (adjointHeartRep m K a - 1) * (adjointHeartRep m K b - 1) = 0) :
    ∃ N : Matrix (Fin m) (Fin m) K, ∀ a ∈ A, ∃ μ : K,
      (a : Matrix (Fin m) (Fin m) K) - 1 = μ • N := by
  by_cases hex : ∃ a0 ∈ A, (a0 : Matrix (Fin m) (Fin m) K) - 1 ≠ 0
  · obtain ⟨a0, ha0A, hNne⟩ := hex
    let N : Matrix (Fin m) (Fin m) K := (a0 : Matrix (Fin m) (Fin m) K) - 1
    have ha0sq : a0 * a0 = 1 := by simpa [pow_two] using hA.2 a0 ha0A
    have hN2 : N * N = 0 := by
      simpa [N] using sub_one_mul_self_eq_zero_of_mul_self_eq_one (K := K) (a := a0) ha0sq
    have hNne' : N ≠ 0 := by simpa [N] using hNne
    refine ⟨N, ?_⟩
    intro a ha
    let M : Matrix (Fin m) (Fin m) K := (a : Matrix (Fin m) (Fin m) K) - 1
    have hasq : a * a = 1 := by simpa [pow_two] using hA.2 a ha
    have hcomm0 : a0 * a = a * a0 := by
      have : IsMulCommutative A := hA.1
      have h := mul_comm' (⟨a0, ha0A⟩ : A) (⟨a, ha⟩ : A)
      simpa using congrArg (fun x : A => (x : GL (Fin m) K)) h
    have hNM0 : N * M = 0 := by
      simpa [N, M] using sub_one_mul_sub_one_eq_zero_of_adjointHeart ha0sq hasq hcomm0
        (hq a0 ha0A a ha)
    have hMN0 : M * N = 0 := by
      have hcomm1 : a * a0 = a0 * a := hcomm0.symm
      simpa [M, N] using sub_one_mul_sub_one_eq_zero_of_adjointHeart hasq ha0sq hcomm1
        (hq a ha a0 ha0A)
    have ha0inv : ((a0⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
        (a0 : Matrix (Fin m) (Fin m) K) := by
      have h := inv_eq_of_mul_self_eq_one ha0sq
      simpa using congrArg (fun g : GL (Fin m) K => (g : Matrix (Fin m) (Fin m) K)) h
    have hbinv : ((a⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
        (a : Matrix (Fin m) (Fin m) K) := by
      have h := inv_eq_of_mul_self_eq_one hasq
      simpa using congrArg (fun g : GL (Fin m) K => (g : Matrix (Fin m) (Fin m) K)) h
    have hstar := dotProduct_eq_of_quadratic_adjointHeart (m := m) (a0 := a0) (b := a)
      (A := (a0 : Matrix (Fin m) (Fin m) K)) (B := (a : Matrix (Fin m) (Fin m) K))
      (N := N) (M := M) hN2 hNM0 hMN0 (by dsimp [N]; abel) (by dsimp [M]; abel)
      rfl rfl ha0inv hbinv (hq a0 ha0A a ha) hNne'
    exact exists_smul_eq_of_quadratic_of_nilpotent hN2 hNM0 hNne' hstar
  · push Not at hex
    refine ⟨0, ?_⟩
    intro a ha
    refine ⟨0, ?_⟩
    rw [hex a ha, zero_smul]


theorem card_le_card_of_adjointHeart {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    {A : Subgroup (GL (Fin m) K)} (hA : IsElemAbelian 2 A)
    (hq : ∀ a ∈ A, ∀ b ∈ A, (adjointHeartRep m K a - 1) * (adjointHeartRep m K b - 1) = 0) :
    Nat.card A ≤ Nat.card K := by
  obtain ⟨N, hN⟩ := exists_smul_eq_of_adjointHeart hA hq
  by_cases hN0 : N = 0
  · have hbot : A = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      obtain ⟨μ, hμ⟩ := hN a ha
      rw [hN0, smul_zero] at hμ
      have hmat : (a : Matrix (Fin m) (Fin m) K) = 1 := sub_eq_zero.mp hμ
      exact Subgroup.mem_bot.mpr (Units.ext hmat)
    rw [hbot, Subgroup.card_bot]
    exact Nat.succ_le_of_lt Nat.card_pos
  · classical
    let μ : A → K := fun a => Classical.choose (hN a a.2)
    have hμspec : ∀ a : A, ((a : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) - 1 =
        μ a • N := fun a => Classical.choose_spec (hN a a.2)
    have hμinj : Function.Injective μ := by
      intro a b hab
      apply Subtype.ext
      apply Units.ext
      have ha := hμspec a
      have hb := hμspec b
      have hsub : ((a : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) - 1 =
          ((b : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) - 1 := by
        rw [ha, hb, hab]
      exact sub_left_injective hsub
    exact Nat.card_le_card_of_injective μ hμinj


theorem finrank_span_singleton_le_one {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (v : V) :
    finrank K (Submodule.span K ({v} : Set V)) ≤ 1 := by
  refine finrank_le_one ⟨v, Submodule.subset_span (Set.mem_singleton v)⟩ ?_
  rintro ⟨w, hw⟩
  rw [Submodule.mem_span_singleton] at hw
  obtain ⟨c, hc⟩ := hw
  exact ⟨c, Subtype.ext hc⟩

theorem finrank_range_le_finrank_range_domRestrict_add_one {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (T : V →ₗ[K] V) (W : Submodule K V) (hcodim : finrank K V ≤ finrank K W + 1) :
    finrank K (LinearMap.range T) ≤
      finrank K (LinearMap.range (T.domRestrict W)) + 1 := by
  by_cases hW : W = ⊤
  · rw [hW]
    rw [LinearMap.range_domRestrict, Submodule.map_top]
    exact Nat.le_add_right _ 1
  · obtain ⟨v, hv⟩ : ∃ v, v ∉ W := by
      by_contra h
      push Not at h
      exact hW (Submodule.eq_top_iff'.mpr fun x => h x)
    have hle : finrank K W ≤ finrank K V := by
      have h := Submodule.finrank_mono (R := K) (M := V)
        (hst := (le_top : W ≤ (⊤ : Submodule K V)))
      simpa using h
    have hlt : finrank K W < finrank K V := by
      refine lt_of_le_of_ne hle ?_
      intro heq
      exact hW ((Submodule.eq_top_iff_finrank_eq).mpr heq)
    have hquot : finrank K (V ⧸ W) = 1 := by
      rw [Submodule.finrank_quotient]
      omega
    have hsup : W ⊔ Submodule.span K {v} = ⊤ :=
      (Submodule.sup_span_singleton_eq_top_iff hv).mpr hquot
    have hrange : LinearMap.range T =
        W.map T ⊔ (Submodule.span K ({v} : Set V)).map T := by
      rw [LinearMap.range_eq_map, ← hsup, Submodule.map_sup]
    have hspan : finrank K ((Submodule.span K ({v} : Set V)).map T) ≤ 1 := by
      rw [LinearMap.map_span]
      rw [show T '' ({v} : Set V) = {T v} from Set.image_singleton]
      exact finrank_span_singleton_le_one (K := K) (T v)
    rw [hrange]
    calc finrank K (W.map T ⊔ (Submodule.span K ({v} : Set V)).map T : Submodule K V)
        ≤ finrank K (W.map T) +
            finrank K ((Submodule.span K ({v} : Set V)).map T) :=
          Submodule.finrank_add_le_finrank_add_finrank
            (s := W.map T) (t := (Submodule.span K ({v} : Set V)).map T)
      _ ≤ finrank K (W.map T) + 1 := Nat.add_le_add_left hspan _
      _ = finrank K (LinearMap.range (T.domRestrict W)) + 1 := by
          rw [LinearMap.range_domRestrict]

theorem finrank_slScalars_le_one (m : ℕ) (K : Type) [Field K] :
    finrank K (slScalars m K) ≤ 1 := by
  let W : Submodule K (Matrix (Fin m) (Fin m) K) := slMatrices m K
  let S : Submodule K W := slScalars m K
  have hle : S.map W.subtype ≤ Submodule.span K {(1 : Matrix (Fin m) (Fin m) K)} := by
    rintro x hx
    rw [Submodule.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change y ∈ slScalars m K at hy
    rw [slScalars, Submodule.mem_comap] at hy
    exact hy
  have hdim : finrank K S = finrank K (S.map W.subtype) :=
    (Submodule.finrank_map_subtype_eq W S).symm
  calc finrank K S = finrank K (S.map W.subtype) := hdim
    _ ≤ finrank K (Submodule.span K {(1 : Matrix (Fin m) (Fin m) K)}) :=
        Submodule.finrank_mono hle
    _ ≤ 1 := finrank_span_singleton_le_one (1 : Matrix (Fin m) (Fin m) K)

theorem finrank_matrix_le_slMatrices_add_one (m : ℕ) (K : Type) [Field K] :
    finrank K (Matrix (Fin m) (Fin m) K) ≤ finrank K (slMatrices m K) + 1 := by
  let tr : Matrix (Fin m) (Fin m) K →ₗ[K] K := Matrix.traceLinearMap (Fin m) K K
  have hrn := LinearMap.finrank_range_add_finrank_ker tr
  have hK1 : finrank K K ≤ 1 :=
    finrank_le_one (1 : K) (fun w => ⟨w, by simp⟩)
  have hrange : finrank K (LinearMap.range tr) ≤ 1 :=
    le_trans (Submodule.finrank_le (LinearMap.range tr)) hK1
  change finrank K (Matrix (Fin m) (Fin m) K) ≤ finrank K (LinearMap.ker tr) + 1
  omega

theorem finrank_range_conj_sub_one_le_adjointHeart {K : Type} [Field K] {m : ℕ}
    (x : GL (Fin m) K) :
    finrank K (LinearMap.range ((LinearMap.mulLeft K (x : Matrix (Fin m) (Fin m) K)) ∘ₗ
        (LinearMap.mulRight K ((x⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) -
          LinearMap.id)) ≤
      finrank K (LinearMap.range (adjointHeartRep m K x - 1)) + 2 := by
  let V : Type := Matrix (Fin m) (Fin m) K
  let T : V →ₗ[K] V :=
    (LinearMap.mulLeft K (x : Matrix (Fin m) (Fin m) K)) ∘ₗ
      (LinearMap.mulRight K ((x⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) -
        LinearMap.id
  let W : Submodule K V := slMatrices m K
  let Z : Submodule K W := slScalars m K
  let H : (W ⧸ Z) →ₗ[K] (W ⧸ Z) := adjointHeartRep m K x - 1
  have hT : T = conjMatricesLinearMap m K x - 1 := rfl
  have hTW : ∀ X ∈ W, T X ∈ W := by
    intro X hX
    rw [hT, LinearMap.sub_apply]
    have hconj : (conjMatricesLinearMap m K x) X ∈ W := by
      rw [conjMatricesLinearMap_apply]
      exact conj_mem_slMatrices x hX
    exact Submodule.sub_mem W hconj hX
  let TW : W →ₗ[K] W := T.restrict hTW
  let U : Submodule K W := LinearMap.range TW
  have hcodim : finrank K V ≤ finrank K W + 1 := by
    simpa [V, W] using finrank_matrix_le_slMatrices_add_one m K
  have hTbound : finrank K (LinearMap.range T) ≤
      finrank K (LinearMap.range (T.domRestrict W)) + 1 :=
    finrank_range_le_finrank_range_domRestrict_add_one T W hcodim
  have hmapTW : W.map T = U.map W.subtype := by
    rw [← LinearMap.range_domRestrict]
    rw [← LinearMap.subtype_comp_restrict (f := T) (p := W) (q := W) hTW]
    rw [LinearMap.range_comp]
  have hdimU : finrank K (LinearMap.range (T.domRestrict W)) = finrank K U := by
    rw [LinearMap.range_domRestrict, hmapTW, Submodule.finrank_map_subtype_eq]
  have hH_apply : ∀ X : W, H (Submodule.Quotient.mk X) = Submodule.Quotient.mk (TW X) := by
    intro X
    rw [show H = adjointHeartRep m K x - 1 from rfl, adjointHeartRep_sub_one_mk]
    congr 1
    apply Subtype.ext
    simp only [TW, T, LinearMap.restrict_apply,
      LinearMap.sub_apply]
    noncomm_ring
  have hrangeH : LinearMap.range H = U.map Z.mkQ := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      induction q using Submodule.Quotient.induction_on with
      | H X =>
        rw [hH_apply X]
        exact Submodule.mem_map.mpr ⟨TW X, ⟨X, rfl⟩, rfl⟩
    · intro hy
      rw [Submodule.mem_map] at hy
      obtain ⟨u, hu, rfl⟩ := hy
      rw [LinearMap.mem_range] at hu
      obtain ⟨X, rfl⟩ := hu
      exact ⟨Submodule.Quotient.mk X, by rw [hH_apply]; rfl⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker (K := K) (V := U)
    (Z.mkQ.domRestrict U)
  rw [LinearMap.range_domRestrict, ← hrangeH] at hrn
  have hker : LinearMap.ker (Z.mkQ.domRestrict U) = Z.comap U.subtype := by
    rw [LinearMap.ker_domRestrict, Submodule.ker_mkQ]
  let P : Submodule K W := U ⊓ Z
  have hkerdim : finrank K (Z.comap U.subtype) = finrank K P := by
    have h := Submodule.finrank_map_subtype_eq U (Z.comap U.subtype)
    rw [Submodule.map_comap_subtype] at h
    dsimp [P]
    exact h.symm
  have hkerle : finrank K (LinearMap.ker (Z.mkQ.domRestrict U)) ≤ 1 := by
    rw [hker, hkerdim]
    exact le_trans (Submodule.finrank_mono (show P ≤ Z from by dsimp [P]; exact inf_le_right))
      (finrank_slScalars_le_one m K)
  have hUbound : finrank K U ≤ finrank K (LinearMap.range H) + 1 := by
    omega
  rw [hdimU] at hTbound
  change finrank K (LinearMap.range T) ≤ finrank K (LinearMap.range H) + 2
  omega


end CFSG.HardMathSupport.GuralnickMalle
