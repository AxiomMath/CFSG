module

public import Mathlib.LinearAlgebra.TensorProduct.Matrix
public import CFSG.HardMathSupport.GuralnickMalle.InvolutionRank
public import CFSG.LieType.SpecialLinear.PairedTensor.Basic

public section

namespace CFSG.LieType.SpecialLinear

open Matrix
open scoped Kronecker TensorProduct

variable {F : Type*} [Field F] [CharP F 2]

section MatrixRank

variable {m n : Type*} [Fintype m] [Fintype n]

omit [CharP F 2] in
theorem matrix_rank_map_ringEquiv (σ : F ≃+* F) (M : Matrix m n F) :
    (M.map σ).rank = M.rank := by
  classical
  let S : Submodule F (m → F) := Submodule.span F (Set.range M.col)
  let B : Module.Basis (Fin (Module.finrank F S)) F S := Module.finBasis F S
  let b : Fin (Module.finrank F S) → (m → F) := fun i => (B i : m → F)
  have hb : LinearIndependent F b :=
    B.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  let j : (m → F) →+ (m → F) :=
    { toFun := fun v i => σ (v i)
      map_zero' := by ext i; simp
      map_add' := fun v w => by ext i; simp }
  have hj_smul : ∀ (c : F) (v : m → F), j (c • v) = σ c • j v := by
    intro c v
    ext i
    simp [j, map_mul]
  have hb' : LinearIndependent F (fun i => j (b i)) :=
    hb.map_of_injective_injective (i := fun r => σ.symm r) (j := j)
      (fun r hr => σ.symm.injective (by simpa using hr))
      (fun v hv => by
        ext i
        have hi : σ (v i) = 0 := by simpa [j] using congrFun hv i
        simpa using σ.injective (by simpa using hi))
      (fun r v => by
        rw [hj_smul]
        simp)
  let L : Submodule F (m → F) := Submodule.span F (Set.range fun i => j (b i))
  let R : Submodule F (m → F) := Submodule.span F (Set.range (M.map σ).col)
  have hcol_eq : (M.map σ).col = fun l => j (M.col l) := by
    funext l i
    rfl
  have hcol : ∀ l : n, j (M.col l) ∈ L := by
    intro l
    set z : S := ⟨M.col l, Submodule.subset_span (Set.mem_range_self l)⟩
    have hrepr : (∑ i, B.repr z i • (B i : m → F)) = M.col l := by
      calc (∑ i, B.repr z i • (B i : m → F))
          = S.subtype (∑ i, B.repr z i • B i) := by
            rw [map_sum]
            simp
        _ = S.subtype z := by rw [B.sum_repr z]
        _ = M.col l := rfl
    rw [← hrepr, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hj_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let T : Submodule F (m → F) :=
    { carrier := {x | j x ∈ R}
      zero_mem' := by
        show j 0 ∈ R
        rw [map_zero]
        exact Submodule.zero_mem R
      add_mem' := by
        intro x y hx hy
        show j (x + y) ∈ R
        rw [map_add]
        exact Submodule.add_mem R hx hy
      smul_mem' := by
        intro c x hx
        show j (c • x) ∈ R
        rw [hj_smul]
        exact Submodule.smul_mem R _ hx }
  have hT : S ≤ T := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, rfl⟩
    show j (M.col l) ∈ R
    have h : (M.map σ).col l ∈ R := Submodule.subset_span (Set.mem_range_self l)
    simpa [hcol_eq] using h
  have hLHS : L ≤ R := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hT (B i).2
  have hRHS : R ≤ L := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, rfl⟩
    simpa [hcol_eq] using hcol l
  have hspan : L = R := le_antisymm hLHS hRHS
  calc (M.map σ).rank
      = Module.finrank F R := by
        rw [Matrix.rank_eq_finrank_span_cols]
    _ = Module.finrank F L := by rw [hspan]
    _ = Fintype.card (Fin (Module.finrank F S)) := by
        simpa [L] using finrank_span_eq_card hb'
    _ = Module.finrank F S := by simp
    _ = M.rank := by
        rw [Matrix.rank_eq_finrank_span_cols M]

end MatrixRank

section TensorRank

open CFSG.HardMathSupport.GuralnickMalle

theorem two_mul_rank_mul_sub_rank_le_rank_kronecker_map_sub_one {n : ℕ}
    (σ : F ≃+* F) (a : GL (Fin n) F) (ha : a * a = 1) :
    2 * (((a : Matrix (Fin n) (Fin n) F) - 1).rank) *
        (n - ((a : Matrix (Fin n) (Fin n) F) - 1).rank) ≤
      (((a : Matrix (Fin n) (Fin n) F) ⊗ₖ
        ((a : Matrix (Fin n) (Fin n) F).map σ)) - 1).rank := by
  classical
  let A : Matrix (Fin n) (Fin n) F := a
  let S : Matrix (Fin n) (Fin n) F := A.map σ
  let j : ℕ := (A - 1).rank
  have hA : A * A = 1 := by
    have h : ((a * a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
      rw [ha]
      rfl
    simpa [A] using h
  have hS : S * S = 1 := by
    change (A.map σ) * (A.map σ) = 1
    rw [← Matrix.map_mul, hA, Matrix.map_one σ (map_zero σ) (map_one σ)]
  have hT : (Matrix.toLin' A).comp (Matrix.toLin' A) = 1 := by
    change Matrix.toLin' A * Matrix.toLin' A = 1
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hA, Matrix.toLin'_one]
    rfl
  have hU : (Matrix.toLin' S).comp (Matrix.toLin' S) = 1 := by
    change Matrix.toLin' S * Matrix.toLin' S = 1
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hS, Matrix.toLin'_one]
    rfl
  have hTsub : Matrix.toLin' (A - 1) = Matrix.toLin' A - 1 := by
    ext v
    simp [Matrix.toLin'_apply]
  have hSsub : S - 1 = (A - 1).map σ := by
    change A.map σ - 1 = (A - 1).map σ
    rw [Matrix.map_sub σ (map_sub σ), Matrix.map_one σ (map_zero σ) (map_one σ)]
  have hUSsub : Matrix.toLin' (S - 1) = Matrix.toLin' S - 1 := by
    ext v
    simp [Matrix.toLin'_apply]
  have hrankT : Module.finrank F (LinearMap.range (Matrix.toLin' A - 1)) = j := by
    have h := Matrix.rank_eq_finrank_range_toLin (A - 1)
      (Pi.basisFun F (Fin n)) (Pi.basisFun F (Fin n))
    rw [Matrix.toLin_eq_toLin', hTsub] at h
    rw [← h]
  have hrankU : Module.finrank F (LinearMap.range (Matrix.toLin' S - 1)) = j := by
    have h := Matrix.rank_eq_finrank_range_toLin (S - 1)
      (Pi.basisFun F (Fin n)) (Pi.basisFun F (Fin n))
    rw [Matrix.toLin_eq_toLin', hUSsub] at h
    rw [← h, hSsub, matrix_rank_map_ringEquiv]
  let b : Module.Basis (Fin n) F (Fin n → F) := Pi.basisFun F (Fin n)
  let b2 : Module.Basis (Fin n × Fin n) F
      ((Fin n → F) ⊗[F] (Fin n → F)) := b.tensorProduct b
  have hkron : Matrix.toLin b2 b2 (A ⊗ₖ S) =
      TensorProduct.map (Matrix.toLin' A) (Matrix.toLin' S) := by
    rw [Matrix.toLin_kronecker]
    rfl
  have hkron_sub : Matrix.toLin b2 b2 (A ⊗ₖ S - 1) =
      TensorProduct.map (Matrix.toLin' A) (Matrix.toLin' S) - 1 := by
    rw [map_sub, hkron, Matrix.toLin_one, Module.End.one_eq_id]
  have hrankK : (A ⊗ₖ S - 1).rank =
      Module.finrank F
        (LinearMap.range (TensorProduct.map (Matrix.toLin' A) (Matrix.toLin' S) - 1)) := by
    rw [Matrix.rank_eq_finrank_range_toLin (A ⊗ₖ S - 1) b2 b2, hkron_sub]
  have hfin : Module.finrank F (Fin n → F) = n := Module.finrank_fin_fun F
  have htensor := finrank_range_tensor_sub_one_add_ge
    (Matrix.toLin' A) hT (Matrix.toLin' S) hU
  have h2 : 2 * j * n ≤
      Module.finrank F
        (LinearMap.range (TensorProduct.map (Matrix.toLin' A) (Matrix.toLin' S) - 1)) +
        2 * j * j := by
    rw [hrankT, hrankU, hfin] at htensor
    simpa [show 2 * j * n = j * n + j * n by ring] using htensor
  have hjm : j ≤ n := by
    have h := Matrix.rank_le_height (A - 1)
    simpa [j] using h
  have hmain := two_mul_mul_sub_le hjm h2
  simpa [A, S, j, hrankK] using hmain

theorem two_mul_sub_two_le_rank_kronecker_map_sub_one {n : ℕ}
    (σ : F ≃+* F) (a : GL (Fin n) F) (ha : a * a = 1) (ha1 : a ≠ 1) :
    2 * n - 2 ≤
      (((a : Matrix (Fin n) (Fin n) F) ⊗ₖ
        ((a : Matrix (Fin n) (Fin n) F).map σ)) - 1).rank := by
  classical
  let A : Matrix (Fin n) (Fin n) F := a
  let S : Matrix (Fin n) (Fin n) F := A.map σ
  let j : ℕ := (A - 1).rank
  have hA : A * A = 1 := by
    have h : ((a * a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
      rw [ha]
      rfl
    simpa [A] using h
  have hbound : 2 * j * (n - j) ≤ (A ⊗ₖ S - 1).rank := by
    simpa [A, S, j] using
      two_mul_rank_mul_sub_rank_le_rank_kronecker_map_sub_one σ a ha
  have hTsub : Matrix.toLin' (A - 1) = Matrix.toLin' A - 1 := by
    ext v
    simp [Matrix.toLin'_apply]
  have hrankT : Module.finrank F (LinearMap.range (Matrix.toLin' A - 1)) = j := by
    have h := Matrix.rank_eq_finrank_range_toLin (A - 1)
      (Pi.basisFun F (Fin n)) (Pi.basisFun F (Fin n))
    rw [Matrix.toLin_eq_toLin', hTsub] at h
    rw [← h]
  have hjpos : 1 ≤ j := by
    by_contra hlt
    have hj0 : j = 0 := Nat.eq_zero_of_not_pos hlt
    have hT1 : Matrix.toLin' A = 1 := by
      have hrange0 : LinearMap.range (Matrix.toLin' A - 1) = ⊥ := by
        apply Submodule.finrank_eq_zero.mp
        rw [hrankT, hj0]
      exact sub_eq_zero.mp (LinearMap.range_eq_bot.mp hrange0)
    have hA1 : A = 1 := by
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_one]
      simpa [Module.End.one_eq_id] using hT1
    exact ha1 (by
      apply Units.ext
      simpa [A] using hA1)
  have h2j : 2 * j ≤ n := by
    have hsq : (A - 1) * (A - 1) = 0 := sub_one_mul_sub_one_eq_zero_of_mul_self A hA
    have hsqT : (Matrix.toLin' A - 1).comp (Matrix.toLin' A - 1) = 0 := by
      rw [← hTsub, ← Matrix.toLin'_mul, hsq]
      simp
    have hle : LinearMap.range (Matrix.toLin' A - 1) ≤
        LinearMap.ker (Matrix.toLin' A - 1) := by
      rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      simpa [LinearMap.comp_apply] using DFunLike.congr_fun hsqT y
    have hjk : j ≤ Module.finrank F (LinearMap.ker (Matrix.toLin' A - 1)) := by
      rw [show j = Module.finrank F (LinearMap.range (Matrix.toLin' A - 1)) from hrankT.symm]
      exact Submodule.finrank_mono hle
    have hnull : j + Module.finrank F (LinearMap.ker (Matrix.toLin' A - 1)) = n := by
      have h := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' A - 1)
      rw [Module.finrank_fin_fun F] at h
      simpa [j, hrankT] using h
    calc 2 * j = j + j := by ring
      _ ≤ j + Module.finrank F (LinearMap.ker (Matrix.toLin' A - 1)) :=
          Nat.add_le_add_left hjk j
      _ = n := hnull
  have hmain := two_mul_sub_two_le hjpos h2j hbound
  simpa [A, S] using hmain

end TensorRank

end CFSG.LieType.SpecialLinear
