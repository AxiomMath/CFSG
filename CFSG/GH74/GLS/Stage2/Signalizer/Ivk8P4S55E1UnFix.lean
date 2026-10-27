module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1UnRad

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem cube_eq_zero_of_mem_radFl {ι : Type} [Fintype ι] [DecidableEq ι] {H : Subgroup (GL ι K)}
    {W W' : Submodule K (ι → K)} {hWW' : W ≤ W'} {g : ↥H} (hg : g ∈ radFl H W W' hWW') :
    (((g : GL ι K) : Matrix ι ι K) - 1) * (((g : GL ι K) : Matrix ι ι K) - 1) *
      (((g : GL ι K) : Matrix ι ι K) - 1) = 0 := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  set N : Matrix ι ι K := ((g : GL ι K) : Matrix ι ι K) - 1 with hN
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  have hx : N *ᵥ x ∈ W' := by
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec]
    exact hg3 x
  have hy : N *ᵥ (N *ᵥ x) ∈ W := by
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec]
    exact hg2 _ hx
  have hz : N *ᵥ (N *ᵥ (N *ᵥ x)) = 0 := by
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec, hg1 _ hy, sub_self]
  rw [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz, map_zero,
    LinearMap.zero_apply]

theorem mul_single_apply' {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K) (a b : ι)
    (c : K) (i j : ι) : (M * single a b c) i j = if j = b then M i a * c else 0 := by
  by_cases hj : j = b
  · subst hj
    simp [mul_single_apply_same]
  · simp [mul_single_apply_of_ne c a b i j hj M, hj]

theorem single_mul_apply' {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K) (a b : ι)
    (c : K) (i j : ι) : (single a b c * M) i j = if i = a then c * M b j else 0 := by
  by_cases hi : i = a
  · subst hi
    simp [single_mul_apply_same]
  · simp [single_mul_apply_of_ne c a b i j hi M, hi]

theorem mem_unRad_of_nil (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {d : ℕ} (hd : d ≤ r)
    (g : hypSU h r ε) (N : Matrix (HypIndex r ε) (HypIndex r ε) K)
    (hgN : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = 1 + N)
    (hN : ∀ i j, N i j ≠ 0 → d ≤ fullPos j ∧
      (fullPos j < 2 * r + ε - d → fullPos i < d) ∧ fullPos i < 2 * r + ε - d) :
    g ∈ unRad h hε hd := by
  have key : ∀ y, ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y - y =
      N *ᵥ y := fun y => by
    rw [hgN, Matrix.add_mulVec, Matrix.one_mulVec, add_sub_cancel_left]
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun y => ?_⟩
  · rw [hypFlag_eq_posFlag h hε (by omega : d ≤ 2 * r + ε), mem_posFlag] at hw
    rw [← sub_eq_zero, key]
    funext i
    show ∑ j, N i j * w j = 0
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hNij : N i j = 0
    · rw [hNij, zero_mul]
    · rw [hw j (hN i j hNij).1, mul_zero]
  · rw [hypFlag_eq_posFlag h hε (by omega : 2 * r + ε - d ≤ 2 * r + ε), mem_posFlag] at hw
    rw [key, hypFlag_eq_posFlag h hε (by omega : d ≤ 2 * r + ε), mem_posFlag]
    intro i hi
    show ∑ j, N i j * w j = 0
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hNij : N i j = 0
    · rw [hNij, zero_mul]
    · have hj : ¬ fullPos j < 2 * r + ε - d := fun hj =>
        absurd ((hN i j hNij).2.1 hj) (not_lt.mpr hi)
      rw [hw j (not_lt.mp hj), mul_zero]
  · rw [key, hypFlag_eq_posFlag h hε (by omega : 2 * r + ε - d ≤ 2 * r + ε), mem_posFlag]
    intro i hi
    show ∑ j, N i j * y j = 0
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hNij : N i j = 0
    · rw [hNij, zero_mul]
    · exact absurd (hN i j hNij).2.2 (not_lt.mpr hi)


theorem card_hypIndex (r ε : ℕ) : Fintype.card (HypIndex r ε) = 2 * r + ε := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

theorem map_sub_one_matrix {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K)
    (σ : K ≃+* K) : (M - 1).map σ = M.map σ - 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.one_apply]
  split_ifs <;> simp

theorem comm_of_fix (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1) {d : ℕ} (hd : d ≤ r)
    (hc : ∀ c : K, c ^ (2 * r + ε) = 1 → ((2 * r + ε : ℕ) : K) * (1 - c) = 0 → c = 1)
    (x : semilinearSimilitudes h r ε) {g : hypSU h r ε} (hg : g ∈ unRad h hε hd)
    (hfix : semilinearAutHom h hr hε x (hypProj h r ε g) = hypProj h r ε g) :
    ((x : SemiGL (HypIndex r ε) K).left : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) - 1).map
          (x : SemiGL (HypIndex r ε) K).right =
      (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) - 1) *
        ((x : SemiGL (HypIndex r ε) K).left : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
  obtain ⟨c, hc0, hcn, hcg⟩ := fix_matrix h hr hε x g hfix
  set M : Matrix (HypIndex r ε) (HypIndex r ε) K :=
    ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) with hM
  set A : Matrix (HypIndex r ε) (HypIndex r ε) K :=
    ((x : SemiGL (HypIndex r ε) K).left : Matrix (HypIndex r ε) (HypIndex r ε) K) with hA
  set A' : Matrix (HypIndex r ε) (HypIndex r ε) K :=
    (((x : SemiGL (HypIndex r ε) K).left⁻¹ : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) with hA'
  set σ := (x : SemiGL (HypIndex r ε) K).right with hσ
  have hA'A : A' * A = 1 := Units.inv_mul _
  have hN3 := cube_eq_zero_of_mem_radFl hg
  have hnil : IsNilpotent (M - 1) := ⟨3, by rw [pow_succ, pow_two]; exact hN3⟩
  have htrN : Matrix.trace (M - 1) = 0 :=
    (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  have htr : Matrix.trace M = ((2 * r + ε : ℕ) : K) := by
    have h1 : Matrix.trace M =
        Matrix.trace (M - 1) + Matrix.trace (1 : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
      rw [← Matrix.trace_add, sub_add_cancel]
    rw [h1, htrN, zero_add, Matrix.trace_one, card_hypIndex]
  have h1 : Matrix.trace M = c * σ (Matrix.trace M) := by
    have := congrArg Matrix.trace hcg
    rw [Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_cycle, hA'A, Matrix.one_mul,
      ← AddMonoidHom.map_trace] at this
    exact this
  rw [htr, map_natCast] at h1
  have hc1 : c = 1 := hc c hcn (by linear_combination h1)
  rw [hc1, one_smul] at hcg
  have hMA : M * A = A * M.map σ := by
    calc M * A = (A * M.map σ * A') * A := by rw [← hcg]
      _ = A * M.map σ * (A' * A) := by rw [Matrix.mul_assoc]
      _ = A * M.map σ := by rw [hA'A, Matrix.mul_one]
  rw [map_sub_one_matrix, Matrix.mul_sub, Matrix.mul_one, ← hMA, Matrix.sub_mul, Matrix.one_mul]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
