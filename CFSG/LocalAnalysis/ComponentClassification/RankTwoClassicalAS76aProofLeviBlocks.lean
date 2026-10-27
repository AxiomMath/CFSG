module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

section Blocks

variable {K : Type*} [Field K] {k : ℕ}

@[expose] noncomputable def blk (X : Matrix (Fin 2) (Fin 2) K) (S : Matrix (Fin k) (Fin k) K) :
    Matrix (Fin (2 + k)) (Fin (2 + k)) K :=
  reindexAlgEquiv K K finSumFinEquiv (fromBlocks X 0 0 S)

theorem blk_mul (X X' : Matrix (Fin 2) (Fin 2) K) (S S' : Matrix (Fin k) (Fin k) K) :
    blk X S * blk X' S' = blk (X * X') (S * S') := by
  rw [blk, blk, blk, ← map_mul, fromBlocks_multiply]
  simp

theorem blk_one : blk (1 : Matrix (Fin 2) (Fin 2) K) (1 : Matrix (Fin k) (Fin k) K) = 1 := by
  rw [blk, fromBlocks_one, map_one]

theorem blk_add (X X' : Matrix (Fin 2) (Fin 2) K) (S S' : Matrix (Fin k) (Fin k) K) :
    blk X S + blk X' S' = blk (X + X') (S + S') := by
  rw [blk, blk, blk, ← map_add, fromBlocks_add]
  simp

theorem blk_smul (c : K) (X : Matrix (Fin 2) (Fin 2) K) (S : Matrix (Fin k) (Fin k) K) :
    c • blk X S = blk (c • X) (c • S) := by
  rw [blk, blk, ← map_smul, fromBlocks_smul]
  simp

theorem det_blk (X : Matrix (Fin 2) (Fin 2) K) (S : Matrix (Fin k) (Fin k) K) :
    (blk X S).det = X.det * S.det := by
  rw [blk, coe_reindexAlgEquiv, det_reindex_self, det_fromBlocks_zero₂₁]

theorem blk_injective {X X' : Matrix (Fin 2) (Fin 2) K} {S S' : Matrix (Fin k) (Fin k) K}
    (h : blk X S = blk X' S') : X = X' ∧ S = S' := by
  rw [blk, blk] at h
  have h1 := (reindexAlgEquiv K K finSumFinEquiv).injective h
  rw [fromBlocks_inj] at h1
  exact ⟨h1.1, h1.2.2.2⟩

theorem eq_reindex_fromBlocks (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) :
    ∃ A B C D, g = reindexAlgEquiv K K finSumFinEquiv (fromBlocks A B C D) := by
  set g' := (reindexAlgEquiv K K finSumFinEquiv).symm g with hg'
  refine ⟨g'.toBlocks₁₁, g'.toBlocks₁₂, g'.toBlocks₂₁, g'.toBlocks₂₂, ?_⟩
  rw [fromBlocks_toBlocks, hg', AlgEquiv.apply_symm_apply]

@[expose] noncomputable def blkSL₁ :
    SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin (2 + k)) K where
  toFun X := ⟨blk (X : Matrix (Fin 2) (Fin 2) K) 1, by rw [det_blk, X.2, det_one, mul_one]⟩
  map_one' := by
    apply Subtype.ext
    exact blk_one
  map_mul' X Y := by
    apply Subtype.ext
    change blk ((X * Y : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 =
      blk (X : Matrix (Fin 2) (Fin 2) K) 1 * blk (Y : Matrix (Fin 2) (Fin 2) K) 1
    rw [blk_mul, mul_one]
    rfl

@[expose] noncomputable def blkSL₂ :
    SpecialLinearGroup (Fin k) K →* SpecialLinearGroup (Fin (2 + k)) K where
  toFun S := ⟨blk 1 (S : Matrix (Fin k) (Fin k) K), by rw [det_blk, S.2, det_one, mul_one]⟩
  map_one' := by
    apply Subtype.ext
    exact blk_one
  map_mul' X Y := by
    apply Subtype.ext
    change blk 1 ((X * Y : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) =
      blk 1 (X : Matrix (Fin k) (Fin k) K) * blk 1 (Y : Matrix (Fin k) (Fin k) K)
    rw [blk_mul, mul_one]
    rfl

theorem coe_blkSL₁ (X : SpecialLinearGroup (Fin 2) K) :
    ((blkSL₁ X : SpecialLinearGroup (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      blk (X : Matrix (Fin 2) (Fin 2) K) 1 :=
  rfl

theorem coe_blkSL₂ (S : SpecialLinearGroup (Fin k) K) :
    ((blkSL₂ S : SpecialLinearGroup (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      blk 1 (S : Matrix (Fin k) (Fin k) K) :=
  rfl

theorem blkSL₁_commute_blkSL₂ (X : SpecialLinearGroup (Fin 2) K)
    (S : SpecialLinearGroup (Fin k) K) :
    (blkSL₁ X : SpecialLinearGroup (Fin (2 + k)) K) * blkSL₂ S = blkSL₂ S * blkSL₁ X :=
  Subtype.ext (by
    change blk (X : Matrix (Fin 2) (Fin 2) K) 1 * blk 1 (S : Matrix (Fin k) (Fin k) K) =
      blk 1 (S : Matrix (Fin k) (Fin k) K) * blk (X : Matrix (Fin 2) (Fin 2) K) 1
    rw [blk_mul, blk_mul, one_mul, mul_one, mul_one, one_mul])

theorem mem_range_blkSL₂ {g : SpecialLinearGroup (Fin (2 + k)) K}
    {X : Matrix (Fin k) (Fin k) K} (hg : (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = blk 1 X) :
    g ∈ (blkSL₂ : SpecialLinearGroup (Fin k) K →* _).range := by
  have hX : X.det = 1 := by
    have := g.2
    rw [hg, det_blk, det_one, one_mul] at this
    exact this
  refine ⟨⟨X, hX⟩, Subtype.ext ?_⟩
  change blk 1 X = (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K)
  exact hg.symm

theorem blkSL₂_injective : Function.Injective
    (blkSL₂ : SpecialLinearGroup (Fin k) K →* SpecialLinearGroup (Fin (2 + k)) K) := fun _ _ h =>
  Subtype.ext (blk_injective (congrArg Subtype.val h)).2

theorem scalar_eq_blk (c : K) :
    scalar (Fin (2 + k)) c = blk (c • (1 : Matrix (Fin 2) (Fin 2) K)) (c • 1) := by
  rw [scalar_apply, ← smul_one_eq_diagonal, ← blk_smul, blk_one]

theorem blkSL₁_injective_proj (hk : 1 ≤ k) : Function.Injective
    ((proj (2 + k) K).comp
      (blkSL₁ : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin (2 + k)) K)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro X hX
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, proj_eq_one_iff, mem_scalars] at hX
  obtain ⟨c, -, hc⟩ := hX
  rw [coe_blkSL₁, scalar_eq_blk] at hc
  have h1 := blk_injective hc
  have hc1 : (c : K) = 1 := by
    have := congrFun (congrFun h1.2 ⟨0, hk⟩) ⟨0, hk⟩
    simpa using this.symm
  simp only [hc1, one_smul] at h1
  exact Subgroup.mem_bot.mpr (Subtype.ext (h1.1.trans rfl))

theorem blkSL₂_injective_proj : Function.Injective
    ((proj (2 + k) K).comp
      (blkSL₂ : SpecialLinearGroup (Fin k) K →* SpecialLinearGroup (Fin (2 + k)) K)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro X hX
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, proj_eq_one_iff, mem_scalars] at hX
  obtain ⟨c, -, hc⟩ := hX
  rw [coe_blkSL₂, scalar_eq_blk] at hc
  have h1 := blk_injective hc
  have hc1 : (c : K) = 1 := by
    have := congrFun (congrFun h1.1 0) 0
    simpa using this.symm
  simp only [hc1, one_smul] at h1
  exact Subgroup.mem_bot.mpr (Subtype.ext (h1.2.trans rfl))

theorem exists_blk_of_commute_single {g : Matrix (Fin (2 + k)) (Fin (2 + k)) K}
    (h₁ : g * blk (single 0 1 1) (0 : Matrix (Fin k) (Fin k) K) =
      blk (single 0 1 1) (0 : Matrix (Fin k) (Fin k) K) * g)
    (h₂ : g * blk (single 1 0 1) (0 : Matrix (Fin k) (Fin k) K) =
      blk (single 1 0 1) (0 : Matrix (Fin k) (Fin k) K) * g) :
    ∃ (c : K) (D : Matrix (Fin k) (Fin k) K), g = blk (c • 1) D := by
  obtain ⟨A, B, C, D, hg⟩ := eq_reindex_fromBlocks g
  have key : ∀ (i j : Fin 2), g * blk (single i j 1) (0 : Matrix (Fin k) (Fin k) K) =
      blk (single i j 1) (0 : Matrix (Fin k) (Fin k) K) * g →
      A * single i j (1 : K) = single i j (1 : K) * A ∧ single i j (1 : K) * B = 0 ∧
        C * single i j (1 : K) = 0 := by
    intro i j h
    rw [hg, blk, ← map_mul, ← map_mul] at h
    have h' := (reindexAlgEquiv K K finSumFinEquiv).injective h
    rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h'
    obtain ⟨e1, e2, e3, -⟩ := h'
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero] at e1 e2 e3
    exact ⟨e1, e2.symm, e3⟩
  obtain ⟨hA₁, hB₁, hC₁⟩ := key 0 1 h₁
  obtain ⟨hA₂, hB₂, hC₂⟩ := key 1 0 h₂
  have hB : B = 0 := by
    ext a b
    fin_cases a
    · have := congrFun (congrFun hB₂ 1) b
      simpa [Matrix.mul_apply, Fin.sum_univ_two, single_apply] using this
    · have := congrFun (congrFun hB₁ 0) b
      simpa [Matrix.mul_apply, Fin.sum_univ_two, single_apply] using this
  have hC : C = 0 := by
    ext a b
    fin_cases b
    · have := congrFun (congrFun hC₁ a) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_two, single_apply] using this
    · have := congrFun (congrFun hC₂ a) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_two, single_apply] using this
  obtain ⟨c, hc⟩ : A ∈ Set.range (scalar (Fin 2)) := by
    refine mem_range_scalar_of_commute_single fun i j hij => ?_
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hA₁.symm
    · exact hA₂.symm
    · exact absurd rfl hij
  refine ⟨c, D, ?_⟩
  rw [hg, hB, hC, ← hc, scalar_apply, ← smul_one_eq_diagonal, blk]

@[expose] def tr₂ (i j : Fin 2) (hij : i ≠ j) : SpecialLinearGroup (Fin 2) K :=
  ⟨1 + single i j 1, det_transvection_of_ne i j hij 1⟩

theorem coe_blkSL₁_tr₂ (i j : Fin 2) (hij : i ≠ j) :
    ((blkSL₁ (tr₂ i j hij : SpecialLinearGroup (Fin 2) K) :
      SpecialLinearGroup (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      1 + blk (single i j 1) (0 : Matrix (Fin k) (Fin k) K) := by
  rw [coe_blkSL₁, ← blk_one, blk_add, add_zero]
  rfl

theorem exists_blk_of_commute {g : SpecialLinearGroup (Fin (2 + k)) K}
    (h₁ : g * blkSL₁ (tr₂ (K := K) 0 1 (by decide)) = blkSL₁ (tr₂ (K := K) 0 1 (by decide)) * g)
    (h₂ : g * blkSL₁ (tr₂ (K := K) 1 0 (by decide)) = blkSL₁ (tr₂ (K := K) 1 0 (by decide)) * g) :
    ∃ (c : K) (D : Matrix (Fin k) (Fin k) K),
      (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = blk (c • 1) D := by
  have conv : ∀ (i j : Fin 2) (hij : i ≠ j),
      g * blkSL₁ (tr₂ (K := K) i j hij) = blkSL₁ (tr₂ (K := K) i j hij) * g →
        (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) * blk (single i j 1)
          (0 : Matrix (Fin k) (Fin k) K) =
          blk (single i j 1) (0 : Matrix (Fin k) (Fin k) K) * g := by
    intro i j hij h
    have h' := congrArg Subtype.val h
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blkSL₁_tr₂,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h'
    exact add_left_cancel h'
  exact exists_blk_of_commute_single (conv 0 1 _ h₁) (conv 1 0 _ h₂)

theorem exists_inv_blk {g : SpecialLinearGroup (Fin (2 + k)) K} {c : K}
    {D : Matrix (Fin k) (Fin k) K}
    (hg : (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = blk (c • 1) D) :
    c ≠ 0 ∧ ∃ E : Matrix (Fin k) (Fin k) K,
      ((g⁻¹ : SpecialLinearGroup (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
        blk (c⁻¹ • 1) E ∧ D * E = 1 ∧ E * D = 1 := by
  obtain ⟨A, B, C, E, hgi⟩ := eq_reindex_fromBlocks
    ((g⁻¹ : SpecialLinearGroup (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K)
  have h1 : (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *
      ((g⁻¹ : SpecialLinearGroup (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h2 : ((g⁻¹ : SpecialLinearGroup (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *
      (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [hg, hgi, blk, ← map_mul, ← blk_one, blk] at h1
  rw [hg, hgi, blk, ← map_mul, ← blk_one, blk] at h2
  have e1 := (reindexAlgEquiv K K finSumFinEquiv).injective h1
  have e2 := (reindexAlgEquiv K K finSumFinEquiv).injective h2
  rw [fromBlocks_multiply, fromBlocks_inj] at e1 e2
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one] at e1 e2
  obtain ⟨hA, hB, -, hE⟩ := e1
  obtain ⟨-, -, hC, hE'⟩ := e2
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hA
    have := congrFun (congrFun hA 0) 0
    simp at this
  have hA' : A = c⁻¹ • 1 := by
    rw [← hA, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hB' : B = 0 := by
    have : c⁻¹ • (c • B) = 0 := by rw [hB, smul_zero]
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have hC' : C = 0 := by
    have : c⁻¹ • (c • C) = 0 := by rw [hC, smul_zero]
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  refine ⟨hc, E, ?_, hE, hE'⟩
  rw [hgi, hA', hB', hC', blk]

theorem smul_one_mul_smul_one (c c' : K) :
    (c • (1 : Matrix (Fin 2) (Fin 2) K)) * (c' • 1) = (c * c') • 1 := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]

theorem conj_mem_range_blkSL₂ {g : SpecialLinearGroup (Fin (2 + k)) K} {c : K}
    {D : Matrix (Fin k) (Fin k) K}
    (hg : (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = blk (c • 1) D)
    (S : SpecialLinearGroup (Fin k) K) :
    g * blkSL₂ S * g⁻¹ ∈ (blkSL₂ : SpecialLinearGroup (Fin k) K →* _).range := by
  obtain ⟨hc, E, hE, -, -⟩ := exists_inv_blk hg
  refine mem_range_blkSL₂ (X := D * (S : Matrix (Fin k) (Fin k) K) * E) ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hg, hE, coe_blkSL₂,
    blk_mul, blk_mul, Matrix.mul_one, smul_one_mul_smul_one, mul_inv_cancel₀ hc, one_smul]

theorem commutatorElement_mem_range_blkSL₂ {g g' : SpecialLinearGroup (Fin (2 + k)) K}
    {c c' : K} {D D' : Matrix (Fin k) (Fin k) K}
    (hg : (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = blk (c • 1) D)
    (hg' : (g' : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = blk (c' • 1) D') :
    ⁅g, g'⁆ ∈ (blkSL₂ : SpecialLinearGroup (Fin k) K →* _).range := by
  obtain ⟨hc, E, hE, -, -⟩ := exists_inv_blk hg
  obtain ⟨hc', E', hE', -, -⟩ := exists_inv_blk hg'
  refine mem_range_blkSL₂ (X := D * D' * E * E') ?_
  rw [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hg, hg', hE, hE',
    blk_mul, blk_mul, blk_mul, smul_one_mul_smul_one, smul_one_mul_smul_one,
    smul_one_mul_smul_one]
  congr 1
  rw [show c * c' * c⁻¹ * c'⁻¹ = 1 by field_simp, one_smul]

end Blocks

end CFSG.ComponentClassification.RankTwoClassical
