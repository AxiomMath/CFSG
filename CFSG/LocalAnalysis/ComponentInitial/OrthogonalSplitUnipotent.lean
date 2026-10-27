module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitStabilizer
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFourRoots

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module Matrix CFSG.LieType.Universal.Spin
open scoped Pointwise

variable {r : ℕ} {K : Type*} [Field K]

theorem mem_flag_iff_coord {i : ℕ} {v : Fin r ⊕ Fin r → K} :
    v ∈ flag r K i ↔ (∀ k, v (.inr k) = 0) ∧ ∀ k : Fin r, i ≤ k → v (.inl k) = 0 := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      refine ⟨fun k => by simp, fun k hk => ?_⟩
      have hjk : j ≠ k := fun h => by
        subst h
        exact absurd hj (not_lt.2 hk)
      simp [Ne.symm hjk]
    | zero => exact ⟨fun k => rfl, fun k _ => rfl⟩
    | add x y _ _ hx hy =>
      exact ⟨fun k => by simp [hx.1 k, hy.1 k], fun k hk => by simp [hx.2 k hk, hy.2 k hk]⟩
    | smul a x _ hx => exact ⟨fun k => by simp [hx.1 k], fun k hk => by simp [hx.2 k hk]⟩
  · rintro ⟨h1, h2⟩
    have hsum : v = ∑ j : Fin r, v (.inl j) • (Pi.single (Sum.inl j) (1 : K) :
        Fin r ⊕ Fin r → K) := by
      ext c
      rcases c with c | c
      · simp [Finset.sum_apply, Pi.single_apply]
      · simp [Finset.sum_apply, h1 c]
    rw [hsum]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : (j : ℕ) < i
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · rw [h2 j (not_lt.1 hj), zero_smul]
      exact zero_mem _

theorem apply_eq_of_toMatrix' {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    {A : GL (Fin r) K} {C : Matrix (Fin r) (Fin r) K}
    (hg : LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
      fromBlocks (A : Matrix (Fin r) (Fin r) K) ((A : Matrix (Fin r) (Fin r) K) * C) 0
        ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ) (v : Fin r ⊕ Fin r → K) :
    g v = Sum.elim ((A : Matrix (Fin r) (Fin r) K) *ᵥ (v ∘ Sum.inl + C *ᵥ (v ∘ Sum.inr)))
      (((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ *ᵥ (v ∘ Sum.inr)) := by
  rw [apply_eq_toMatrix'_mulVec, hg, fromBlocks_mulVec_apply, Matrix.zero_mulVec, zero_add,
    Matrix.mulVec_add, Matrix.mulVec_mulVec]

variable (r K) in
@[expose] noncomputable def posBorel :
    Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  maxStab r K ⊓ ⨅ i : ℕ,
    MulAction.stabilizer ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (flag r K i)

theorem mem_posBorel {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} :
    g ∈ posBorel r K ↔ g ∈ maxStab r K ∧
      ∀ i : ℕ, (flag r K i).map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
        flag r K i := by
  simp only [posBorel, Subgroup.mem_inf, Subgroup.mem_iInf]
  rfl

theorem mem_posBorel_iff {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} :
    g ∈ posBorel r K ↔ ∃ (A : GL (Fin r) K) (C : Matrix (Fin r) (Fin r) K),
      (A : Matrix (Fin r) (Fin r) K).IsUpperTriangular ∧ Cᵀ = -C ∧ (∀ i, C i i = 0) ∧
      LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
        fromBlocks (A : Matrix (Fin r) (Fin r) K) ((A : Matrix (Fin r) (Fin r) K) * C) 0
          ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ := by
  constructor
  · intro hg
    obtain ⟨hS, hF⟩ := mem_posBorel.1 hg
    obtain ⟨A, C, hC, hd, hgM⟩ := exists_toMatrix'_of_mem_maxStab hS
    refine ⟨A, C, fun i j hji => ?_, hC, hd, hgM⟩
    have hmem : g (Pi.single (Sum.inl j) 1) ∈ flag r K (j + 1) := by
      rw [← hF (j + 1)]
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨j, Nat.lt_succ_self _, rfl⟩)
    have h := (mem_flag_iff_coord.1 hmem).2 i hji
    rw [apply_eq_toMatrix'_mulVec, hgM, Matrix.mulVec_single_one, Matrix.col_apply,
      fromBlocks_apply₁₁] at h
    exact h
  · rintro ⟨A, C, hA, hC, hd, hgM⟩
    refine mem_posBorel.2 ⟨mem_maxStab_of_toMatrix' A C hC hd hgM, fun i => ?_⟩
    have hle : (flag r K i).map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) ≤
        flag r K i := by
      rintro _ ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe, mem_flag_iff_coord] at hv
      have hy : v ∘ Sum.inr = 0 := funext hv.1
      rw [mem_flag_iff_coord]
      change (∀ k, g v (Sum.inr k) = 0) ∧ ∀ k : Fin r, i ≤ k → g v (Sum.inl k) = 0
      rw [apply_eq_of_toMatrix' hgM, hy, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
      refine ⟨fun k => rfl, fun k hk => ?_⟩
      simp only [Sum.elim_inl, Matrix.mulVec, dotProduct, Function.comp_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : i ≤ (j : ℕ)
      · rw [hv.2 j hj, mul_zero]
      · rw [hA (show j < k by rw [Fin.lt_def]; omega), zero_mul]
    exact Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq g _)

theorem posBorel_le_orthogonalGroup :
    posBorel r K ≤ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) :=
  fun _ hg => (mem_posBorel.1 hg).1.1

theorem toMatrix'_inl_inl_ne_zero {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hg : g ∈ posBorel r K) (i : Fin r) :
    LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K))
      (Sum.inl i) (Sum.inl i) ≠ 0 := by
  obtain ⟨A, C, hA, -, -, hgM⟩ := mem_posBorel_iff.1 hg
  rw [hgM, fromBlocks_apply₁₁]
  have hdet : (A : Matrix (Fin r) (Fin r) K).det ≠ 0 := (Matrix.isUnits_det_units A).ne_zero
  rw [det_of_isUpperTriangular hA] at hdet
  exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ i)

theorem toMatrix'_mul_inl_inl {g h : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hg : g ∈ posBorel r K) (hh : h ∈ posBorel r K) (i : Fin r) :
    LinearMap.toMatrix' ((g * h : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
        (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) (Sum.inl i) (Sum.inl i) =
      LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K))
          (Sum.inl i) (Sum.inl i) *
        LinearMap.toMatrix' (h : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K))
          (Sum.inl i) (Sum.inl i) := by
  obtain ⟨A, C, hA, -, -, hgM⟩ := mem_posBorel_iff.1 hg
  obtain ⟨A', C', hA', -, -, hhM⟩ := mem_posBorel_iff.1 hh
  rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix'_mul, hgM, hhM, fromBlocks_multiply,
    fromBlocks_apply₁₁, fromBlocks_apply₁₁, fromBlocks_apply₁₁, Matrix.mul_zero, add_zero]
  exact LinearFlag.mul_apply_self_of_isUpperTriangular hA hA' i

variable (r K) in
@[expose] noncomputable def posBorelDiag : posBorel r K →* (Fin r → Kˣ) where
  toFun g i := Units.mk0 _ (toMatrix'_inl_inl_ne_zero g.2 i)
  map_one' := by
    funext i
    refine Units.ext ?_
    change LinearMap.toMatrix' (((1 : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) :
      (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) (Sum.inl i) (Sum.inl i) = 1
    rw [show (((1 : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) :
      (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = LinearMap.id from rfl,
      LinearMap.toMatrix'_id, Matrix.one_apply_eq]
  map_mul' g h := by
    funext i
    refine Units.ext ?_
    exact toMatrix'_mul_inl_inl g.2 h.2 i

theorem coe_posBorelDiag (g : posBorel r K) (i : Fin r) :
    ((posBorelDiag r K g i : Kˣ) : K) =
      LinearMap.toMatrix' ((g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
        (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) (Sum.inl i) (Sum.inl i) :=
  rfl

@[expose] noncomputable def diagGL (d : Fin r → Kˣ) : GL (Fin r) K :=
  ⟨diagonal fun i => (d i : K), diagonal fun i => ((d i)⁻¹ : Kˣ),
    by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩

theorem torusElt_mem_posBorel (d : Fin r → Kˣ) : torusElt r K d ∈ posBorel r K := by
  refine mem_posBorel_iff.2 ⟨diagGL d, 0, Matrix.blockTriangular_diagonal _, by simp, by simp, ?_⟩
  rw [toMatrix'_torusElt]
  simp [diagGL]

theorem posBorelDiag_surjective : Function.Surjective (posBorelDiag r K) := fun d =>
  ⟨⟨torusElt r K d, torusElt_mem_posBorel d⟩, funext fun i => Units.ext (by
    rw [coe_posBorelDiag, toMatrix'_torusElt, fromBlocks_apply₁₁, diagonal_apply_eq])⟩

variable (r K) in
@[expose] noncomputable def posUnip :
    Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  (posBorelDiag r K).ker.map (posBorel r K).subtype

theorem mem_posUnip {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} :
    g ∈ posUnip r K ↔ g ∈ posBorel r K ∧
      ∀ i, LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K))
        (Sum.inl i) (Sum.inl i) = 1 := by
  constructor
  · rintro ⟨g', hker, rfl⟩
    refine ⟨g'.2, fun i => ?_⟩
    have h := congrArg Units.val (congrFun (MonoidHom.mem_ker.1 hker) i)
    simpa [coe_posBorelDiag] using h
  · rintro ⟨hg, h1⟩
    refine ⟨⟨g, hg⟩, MonoidHom.mem_ker.2 (funext fun i => Units.ext ?_), rfl⟩
    rw [coe_posBorelDiag]
    simpa using h1 i

theorem mem_posUnip_iff {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} :
    g ∈ posUnip r K ↔ ∃ (A : GL (Fin r) K) (C : Matrix (Fin r) (Fin r) K),
      (A : Matrix (Fin r) (Fin r) K).IsUpperTriangular ∧
      (∀ i, (A : Matrix (Fin r) (Fin r) K) i i = 1) ∧ Cᵀ = -C ∧ (∀ i, C i i = 0) ∧
      LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
        fromBlocks (A : Matrix (Fin r) (Fin r) K) ((A : Matrix (Fin r) (Fin r) K) * C) 0
          ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ := by
  rw [mem_posUnip, mem_posBorel_iff]
  constructor
  · rintro ⟨⟨A, C, hA, hC, hd, hgM⟩, h1⟩
    refine ⟨A, C, hA, fun i => ?_, hC, hd, hgM⟩
    have := h1 i
    rwa [hgM, fromBlocks_apply₁₁] at this
  · rintro ⟨A, C, hA, h1, hC, hd, hgM⟩
    refine ⟨⟨A, C, hA, hC, hd, hgM⟩, fun i => ?_⟩
    rw [hgM, fromBlocks_apply₁₁]
    exact h1 i

theorem posUnip_le_posBorel : posUnip r K ≤ posBorel r K := fun _ hg => (mem_posUnip.1 hg).1

theorem posBorelDiag_ker : (posBorelDiag r K).ker = (posUnip r K).subgroupOf (posBorel r K) := by
  ext g
  rw [Subgroup.mem_subgroupOf, mem_posUnip, MonoidHom.mem_ker]
  constructor
  · intro h
    refine ⟨g.2, fun i => ?_⟩
    have := congrArg Units.val (congrFun h i)
    simpa [coe_posBorelDiag] using this
  · rintro ⟨-, h1⟩
    exact funext fun i => Units.ext (by rw [coe_posBorelDiag]; simpa using h1 i)

theorem posUnip_normal : ((posUnip r K).subgroupOf (posBorel r K)).Normal := by
  rw [← posBorelDiag_ker]
  exact MonoidHom.normal_ker _

variable (r K) in
@[expose] def posUnipGens : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  {g | ∃ (i j : Fin r) (t : K), i < j ∧
      g = eichler (quadPlus r K) (Pi.single (Sum.inl i) 1) ((-t) • Pi.single (Sum.inr j) 1)} ∪
    {g | ∃ (i j : Fin r) (t : K), i < j ∧
      g = eichler (quadPlus r K) (Pi.single (Sum.inl i) 1) ((-t) • Pi.single (Sum.inl j) 1)}

@[expose] noncomputable def elemGL {i j : Fin r} (hij : i ≠ j) (t : K) : GL (Fin r) K :=
  ⟨1 + t • Matrix.single i j 1, 1 - t • Matrix.single i j 1,
    by
      rw [add_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, smul_mul_smul_comm,
        single_mul_single_of_ne (1 : K) i j i hij.symm 1, smul_zero, sub_zero]
      abel,
    by
      rw [sub_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul_comm,
        single_mul_single_of_ne (1 : K) i j i hij.symm 1, smul_zero, add_zero]
      abel⟩

theorem toMatrix'_eichler_inl_inr_eq {i j : Fin r} (hij : i ≠ j) (t : K) :
    LinearMap.toMatrix' ((eichler (quadPlus r K) (Pi.single (Sum.inl i) 1)
      ((-t) • Pi.single (Sum.inr j) 1) : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
        (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
      fromBlocks (elemGL hij t : Matrix (Fin r) (Fin r) K)
        ((elemGL hij t : Matrix (Fin r) (Fin r) K) * 0) 0
        (((elemGL hij t)⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ := by
  rw [toMatrix'_eichler_inl_inr hij]
  simp [elemGL, transpose_single]

theorem posUnip_eq_closure : posUnip r K = Subgroup.closure (posUnipGens r K) := by
  apply le_antisymm
  · intro g hg
    let InH : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K → Prop := fun M =>
      ∃ h ∈ Subgroup.closure (posUnipGens r K),
        LinearMap.toMatrix' (h : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = M
    have hmul : ∀ M N, InH M → InH N → InH (M * N) := by
      rintro _ _ ⟨h₁, h₁H, rfl⟩ ⟨h₂, h₂H, rfl⟩
      exact ⟨h₁ * h₂, mul_mem h₁H h₂H, by
        rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix'_mul]⟩
    have hone : InH 1 := ⟨1, one_mem _, by
      rw [← LinearMap.toMatrix'_id]
      rfl⟩
    have hinv : ∀ M, InH M → InH M⁻¹ := by
      rintro _ ⟨h, hH, rfl⟩
      refine ⟨h⁻¹, inv_mem hH, (Matrix.inv_eq_left_inv ?_).symm⟩
      rw [← LinearMap.toMatrix'_mul, ← LinearEquiv.coe_toLinearMap_mul, inv_mul_cancel,
        ← LinearMap.toMatrix'_id]
      rfl
    have hgen : ∀ h ∈ posUnipGens r K,
        InH (LinearMap.toMatrix' (h : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K))) :=
      fun h hh => ⟨h, Subgroup.subset_closure hh, rfl⟩
    have hSL : ∀ B ∈ Subgroup.closure {g : SpecialLinearGroup (Fin r) K |
        ∃ i j a, i < j ∧ LinearCover.rootElt i j a = g},
        InH (blockDiagInv (B : Matrix (Fin r) (Fin r) K)) := by
      intro B hcl
      induction hcl using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨i, j, a, hij, rfl⟩ := hx
        rw [LinearCover.coe_rootElt_of_ne hij.ne, blockDiagInv_transvection hij.ne]
        exact hgen _ (Or.inl ⟨i, j, a, hij, rfl⟩)
      | one =>
        change InH (blockDiagInv (1 : Matrix (Fin r) (Fin r) K))
        rw [blockDiagInv_one]
        exact hone
      | mul x y _ _ hx hy =>
        change InH (blockDiagInv ((x : Matrix (Fin r) (Fin r) K) * (y : Matrix (Fin r) (Fin r) K)))
        rw [blockDiagInv_mul]
        exact hmul _ _ hx hy
      | inv x _ hx =>
        have h1 : ((x⁻¹ : SpecialLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K) *
            (x : Matrix (Fin r) (Fin r) K) = 1 :=
          congrArg (fun y : SpecialLinearGroup (Fin r) K => (y : Matrix (Fin r) (Fin r) K))
            (inv_mul_cancel x)
        have hxinv : blockDiagInv ((x⁻¹ : SpecialLinearGroup (Fin r) K) :
            Matrix (Fin r) (Fin r) K) = (blockDiagInv (x : Matrix (Fin r) (Fin r) K))⁻¹ := by
          refine (Matrix.inv_eq_left_inv ?_).symm
          rw [← blockDiagInv_mul, h1, blockDiagInv_one]
        rw [hxinv]
        exact hinv _ hx
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
    obtain ⟨A, C, hA, h1, hC, hd, hgM⟩ := mem_posUnip_iff.1 hg
    have hdet : (A : Matrix (Fin r) (Fin r) K).det = 1 := by
      rw [det_of_isUpperTriangular hA]
      exact Finset.prod_eq_one fun i _ => h1 i
    let B : SpecialLinearGroup (Fin r) K := ⟨A, hdet⟩
    have hB : B ∈ LinearFlag.unitriangular r K := ⟨fun i j hji => hA hji, h1⟩
    obtain ⟨h, hH, hh⟩ :=
      hmul _ _ (hSL B (LinearCover.unitriangular_le_closure_rootElt hB)) (hunip C hC hd)
    rw [show ((B : SpecialLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K) = A from rfl,
      ← fromBlocks_eq_blockDiagInv_mul, ← hgM] at hh
    rw [← LinearEquiv.toLinearMap_injective (LinearMap.toMatrix'.injective hh)]
    exact hH
  · rw [Subgroup.closure_le]
    rintro g (⟨i, j, t, hij, rfl⟩ | ⟨i, j, t, hij, rfl⟩)
    · refine mem_posUnip_iff.2 ⟨elemGL hij.ne t, 0, fun a b hba => ?_, fun a => ?_, by simp,
        by simp, toMatrix'_eichler_inl_inr_eq hij.ne t⟩
      · have hba' : b < a := hba
        have hne : ¬(i = a ∧ j = b) := fun ⟨h1, h2⟩ => by
          subst h1
          subst h2
          exact absurd (hij.trans hba') (lt_irrefl _)
        simp [elemGL, Matrix.one_apply_ne (ne_of_gt hba'), hne]
      · simp only [elemGL, Units.val_mk, Matrix.add_apply, Matrix.smul_apply,
          Matrix.single_apply, Matrix.one_apply_eq, smul_eq_mul]
        rw [ite_eq_right fun h => hij.ne (h.1.trans h.2.symm), mul_zero, add_zero]
    · refine mem_posUnip_iff.2 ⟨1, t • (Matrix.single i j 1 - Matrix.single j i 1),
        fun a b hba => ?_, fun a => by simp, ?_, fun k => ?_, ?_⟩
      · have hba' : b < a := hba
        simp [Matrix.one_apply_ne (ne_of_gt hba')]
      · rw [transpose_smul, transpose_sub, transpose_single, transpose_single, ← neg_sub,
          smul_neg]
      · by_cases h1 : i = k <;> by_cases h2 : j = k <;> simp [h1, h2]
      · rw [toMatrix'_eichler_inl_inl hij.ne]
        simp

theorem posUnip_le_orthElementaryGroup : posUnip r K ≤ orthElementaryGroup (quadPlus r K) := by
  rw [posUnip_eq_closure, Subgroup.closure_le]
  rintro g (⟨i, j, t, -, rfl⟩ | ⟨i, j, t, -, rfl⟩) <;> exact eichler_mem_elementaryGroup _ _ _

variable (r K) in
abbrev AltMat := {C : Matrix (Fin r) (Fin r) K // Cᵀ = -C ∧ ∀ i, C i i = 0}

variable (r K) in
@[expose] def altEquiv : AltMat r K ≃ ({ij : Fin r × Fin r // ij.1 < ij.2} → K) where
  toFun C ij := (C : Matrix (Fin r) (Fin r) K) ij.1.1 ij.1.2
  invFun f := ⟨Matrix.of fun i j => if h : i < j then f ⟨(i, j), h⟩ else
      if h' : j < i then -f ⟨(j, i), h'⟩ else 0, by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.of_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, h.not_gt]
    · simp
    · simp [h, h.not_gt], fun i => by simp⟩
  left_inv C := by
    obtain ⟨C, hC, hd⟩ := C
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    have hji : C j i = -C i j := by
      have := congrFun (congrFun hC i) j
      simpa using this
    change (if h : i < j then C i j else if h' : j < i then -C j i else 0) = C i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h]
    · simp [hd]
    · simp [h, h.not_gt, hji]
  right_inv f := by
    funext ij
    change (if h : ij.1.1 < ij.1.2 then f ⟨(ij.1.1, ij.1.2), h⟩ else _) = f ij
    rw [dite_eq_left ij.2]

theorem card_altMat [Finite K] : Nat.card (AltMat r K) = Nat.card K ^ (r * (r - 1) / 2) := by
  rw [Nat.card_congr (altEquiv r K), Nat.card_fun, Nat.card_eq_fintype_card
    (α := {ij : Fin r × Fin r // ij.1 < ij.2}), Fintype.card_subtype,
    Fintype.card_product_filter_lt, Fintype.card_fin, Nat.choose_two_right]

theorem exists_posUnip_toMatrix' (A : GL (Fin r) K) (C : Matrix (Fin r) (Fin r) K)
    (hA : (A : Matrix (Fin r) (Fin r) K).IsUpperTriangular)
    (h1 : ∀ i, (A : Matrix (Fin r) (Fin r) K) i i = 1) (hC : Cᵀ = -C) (hd : ∀ i, C i i = 0) :
    ∃ g ∈ posUnip r K,
      LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
        fromBlocks (A : Matrix (Fin r) (Fin r) K) ((A : Matrix (Fin r) (Fin r) K) * C) 0
          ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ := by
  obtain ⟨g, -, hg⟩ :=
    (orthogonal_geometry_split_maximal_stabilizer_matrices (r := r) (K := K)).2.1 A C hC hd
  exact ⟨g, mem_posUnip_iff.2 ⟨A, C, hA, h1, hC, hd, hg⟩, hg⟩

theorem card_posUnip [Finite K] : Nat.card (posUnip r K) = Nat.card K ^ (r * (r - 1)) := by
  have hex : ∀ p : LinearFlag.unitriangular r K × AltMat r K, ∃ g ∈ posUnip r K,
      LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
        fromBlocks (SpecialLinearGroup.toGL p.1.1 : Matrix (Fin r) (Fin r) K)
          ((SpecialLinearGroup.toGL p.1.1 : Matrix (Fin r) (Fin r) K) * p.2.1) 0
          (((SpecialLinearGroup.toGL p.1.1)⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ :=
    fun p => exists_posUnip_toMatrix' _ p.2.1 (fun _ _ h => p.1.2.1 _ _ h) p.1.2.2 p.2.2.1
      p.2.2.2
  let Φ : LinearFlag.unitriangular r K × AltMat r K → posUnip r K := fun p =>
    ⟨(hex p).choose, (hex p).choose_spec.1⟩
  have hΦ : ∀ p, LinearMap.toMatrix' (((Φ p : posUnip r K) :
      (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
        (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
      fromBlocks (SpecialLinearGroup.toGL p.1.1 : Matrix (Fin r) (Fin r) K)
        ((SpecialLinearGroup.toGL p.1.1 : Matrix (Fin r) (Fin r) K) * p.2.1) 0
        (((SpecialLinearGroup.toGL p.1.1)⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ :=
    fun p => (hex p).choose_spec.2
  have hinj : Function.Injective Φ := by
    intro p p' h
    have h' := congrArg (fun g : posUnip r K => LinearMap.toMatrix'
      ((g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
        (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K))) h
    simp only [hΦ] at h'
    obtain ⟨hA, hC⟩ := fromBlocks_params_unique h'
    exact Prod.ext (Subtype.ext (SpecialLinearGroup.toGL_injective hA)) (Subtype.ext hC)
  have hsurj : Function.Surjective Φ := by
    rintro ⟨g, hg⟩
    obtain ⟨A, C, hA, h1, hC, hd, hgM⟩ := mem_posUnip_iff.1 hg
    have hdet : (A : Matrix (Fin r) (Fin r) K).det = 1 := by
      rw [det_of_isUpperTriangular hA]
      exact Finset.prod_eq_one fun i _ => h1 i
    let B : SpecialLinearGroup (Fin r) K := ⟨A, hdet⟩
    have hB : B ∈ LinearFlag.unitriangular r K := ⟨fun i j hji => hA hji, h1⟩
    have hBA : SpecialLinearGroup.toGL B = A := Units.ext rfl
    refine ⟨(⟨B, hB⟩, ⟨C, hC, hd⟩), Subtype.ext (LinearEquiv.toLinearMap_injective
      (LinearMap.toMatrix'.injective ?_))⟩
    rw [hΦ, hgM]
    simp only [hBA]
  rw [← Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩), Nat.card_prod,
    LinearFlag.card_unitriangular, card_altMat, ← pow_add]
  congr 1
  obtain ⟨m, hm⟩ := Nat.even_mul_pred_self r
  generalize r * (r - 1) = N at hm ⊢
  omega

theorem index_posUnip [Finite K] :
    ((posUnip r K).subgroupOf (posBorel r K)).index = (Nat.card K - 1) ^ r := by
  rw [← posBorelDiag_ker, Subgroup.index_ker, MonoidHom.range_eq_top.2 posBorelDiag_surjective,
    Subgroup.card_top, Nat.card_fun, Nat.card_fin]
  have := Nat.card_eq_card_units_add_one K
  congr 1
  omega

theorem orthogonal_geometry_split_positive_unipotent_matrices :
    (∀ g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K),
      g ∈ posBorel r K ↔ ∃ (A : GL (Fin r) K) (C : Matrix (Fin r) (Fin r) K),
        (A : Matrix (Fin r) (Fin r) K).IsUpperTriangular ∧ Cᵀ = -C ∧ (∀ i, C i i = 0) ∧
        LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
          fromBlocks (A : Matrix (Fin r) (Fin r) K) ((A : Matrix (Fin r) (Fin r) K) * C) 0
            ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ) ∧
    (∀ g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K),
      g ∈ posUnip r K ↔ ∃ (A : GL (Fin r) K) (C : Matrix (Fin r) (Fin r) K),
        (A : Matrix (Fin r) (Fin r) K).IsUpperTriangular ∧
        (∀ i, (A : Matrix (Fin r) (Fin r) K) i i = 1) ∧ Cᵀ = -C ∧ (∀ i, C i i = 0) ∧
        LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
          fromBlocks (A : Matrix (Fin r) (Fin r) K) ((A : Matrix (Fin r) (Fin r) K) * C) 0
            ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ) ∧
    posBorel r K ≤ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) ∧
    posUnip r K ≤ orthElementaryGroup (quadPlus r K) ∧ posUnip r K ≤ posBorel r K ∧
    ((posUnip r K).subgroupOf (posBorel r K)).Normal ∧
    (∀ (g : posBorel r K) (i : Fin r), ((posBorelDiag r K g i : Kˣ) : K) =
      LinearMap.toMatrix' ((g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
        (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) (Sum.inl i) (Sum.inl i)) ∧
    Function.Surjective (posBorelDiag r K) ∧
    (posBorelDiag r K).ker = (posUnip r K).subgroupOf (posBorel r K) ∧
    posUnip r K = Subgroup.closure (posUnipGens r K) ∧
    ∀ (p : ℕ), CharP K p → Finite K →
      Nat.card (posUnip r K) = Nat.card K ^ (r * (r - 1)) ∧ IsPGroup p (posUnip r K) ∧
      ((posUnip r K).subgroupOf (posBorel r K)).index = (Nat.card K - 1) ^ r := by
  refine ⟨fun g => mem_posBorel_iff, fun g => mem_posUnip_iff, posBorel_le_orthogonalGroup,
    posUnip_le_orthElementaryGroup, posUnip_le_posBorel, posUnip_normal, coe_posBorelDiag,
    posBorelDiag_surjective, posBorelDiag_ker, posUnip_eq_closure, fun p _ _ => ?_⟩
  refine ⟨card_posUnip, ?_, index_posUnip⟩
  let _ := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K p
  refine IsPGroup.of_card (n := n * (r * (r - 1))) ?_
  rw [card_posUnip, Nat.card_eq_fintype_card, hn, ← pow_mul]

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
