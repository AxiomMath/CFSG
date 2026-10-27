module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidLinCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviNoInv

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section OddAut

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem exists_conjAut_fieldAut_of_pow_odd (hn : 3 ≤ n) {α : MulAut (projectiveSL n K)} {r : ℕ}
    (hr : Odd r) (hα : α ^ r = 1) :
    ∃ (B : GL (Fin n) K) (σ : K ≃+* K), α = conjAut n K B * fieldAut n K σ := by
  have : Finite (MulAut (projectiveSL n K)) :=
    Finite.of_injective (fun α : MulAut (projectiveSL n K) => (α : projectiveSL n K → _))
      fun _ _ h => MulEquiv.ext (congrFun h)
  obtain ⟨-, -, -, -, -, -, -, hidx, -, -⟩ := standard_outer_quotients (K := K) (n := n)
  rw [(automorphism_generation (K := K) hn).1] at hidx
  have hidx' : (semilinearAutGroup n K).index ≤ 2 := by
    rw [← Subgroup.relIndex_top_right]
    exact hidx
  have hne : (semilinearAutGroup n K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmem : α ∈ semilinearAutGroup n K := by
    rcases (show (semilinearAutGroup n K).index = 1 ∨ (semilinearAutGroup n K).index = 2 by
      omega) with h1 | h2
    · rw [Subgroup.index_eq_one.1 h1]
      exact Subgroup.mem_top α
    · have hsq := Subgroup.sq_mem_of_index_two h2 α
      obtain ⟨j, rfl⟩ := hr
      have hxk : α = ((α ^ 2) ^ j)⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← pow_mul, ← pow_succ']
        exact hα
      rw [hxk]
      exact inv_mem (pow_mem hsq j)
  exact mem_semilinearAutGroup_iff.mp hmem

end OddAut

section Four

variable {K : Type} [Field K] [CharP K 2]

theorem eq_one_of_mem_scalars_four {s : SpecialLinearGroup (Fin (2 + 2)) K}
    (hs : s ∈ scalars (2 + 2) K) : s = 1 := by
  obtain ⟨c, hc4, hc⟩ := mem_scalars.mp hs
  have h1 : (c : K) = 1 := by
    have h := congrArg Units.val hc4
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h
    have h2 : ((c : K) - 1) ^ 2 ^ 2 = 0 := by
      rw [sub_pow_char_pow, one_pow, show (2 : ℕ) ^ 2 = 2 + 2 by norm_num, h, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h2)
  apply Subtype.ext
  rw [hc, h1, map_one]
  rfl

theorem eq_of_proj_eq_four {g h : SpecialLinearGroup (Fin (2 + 2)) K}
    (he : proj (2 + 2) K g = proj (2 + 2) K h) : g = h := by
  rw [proj_eq_proj_iff] at he
  exact inv_mul_eq_one.mp (eq_one_of_mem_scalars_four he)

end Four

section TraceTwo

variable {K : Type} [Field K] {k : ℕ}

theorem trace_eq_trace_stdRhoMat [CharP K 2] (hk : 2 ≤ k) {g : SpecialLinearGroup (Fin (2 + k)) K}
    (hg : g ∈ stdX K hk) :
    (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K).trace =
      (stdRhoMat hk (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K)).trace := by
  simp only [Matrix.trace, Matrix.diag, stdRhoMat, submatrix_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun x => x ≠ idxU hk ∧ x ≠ idxV hk)]
  have huv : (⟨idxU hk, fun h => h.1 rfl⟩ : StdEnds hk) ≠ ⟨idxV hk, fun h => h.2 rfl⟩ := by
    intro h
    exact idxU_ne_idxV hk (congrArg Subtype.val h)
  have hz : ∑ x : StdEnds hk, (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) x.1 x.1 = 0 := by
    rw [Fintype.sum_eq_add _ _ huv fun x hx => absurd hx (by
      rcases not_and_or.mp x.2 with h | h <;> push Not at h
      · exact fun h' => h'.1 (Subtype.ext h)
      · exact fun h' => h'.2 (Subtype.ext h))]
    change (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxU hk) (idxU hk) +
      (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxV hk) (idxV hk) = 0
    rw [stdX_apply_u hk hg, stdX_apply_v hk hg, Pi.single_eq_same, Pi.single_eq_same,
      CharTwo.add_self_eq_zero]
  rw [hz, add_zero]

@[expose] noncomputable def midEquivTwo : Fin 2 ≃ StdMid (le_rfl : 2 ≤ 2) :=
  Equiv.ofBijective (fun i => ⟨finSumFinEquiv (Sum.inl i),
      finSumFinEquiv.injective.ne Sum.inl_ne_inr, finSumFinEquiv.injective.ne Sum.inl_ne_inr⟩)
    ⟨fun i j h => Sum.inl_injective (finSumFinEquiv.injective (congrArg Subtype.val h)), by
      intro a
      obtain ⟨z, hz⟩ := finSumFinEquiv.surjective a.1
      rcases z with i | j
      · exact ⟨i, Subtype.ext hz⟩
      · exfalso
        fin_cases j
        · exact a.2.1 hz.symm
        · exact a.2.2 hz.symm⟩

theorem coe_midEquivTwo (i : Fin 2) :
    ((midEquivTwo i : StdMid (le_rfl : 2 ≤ 2)) : Fin (2 + 2)) = finSumFinEquiv (Sum.inl i) :=
  rfl

theorem stdRhoMat_blkSL₁_midEquivTwo (N : SpecialLinearGroup (StdMid (le_rfl : 2 ≤ 2)) K) :
    stdRhoMat (le_rfl : 2 ≤ 2) ((blkSL₁ ((slIndexEquiv K midEquivTwo).symm N) :
      SpecialLinearGroup (Fin (2 + 2)) K) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) =
      (N : Matrix (StdMid (le_rfl : 2 ≤ 2)) (StdMid (le_rfl : 2 ≤ 2)) K) := by
  ext a b
  obtain ⟨i, rfl⟩ := midEquivTwo.surjective a
  obtain ⟨j, rfl⟩ := midEquivTwo.surjective b
  rw [stdRhoMat, submatrix_apply, coe_blkSL₁, coe_midEquivTwo, coe_midEquivTwo, blk,
    coe_reindexAlgEquiv, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, fromBlocks_apply₁₁]
  change ((reindexAlgEquiv K K midEquivTwo).symm (N : Matrix (StdMid (le_rfl : 2 ≤ 2))
    (StdMid (le_rfl : 2 ≤ 2)) K)) i j = _
  rw [symm_reindexAlgEquiv, coe_reindexAlgEquiv, reindex_apply, submatrix_apply, Equiv.symm_symm]

end TraceTwo

section CommuteStd

variable {K : Type} [Field K] {k : ℕ}

theorem mulVec_u_of_commute_stdT (hk : 2 ≤ k) {M : Matrix (Fin (2 + k)) (Fin (2 + k)) K}
    (h : M * (1 + single (idxU hk) (idxV hk) 1) = (1 + single (idxU hk) (idxV hk) 1) * M) :
    M *ᵥ Pi.single (idxU hk) 1 = M (idxU hk) (idxU hk) • Pi.single (idxU hk) 1 := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
  have h' := add_left_cancel h
  ext x
  rw [mulVec_single_one, col_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  have hx := congrFun (congrFun h' x) (idxV hk)
  rw [mul_single_apply_same, mul_one] at hx
  split_ifs with hxu
  · subst hxu
    rw [mul_one]
  · rw [single_mul_apply_of_ne _ _ _ _ _ hxu] at hx
    rw [mul_zero]
    exact hx

theorem vecMul_v_of_commute_stdT (hk : 2 ≤ k) {M : Matrix (Fin (2 + k)) (Fin (2 + k)) K}
    (h : M * (1 + single (idxU hk) (idxV hk) 1) = (1 + single (idxU hk) (idxV hk) 1) * M) :
    Pi.single (idxV hk) 1 ᵥ* M = M (idxU hk) (idxU hk) • Pi.single (idxV hk) 1 := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
  have h' := add_left_cancel h
  ext y
  rw [single_one_vecMul, row_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  have hy := congrFun (congrFun h' (idxU hk)) y
  rw [single_mul_apply_same, one_mul] at hy
  split_ifs with hyv
  · subst hyv
    rw [mul_single_apply_same, mul_one] at hy
    rw [mul_one, hy]
  · rw [mul_single_apply_of_ne _ _ _ _ _ hyv] at hy
    rw [mul_zero, ← hy]

end CommuteStd

section FieldTrivial

variable {K : Type} [Field K] [CharP K 2]

theorem fieldAut_eq_one_of_fix_traces (B : GL (Fin (2 + 2)) K) (σ : K ≃+* K)
    {S : Set (SpecialLinearGroup (Fin (2 + 2)) K)} (hS : ∀ g ∈ S, g ∈ stdX K (le_rfl : 2 ≤ 2))
    (hfix : ∀ g ∈ S, (conjAut (2 + 2) K B * fieldAut (2 + 2) K σ) (proj (2 + 2) K g) =
      proj (2 + 2) K g)
    (htr : ∀ t : K, ∃ g ∈ S,
      (stdRhoMat (le_rfl : 2 ≤ 2) (g : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K)).trace = t) :
    σ = 1 := by
  apply RingEquiv.ext
  intro t
  obtain ⟨g, hg, hgt⟩ := htr t
  have h1 := hfix g hg
  rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj] at h1
  have h2 := congrArg (fun M : SpecialLinearGroup (Fin (2 + 2)) K =>
    (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K).trace) (eq_of_proj_eq_four h1)
  rw [coe_slConjugation, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace,
    trace_eq_trace_stdRhoMat (le_rfl : 2 ≤ 2) (hS g hg), hgt] at h2
  exact h2

end FieldTrivial

section Unipotent

variable {K : Type} [Field K] {k : ℕ}

theorem sub_one_sq_apply_of_fixesStdEnds (hk : 2 ≤ k) {M : Matrix (Fin (2 + k)) (Fin (2 + k)) K}
    (hM : FixesStdEnds hk M) (hρ : stdRhoMat hk M = 1) {x y : Fin (2 + k)}
    (hxy : ¬ (x = idxU hk ∧ y = idxV hk)) : ((M - 1) * (M - 1)) x y = 0 := by
  have hcol : ∀ z, (M - 1) z (idxU hk) = 0 := by
    intro z
    rw [Matrix.sub_apply, hM.apply_u]
    by_cases hz : z = idxU hk
    · rw [hz, Pi.single_eq_same, one_apply_eq, sub_self]
    · rw [Pi.single_eq_of_ne hz, one_apply_ne hz, sub_zero]
  have hrow : ∀ z, (M - 1) (idxV hk) z = 0 := by
    intro z
    rw [Matrix.sub_apply, hM.apply_v]
    by_cases hz : z = idxV hk
    · rw [hz, Pi.single_eq_same, one_apply_eq, sub_self]
    · rw [Pi.single_eq_of_ne hz, one_apply_ne (Ne.symm hz), sub_zero]
  have hmid : ∀ a b : StdMid hk, (M - 1) a.1 b.1 = 0 := by
    intro a b
    have := congrFun (congrFun hρ a) b
    rw [stdRhoMat, submatrix_apply, one_apply] at this
    rw [Matrix.sub_apply, this, one_apply]
    split_ifs with h1 h2 h2
    · exact sub_self _
    · exact absurd (congrArg Subtype.val h1) h2
    · exact absurd (Subtype.ext h2) h1
    · exact sub_self _
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun z _ => ?_
  by_cases hzu : z = idxU hk
  · rw [hzu, hcol, zero_mul]
  by_cases hzv : z = idxV hk
  · rw [hzv, hrow, mul_zero]
  by_cases hx : x = idxU hk
  · have hy : y ≠ idxV hk := fun hy => hxy ⟨hx, hy⟩
    by_cases hyu : y = idxU hk
    · rw [hyu, hcol, mul_zero]
    · rw [hmid ⟨z, hzu, hzv⟩ ⟨y, hyu, hy⟩, mul_zero]
  · by_cases hxv : x = idxV hk
    · rw [hxv, hrow, zero_mul]
    · rw [hmid ⟨x, hx, hxv⟩ ⟨z, hzu, hzv⟩, zero_mul]

theorem pow_four_eq_one_of_fixesStdEnds [CharP K 2] (hk : 2 ≤ k)
    {M : Matrix (Fin (2 + k)) (Fin (2 + k)) K} (hM : FixesStdEnds hk M)
    (hρ : stdRhoMat hk M = 1) : M ^ 4 = 1 := by
  set N := M - 1 with hN
  have hM' : M = 1 + N := by rw [hN, add_sub_cancel]
  have hNN : N * N * (N * N) = 0 := by
    ext x y
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases h1 : x = idxU hk ∧ z = idxV hk
    · have hz : ¬ (z = idxU hk ∧ y = idxV hk) := fun h => idxU_ne_idxV hk (h.1.symm.trans h1.2)
      rw [sub_one_sq_apply_of_fixesStdEnds hk hM hρ hz, mul_zero]
    · rw [sub_one_sq_apply_of_fixesStdEnds hk hM hρ h1, zero_mul]
  have hadd : ∀ P : Matrix (Fin (2 + k)) (Fin (2 + k)) K, P + P = 0 := by
    intro P
    ext x y
    rw [Matrix.add_apply, CharTwo.add_self_eq_zero, Matrix.zero_apply]
  have hsq : (1 + N) * (1 + N) = 1 + N * N := by
    rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, add_assoc, ← add_assoc N N,
      hadd N, zero_add]
  have hsq' : (1 + N * N) * (1 + N * N) = 1 := by
    rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, hNN, add_zero, add_assoc,
      hadd, add_zero]
  rw [hM', show ((1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) + N) ^ 4 =
    ((1 + N) * (1 + N)) * ((1 + N) * (1 + N)) by noncomm_ring, hsq, hsq']

end Unipotent

section RhoScalar

variable {K : Type} [Field K] {k : ℕ}

theorem exists_rho_scalar_of_commute (hk : 2 ≤ k) {B : Matrix (Fin (2 + k)) (Fin (2 + k)) K}
    (hT : B * (1 + single (idxU hk) (idxV hk) 1) = (1 + single (idxU hk) (idxV hk) 1) * B)
    {S : Set (SpecialLinearGroup (Fin (2 + k)) K)} (hS : ∀ g ∈ S, g ∈ stdX K hk)
    (hBS : ∀ g ∈ S, B * (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) * B)
    (hcov : ∀ N : SpecialLinearGroup (StdMid hk) K, ∃ g ∈ S,
      stdRhoMat hk (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
        (N : Matrix (StdMid hk) (StdMid hk) K)) :
    ∃ b : K, stdRhoMat hk B = scalar (StdMid hk) b := by
  have hu := mulVec_u_of_commute_stdT hk hT
  have hv := vecMul_v_of_commute_stdT hk hT
  have hcol : ∀ a : StdMid hk, B a.1 (idxU hk) = 0 := fun a => by
    have := congrFun hu a.1
    rwa [mulVec_single_one, col_apply, Pi.smul_apply, Pi.single_eq_of_ne a.2.1, smul_zero] at this
  have hrow : ∀ b : StdMid hk, B (idxV hk) b.1 = 0 := fun b => by
    have := congrFun hv b.1
    rwa [single_one_vecMul, row_apply, Pi.smul_apply, Pi.single_eq_of_ne b.2.2, smul_zero] at this
  have hcomm : ∀ N : SpecialLinearGroup (StdMid hk) K, stdRhoMat hk B *
      (N : Matrix (StdMid hk) (StdMid hk) K) = (N : Matrix (StdMid hk) (StdMid hk) K) *
        stdRhoMat hk B := by
    intro N
    obtain ⟨g, hg, hgN⟩ := hcov N
    have hgcol : ∀ a : StdMid hk, (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) a.1 (idxU hk) = 0 :=
      fun a => by rw [stdX_apply_u hk (hS g hg), Pi.single_eq_of_ne a.2.1]
    have hgrow : ∀ b : StdMid hk, (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxV hk) b.1 = 0 :=
      fun b => by rw [stdX_apply_v hk (hS g hg), Pi.single_eq_of_ne b.2.2]
    rw [← hgN, ← stdRhoMat_mul' hk hcol hgrow, ← stdRhoMat_mul' hk hgcol hrow, hBS g hg]
  obtain ⟨b, hb⟩ := mem_range_scalar_of_commute_transvectionStruct fun t =>
    (hcomm t.toSpecialLinearGroup).symm
  exact ⟨b, hb.symm⟩

end RhoScalar

section Normalizer

variable {G : Type} [Group G] {A : Subgroup G}

@[expose] def linNormConj {t : G} (ht : t ∈ normalizer (A : Set G)) : MulAut ↥A where
  toFun a := ⟨t * a * t⁻¹, (mem_normalizer_iff.mp ht a).mp a.2⟩
  invFun a := ⟨t⁻¹ * a * t, by
    have h := (mem_normalizer_iff.mp (inv_mem ht) a).mp a.2
    rwa [inv_inv] at h⟩
  left_inv a := Subtype.ext (by simp [mul_assoc])
  right_inv a := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by
    change t * (a * b : G) * t⁻¹ = t * a * t⁻¹ * (t * b * t⁻¹)
    group)

theorem coe_linNormConj {t : G} (ht : t ∈ normalizer (A : Set G)) (a : ↥A) :
    ((linNormConj ht a : ↥A) : G) = t * a * t⁻¹ :=
  rfl

theorem linNormConj_pow_eq_one {t : G} (ht : t ∈ normalizer (A : Set G)) {N : ℕ}
    (htN : t ^ N = 1) : linNormConj ht ^ N = 1 := by
  have h : ∀ j : ℕ, ∀ a : ↥A, (((linNormConj ht ^ j) a : ↥A) : G) = t ^ j * a * (t ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro a; simp
    | succ j ih =>
      intro a
      rw [pow_succ, MulAut.mul_apply, ih, coe_linNormConj, pow_succ]
      group
  ext a
  rw [h N a, htN, MulAut.one_apply]
  simp

theorem exists_inducedAut_of_mem_normalizer {P : Type*} [Group P] {θ : ↥A →* P}
    (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ) {t : G}
    (ht : t ∈ normalizer (A : Set G)) :
    ∃ α : MulAut P, (∀ a, α (θ a) = θ (linNormConj ht a)) ∧
      ∀ N : ℕ, t ^ N = 1 → α ^ N = 1 := by
  obtain ⟨α, hα⟩ := exists_inducedAut hker hθ (linNormConj ht)
  refine ⟨α, hα, fun N hN => ?_⟩
  have h : ∀ j : ℕ, ∀ a, (α ^ j) (θ a) = θ ((linNormConj ht ^ j) a) := by
    intro j
    induction j with
    | zero => intro a; rfl
    | succ j ih =>
      intro a
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hα, ih]
  ext x
  obtain ⟨a, rfl⟩ := hθ x
  rw [h N a, linNormConj_pow_eq_one ht hN, MulAut.one_apply, MulAut.one_apply]

end Normalizer

section FixTwo

variable {K : Type} [Field K]

theorem trace_reindexAlgEquiv {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (X : Matrix ι ι K) : (reindexAlgEquiv K K e X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, coe_reindexAlgEquiv, reindex_apply, submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => X i i)

theorem exists_trace_eq_two [CharP K 2] (t : K) :
    ∃ N : SpecialLinearGroup (StdMid (le_rfl : 2 ≤ 2)) K,
      (N : Matrix (StdMid (le_rfl : 2 ≤ 2)) (StdMid (le_rfl : 2 ≤ 2)) K).trace = t := by
  let X : SpecialLinearGroup (Fin 2) K := ⟨!![t, 1; 1, 0], by
    rw [det_fin_two_of]; simp [CharTwo.neg_eq]⟩
  refine ⟨slIndexEquiv K midEquivTwo X, ?_⟩
  rw [coe_slIndexEquiv, trace_reindexAlgEquiv]
  change (!![t, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K).trace = t
  rw [trace_fin_two_of]
  simp

theorem exists_conjAut_of_fix_two [Finite K] [CharP K 2] {α : MulAut (projectiveSL (2 + 2) K)}
    {r : ℕ} (hr : Odd r) (hαr : α ^ r = 1) {S : Set (SpecialLinearGroup (Fin (2 + 2)) K)}
    (hS : ∀ g ∈ S, g ∈ stdX K (le_rfl : 2 ≤ 2))
    (hcov : ∀ N : SpecialLinearGroup (StdMid (le_rfl : 2 ≤ 2)) K, ∃ g ∈ S,
      stdRhoMat (le_rfl : 2 ≤ 2) (g : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) =
        (N : Matrix (StdMid (le_rfl : 2 ≤ 2)) (StdMid (le_rfl : 2 ≤ 2)) K))
    (hfix : ∀ g ∈ S, α (proj (2 + 2) K g) = proj (2 + 2) K g)
    (hfixT : α (proj (2 + 2) K (trSL (idxU (le_rfl : 2 ≤ 2)) (idxV (le_rfl : 2 ≤ 2))
      (idxU_ne_idxV _) 1)) = proj (2 + 2) K (trSL (idxU (le_rfl : 2 ≤ 2))
        (idxV (le_rfl : 2 ≤ 2)) (idxU_ne_idxV _) 1)) :
    ∃ B : GL (Fin (2 + 2)) K, α = conjAut (2 + 2) K B ∧
      (B : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) *
        (1 + single (idxU (le_rfl : 2 ≤ 2)) (idxV (le_rfl : 2 ≤ 2)) (1 : K)) =
        (1 + single (idxU (le_rfl : 2 ≤ 2)) (idxV (le_rfl : 2 ≤ 2)) (1 : K)) * B ∧
      (∀ g ∈ S, (B : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) * g = g * B) ∧
      ∃ b : K, stdRhoMat (le_rfl : 2 ≤ 2) (B : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) =
        scalar (StdMid (le_rfl : 2 ≤ 2)) b := by
  obtain ⟨B, σ, rfl⟩ := exists_conjAut_fieldAut_of_pow_odd (by norm_num) hr hαr
  have hσ : σ = 1 := fieldAut_eq_one_of_fix_traces B σ hS hfix fun t => by
    obtain ⟨N, hN⟩ := exists_trace_eq_two t
    obtain ⟨g, hg, hgN⟩ := hcov N
    exact ⟨g, hg, by rw [hgN, hN]⟩
  rw [hσ, map_one, mul_one] at hfix hfixT
  have ht2 : (trSL (idxU (le_rfl : 2 ≤ 2)) (idxV (le_rfl : 2 ≤ 2)) (idxU_ne_idxV _) (1 : K)) ^ 2
      = 1 := by
    rw [sq, trSL_mul_self_charTwo]
  have hT := mul_eq_mul_of_proj_eq B ht2 ht2 (by rw [← conjAut_proj]; exact hfixT)
  rw [coe_trSL] at hT
  have hBS : ∀ g ∈ S, (B : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) * g = g * B := by
    intro g hg
    have h0 : proj (2 + 2) K (CatalogueBHigherLinearAction.slConjugation (2 + 2) K B g) =
        proj (2 + 2) K g := by
      rw [← conjAut_proj]
      exact hfix g hg
    have h1 := eq_of_proj_eq_four h0
    have h2 := congrArg Subtype.val h1
    rw [CatalogueBHigherLinearAction.slConjugation_matrix] at h2
    calc (B : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) * g =
        (B : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) * g *
          ((B⁻¹ : GL (Fin (2 + 2)) K) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) * B := by
          rw [Matrix.mul_assoc _
              ((B⁻¹ : GL (Fin (2 + 2)) K) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K),
            Units.inv_mul, Matrix.mul_one]
      _ = g * B := by rw [h2]
  exact ⟨B, by rw [hσ, map_one, mul_one], hT, hBS,
    exists_rho_scalar_of_commute (le_rfl : 2 ≤ 2) hT hS hBS hcov⟩

end FixTwo

section Witness

variable {K : Type} [Field K]

theorem isBlockOne_of_two {x : Fin (2 + 2)} (hxu : x ≠ idxU (le_rfl : 2 ≤ 2))
    (hxv : x ≠ idxV (le_rfl : 2 ≤ 2)) : IsBlockOne 2 x := by
  obtain ⟨z, rfl⟩ := finSumFinEquiv.surjective x
  rcases z with i | j
  · fin_cases i
    exacts [Or.inl rfl, Or.inr rfl]
  · fin_cases j
    · exact (hxu rfl).elim
    · exact (hxv rfl).elim

theorem blockOneShape_of_two (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) :
    BlockOneShape (le_rfl : 2 ≤ 2) M := fun _ _ hxu hxv hyu hyv hxy =>
  absurd ⟨isBlockOne_of_two hxu hxv, isBlockOne_of_two hyu hyv⟩ hxy

theorem eq_one_of_pow_four_of_pow_odd {M : Type*} [Monoid M] {x : M} {r : ℕ} (hr : Odd r)
    (h4 : x ^ 4 = 1) (hrx : x ^ r = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one h4
  have h2 : orderOf x ∣ r := orderOf_dvd_of_pow_eq_one hrx
  have hcop : Nat.Coprime (2 ^ 2) r := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hr)
  exact orderOf_eq_one_iff.mp ((hcop.coprime_dvd_left h1).eq_one_of_dvd h2)

theorem conjAut_pow_four_of_rho_eq [CharP K 2] {k : ℕ} (hk : 2 ≤ k) (B : GL (Fin (2 + k)) K)
    (hu : (B.1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ Pi.single (idxU hk) 1 =
      (B.1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxU hk) (idxU hk) • Pi.single (idxU hk) 1)
    (hv : Pi.single (idxV hk) 1 ᵥ* (B.1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      (B.1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxU hk) (idxU hk) • Pi.single (idxV hk) 1)
    (hρ : stdRhoMat hk (B.1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      scalar (StdMid hk) ((B.1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxU hk) (idxU hk))) :
    conjAut (2 + k) K B ^ 4 = 1 := by
  set a := (B.1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxU hk) (idxU hk) with ha_def
  have ha : a ≠ 0 := by
    intro h0
    have h1 : (B.1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ Pi.single (idxU hk) 1 = 0 := by
      rw [hu, h0, zero_smul]
    have h2 := congrArg (fun w => ((B⁻¹ : GL (Fin (2 + k)) K) :
      Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ w) h1
    simp only [mulVec_mulVec, Units.inv_mul, one_mulVec, mulVec_zero] at h2
    have h3 := congrFun h2 (idxU hk)
    simp at h3
  have hN : FixesStdEnds hk (a⁻¹ • (B.1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K)) := by
    refine ⟨?_, ?_⟩
    · rw [smul_mulVec, hu, smul_smul, inv_mul_cancel₀ ha, one_smul]
    · rw [vecMul_smul, hv, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hρN : stdRhoMat hk (a⁻¹ • (B.1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K)) = 1 := by
    have h : stdRhoMat hk (a⁻¹ • (B.1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K)) =
        a⁻¹ • stdRhoMat hk (B.1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) := rfl
    rw [h, hρ, scalar_apply, ← smul_one_eq_diagonal, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have h4 := pow_four_eq_one_of_fixesStdEnds hk hN hρN
  rw [smul_pow] at h4
  have h5 : (B.1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) ^ 4 = scalar (Fin (2 + k)) (a ^ 4) := by
    have h6 := congrArg (fun M => a ^ 4 • M) h4
    simp only [smul_smul, inv_pow, mul_inv_cancel₀ (pow_ne_zero 4 ha), one_smul] at h6
    rw [h6, scalar_apply, smul_one_eq_diagonal]
  rw [← map_pow]
  exact conjAut_eq_one_of_scalar (B ^ 4) (by rw [Units.val_pow_eq_pow_val, h5])

theorem coe_torus_eq_diagonal (c : Kˣ) :
    ((torus c : SpecialLinearGroup (Fin (2 + 2)) K) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) =
      diagonal (Sum.elim (fun _ => ((c⁻¹ : Kˣ) : K)) (fun _ => (c : K)) ∘ finSumFinEquiv.symm) := by
  rw [coe_torus, blk, smul_one_eq_diagonal, smul_one_eq_diagonal, fromBlocks_diagonal,
    coe_reindexAlgEquiv, reindex_apply, submatrix_diagonal_equiv]

theorem torus_mul_trSL_ne [CharP K 2] {c : Kˣ} (hc : c ≠ 1) :
    torus c * trSL (idxU (le_rfl : 2 ≤ 2)) (idxW 2) (idxW_ne_idxU _).symm (1 : K) ≠
      trSL (idxU (le_rfl : 2 ≤ 2)) (idxW 2) (idxW_ne_idxU _).symm 1 * torus c := by
  intro h
  have h1 := congrFun (congrFun (congrArg Subtype.val h) (idxU (le_rfl : 2 ≤ 2))) (idxW 2)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_torus_eq_diagonal, diagonal_mul, mul_diagonal, coe_trSL] at h1
  have he : (((1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) +
      single (idxU (le_rfl : 2 ≤ 2)) (idxW 2) (1 : K) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K))
        (idxU (le_rfl : 2 ≤ 2)) (idxW 2) = 1 := by
    rw [Matrix.add_apply, one_apply_ne (idxW_ne_idxU (le_rfl : 2 ≤ 2)).symm, single_apply_same,
      zero_add]
  rw [he, mul_one, one_mul] at h1
  simp only [Function.comp_apply, idxU, idxW, Equiv.symm_apply_apply, Sum.elim_inr,
    Sum.elim_inl] at h1
  have h2 : (c : K) * c = 1 * 1 := by
    calc (c : K) * c = ((c⁻¹ : Kˣ) : K) * c := by rw [h1]
      _ = 1 * 1 := by rw [Units.inv_mul, one_mul]
  exact hc (Units.ext (by rw [Units.val_one]; exact eq_of_mul_self_eq h2))

end Witness

section TorusLift

variable {G : Type} [Group G] {A : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Field K] [Finite K] [CharP K 2] in
theorem odd_card_sub_one_of_two_pow {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) :
    Odd (Nat.card K - 1) := by
  rw [hK]
  obtain ⟨j, hj⟩ : Even (2 ^ m) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  exact ⟨j - 1, by omega⟩

omit [CharP K 2] in
theorem pow_eq_one_of_theta_torus [Finite G] {θ : ↥A →* projectiveSL (2 + 2) K}
    (hker : θ.ker = center ↥A) {δ : G} (hδA : δ ∈ A) {c : Kˣ}
    (hθδ : θ ⟨δ, hδA⟩ = proj (2 + 2) K (torus c)) :
    δ ^ ((Nat.card K - 1) * Nat.card (center ↥A)) = 1 := by
  have := Fintype.ofFinite K
  have hc : c ^ (Nat.card K - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ c.ne_zero
  have h1 : (⟨δ, hδA⟩ : ↥A) ^ (Nat.card K - 1) ∈ center ↥A := by
    rw [← hker, MonoidHom.mem_ker, map_pow, hθδ, ← map_pow, ← map_pow, hc, map_one, map_one]
  have h2 : ((⟨δ, hδA⟩ : ↥A) ^ (Nat.card K - 1)) ^ Nat.card (center ↥A) = 1 := by
    have := pow_card_eq_one' (G := ↥(center ↥A)) (x := ⟨_, h1⟩)
    exact congrArg Subtype.val this
  rw [← pow_mul] at h2
  exact congrArg Subtype.val h2

omit [Finite K] [CharP K 2] in
theorem leviW_le_centralizer_of_barT {θ : ↥A →* projectiveSL (2 + 2) K}
    (hker : θ.ker = center ↥A) {δ : G} (hδA : δ ∈ A) (hδT : θ ⟨δ, hδA⟩ ∈ barT K) :
    leviW θ ≤ centralizer ({δ} : Set G) := by
  refine levLift_le_centralizer hker hδA fun s hs => ?_
  obtain ⟨c, hc⟩ := hδT
  obtain ⟨X, rfl⟩ := hs
  rw [← hc]
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blkSL₁]
  exact (blk_mul_torus _ _ c).symm

end TorusLift

section WitnessMatrix

variable {K : Type} [Field K] {k : ℕ}

theorem inducedAut_eq_of_commute {G : Type} [Group G] {A : Subgroup G} {P : Type*} [Group P]
    {θ : ↥A →* P} {t : G} (ht : t ∈ normalizer (A : Set G)) {α : MulAut P}
    (hα : ∀ a, α (θ a) = θ (linNormConj ht a)) {a : ↥A} (hta : t * a = a * t) :
    α (θ a) = θ a := by
  rw [hα]
  congr 1
  apply Subtype.ext
  rw [coe_linNormConj, hta, mul_inv_cancel_right]

theorem ne_zero_of_mulVec_eq_smul (hk : 2 ≤ k) {B : GL (Fin (2 + k)) K} {a : K}
    (hu : B.1 *ᵥ Pi.single (idxU hk) 1 = a • Pi.single (idxU hk) 1) : a ≠ 0 := by
  intro h0
  have h1 : B.1 *ᵥ Pi.single (idxU hk) 1 = 0 := by rw [hu, h0, zero_smul]
  have h2 := congrArg (fun w => ((B⁻¹ : GL (Fin (2 + k)) K) :
    Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ w) h1
  simp only [mulVec_mulVec, Units.inv_mul, one_mulVec, mulVec_zero] at h2
  have h3 := congrFun h2 (idxU hk)
  simp at h3

theorem fixesStdEnds_inv_smul (hk : 2 ≤ k) {B : Matrix (Fin (2 + k)) (Fin (2 + k)) K} {a : K}
    (ha : a ≠ 0) (hu : B *ᵥ Pi.single (idxU hk) 1 = a • Pi.single (idxU hk) 1)
    (hv : Pi.single (idxV hk) 1 ᵥ* B = a • Pi.single (idxV hk) 1) :
    FixesStdEnds hk (a⁻¹ • B) :=
  ⟨by rw [smul_mulVec, hu, smul_smul, inv_mul_cancel₀ ha, one_smul],
    by rw [vecMul_smul, hv, smul_smul, inv_mul_cancel₀ ha, one_smul]⟩

theorem torusOneShape_inv_smul_of_two {B : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K} (a b : K)
    (hb : stdRhoMat (le_rfl : 2 ≤ 2) B = scalar (StdMid (le_rfl : 2 ≤ 2)) b) :
    TorusOneShape (le_rfl : 2 ≤ 2) (a⁻¹ * b) (a⁻¹ • B) := by
  intro x y hxu hxv hyu hyv _
  have h := congrFun (congrFun hb ⟨x, hxu, hxv⟩) ⟨y, hyu, hyv⟩
  rw [stdRhoMat, submatrix_apply, scalar_apply, diagonal_apply] at h
  rw [Matrix.smul_apply, h, smul_eq_mul]
  by_cases hxy : x = y
  · subst hxy
    simp
  · rw [ite_eq_right (fun h' => hxy (congrArg Subtype.val h')), ite_eq_right hxy, mul_zero]

end WitnessMatrix

section StepOne

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_conj_lam_mem_range_two (h4 : 4 ≤ Nat.card K) (hq4 : ∃ s : Finset K, s.card = 4)
    {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) {θ : ↥A →* projectiveSL (2 + 2) K}
    (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A)))
    (hA : commutator ↥A = ⊤) {p : G} (hpA : p ∈ A) (hp2 : p ^ 2 = 1)
    (hθp : θ ⟨p, hpA⟩ = proj (2 + 2) K (trSL (idxU (le_rfl : 2 ≤ 2)) (idxV (le_rfl : 2 ≤ 2))
      (idxU_ne_idxV _) 1))
    {lam : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* SpecialLinearGroup (Fin (2 + 2)) K}
    {ψ : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →*
      SpecialLinearGroup (StdMid (le_rfl : 2 ≤ 2)) K}
    (hlamX : ∀ x, lam x ∈ stdX K (le_rfl : 2 ≤ 2))
    (hlam : ∀ x, proj (2 + 2) K (lam x) = θ (Subgroup.inclusion (perfectCore_inf_le A p) x))
    (hψ : ∀ x, (ψ x : Matrix (StdMid (le_rfl : 2 ≤ 2)) (StdMid (le_rfl : 2 ≤ 2)) K) =
      stdRhoMat (le_rfl : 2 ≤ 2) (lam x : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K))
    {c : G} {γ : MulAut ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))}
    (hγ : ∀ x, ((γ x : ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))) : G) = c⁻¹ * x * c)
    {β : MulAut (SpecialLinearGroup (StdMid (le_rfl : 2 ≤ 2)) K)} (hβ : ∀ x, β (ψ x) = ψ (γ x))
    (hTN : AschbacherTightEmbedding.rightConjugate (liftSub θ (barT K)) c ≤
      normalizer (A : Set G))
    (hTC : AschbacherTightEmbedding.rightConjugate (liftSub θ (barT K)) c ≤
      centralizer ({p} : Set G)) :
    ∃ u₀ : SpecialLinearGroup (Fin (2 + 2)) K, u₀ ∈ stdX K (le_rfl : 2 ≤ 2) ∧
      ∀ y : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))), (y : G) ∈ leviW θ →
        u₀⁻¹ * lam (γ y) * u₀ ∈
          (blkSL₁ : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin (2 + 2)) K).range := by
  have hk : (2 : ℕ) ≤ 2 := le_rfl
  have hYX := leviW_le_perfectCore hk hker hθ hq4 hpA hθp
  obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_ne_one_of_four hq4
  have hlu1 : Units.mk0 l hl0 ≠ 1 := fun h => hl1 (by simpa using congrArg Units.val h)
  obtain ⟨⟨δ, hδA⟩, hθδ⟩ := hθ (proj (2 + 2) K (torus (Units.mk0 l hl0)))
  have hδT : θ ⟨δ, hδA⟩ ∈ barT K := by rw [hθδ]; exact ⟨_, rfl⟩
  have ht : c⁻¹ * δ * c ∈ AschbacherTightEmbedding.rightConjugate (liftSub θ (barT K)) c := by
    rw [AschbacherTightEmbedding.mem_rightConjugate_iff]
    simpa [mul_assoc] using mem_liftSub.mpr ⟨hδA, hδT⟩
  have htN := hTN ht
  have htC := hTC ht
  obtain ⟨α, hα, hαpow⟩ := exists_inducedAut_of_mem_normalizer hker hθ htN
  have hNodd : Odd ((Nat.card K - 1) * Nat.card (center ↥A)) :=
    (odd_card_sub_one_of_two_pow hm hK).mul hodd
  have htpow : ∀ n : ℕ, (c⁻¹ * δ * c) ^ n = c⁻¹ * δ ^ n * c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih, pow_succ]
      group
  have hαN : α ^ ((Nat.card K - 1) * Nat.card (center ↥A)) = 1 := hαpow _ (by
    rw [htpow, pow_eq_one_of_theta_torus hker hδA hθδ, mul_one, inv_mul_cancel])
  have hα1 : α ≠ 1 := by
    intro h1
    have hσ : linNormConj htN = 1 :=
      eq_one_of_theta_eq hker hA _ fun a => by rw [← hα, h1, MulAut.one_apply]
    obtain ⟨x₁, hx₁⟩ := exists_lam_eq_of_mem_perfectCore hk hθ hker hodd hpA hp2 hθp hlamX hlam
      (trSL_mem_perfectCore_stdCen hk h4 (idxW_ne_idxU hk).symm (idxU_ne_idxV hk)
        (idxW_ne_idxU hk) 1)
    have h2 := congrArg (fun σ' : MulAut ↥A =>
      ((σ' (Subgroup.inclusion (perfectCore_inf_le A p) (γ x₁)) : ↥A) : G)) hσ
    simp only [coe_linNormConj, MulAut.one_apply, Subgroup.coe_inclusion, hγ] at h2
    have hcomm : δ * (x₁ : G) = x₁ * δ := by
      have h4 : δ * x₁ * δ⁻¹ = x₁ := by
        have h3 := congrArg (fun z => c * z * c⁻¹) h2
        calc δ * x₁ * δ⁻¹ = c * (c⁻¹ * δ * c * (c⁻¹ * x₁ * c) * (c⁻¹ * δ * c)⁻¹) * c⁻¹ := by
              group
          _ = c * (c⁻¹ * x₁ * c) * c⁻¹ := h3
          _ = x₁ := by group
      calc δ * (x₁ : G) = δ * x₁ * δ⁻¹ * δ := by group
        _ = x₁ * δ := by rw [h4]
    have h5 : θ ⟨δ, hδA⟩ * θ (Subgroup.inclusion (perfectCore_inf_le A p) x₁) =
        θ (Subgroup.inclusion (perfectCore_inf_le A p) x₁) * θ ⟨δ, hδA⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hcomm
    rw [hθδ, ← hlam, hx₁] at h5
    exact torus_mul_trSL_ne hlu1 (commute_of_proj_commute (by rw [sq, trSL_mul_self_charTwo]) h5)
  have hYperf : ⁅leviW θ, leviW θ⁆ = leviW θ := commutator_levLift hker hθ (commutator_barW hq4)
  have hWperf : ⁅((leviW θ).subgroupOf (perfectCore (A ⊓ centralizer ({p} : Set G)))).map
      (lam.comp γ.toMonoidHom), ((leviW θ).subgroupOf
        (perfectCore (A ⊓ centralizer ({p} : Set G)))).map (lam.comp γ.toMonoidHom)⁆ =
      ((leviW θ).subgroupOf (perfectCore (A ⊓ centralizer ({p} : Set G)))).map
        (lam.comp γ.toMonoidHom) := by
    rw [← map_commutator, commutator_subgroupOf_eq_self hYX hYperf]
  have hWX : ((leviW θ).subgroupOf (perfectCore (A ⊓ centralizer ({p} : Set G)))).map
      (lam.comp γ.toMonoidHom) ≤ stdX K hk := by
    rintro _ ⟨y, -, rfl⟩
    exact hlamX _
  have hcov : ∀ N : SpecialLinearGroup (StdMid hk) K, ∃ g ∈ ((((leviW θ).subgroupOf
      (perfectCore (A ⊓ centralizer ({p} : Set G)))).map (lam.comp γ.toMonoidHom) :
        Subgroup (SpecialLinearGroup (Fin (2 + 2)) K)) : Set (SpecialLinearGroup (Fin (2 + 2)) K)),
      stdRhoMat hk (g : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) =
        (N : Matrix (StdMid hk) (StdMid hk) K) := by
    intro N
    obtain ⟨y, hy, hyθ⟩ := exists_mem_levLift hθ (commutator_barW hq4)
      (⟨(slIndexEquiv K midEquivTwo).symm (β.symm N), rfl⟩ :
        proj (2 + 2) K (blkSL₁ ((slIndexEquiv K midEquivTwo).symm (β.symm N))) ∈ barW K 2)
    have hlamy : lam ⟨y, hYX hy⟩ = blkSL₁ ((slIndexEquiv K midEquivTwo).symm (β.symm N)) :=
      proj_injOn_stdX hk (hlamX _) (perfectCore_stdCen_le_stdX hk
        (blkSL₁_range_le_perfectCore hk h4 ⟨_, rfl⟩)) (by rw [hlam]; exact hyθ)
    have hψy : ψ ⟨y, hYX hy⟩ = β.symm N :=
      Subtype.ext (by rw [hψ, hlamy, stdRhoMat_blkSL₁_midEquivTwo])
    refine ⟨lam (γ ⟨y, hYX hy⟩), ⟨⟨y, hYX hy⟩, hy, rfl⟩, ?_⟩
    rw [← hψ, ← hβ, hψy, MulEquiv.apply_symm_apply]
  have hfix : ∀ g ∈ ((((leviW θ).subgroupOf
      (perfectCore (A ⊓ centralizer ({p} : Set G)))).map (lam.comp γ.toMonoidHom) :
        Subgroup (SpecialLinearGroup (Fin (2 + 2)) K)) : Set (SpecialLinearGroup (Fin (2 + 2)) K)),
      α (proj (2 + 2) K g) = proj (2 + 2) K g := by
    rintro _ ⟨y, hy, rfl⟩
    change α (proj (2 + 2) K (lam (γ y))) = proj (2 + 2) K (lam (γ y))
    rw [hlam]
    refine inducedAut_eq_of_commute htN hα ?_
    have hyδ : (y : G) * δ = δ * y :=
      mem_centralizer_singleton_iff.mp (leviW_le_centralizer_of_barT hker hδA hδT hy)
    change c⁻¹ * δ * c * ((γ y : ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))) : G) =
      ((γ y : ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))) : G) * (c⁻¹ * δ * c)
    rw [hγ]
    calc c⁻¹ * δ * c * (c⁻¹ * y * c) = c⁻¹ * (δ * y) * c := by group
      _ = c⁻¹ * (y * δ) * c := by rw [hyδ]
      _ = c⁻¹ * y * c * (c⁻¹ * δ * c) := by group
  have hfixT : α (proj (2 + 2) K (trSL (idxU hk) (idxV hk) (idxU_ne_idxV _) 1)) =
      proj (2 + 2) K (trSL (idxU hk) (idxV hk) (idxU_ne_idxV _) 1) := by
    rw [← hθp]
    exact inducedAut_eq_of_commute htN hα (mem_centralizer_singleton_iff.mp htC)
  obtain ⟨B, hαB, hT, hBS, b, hb⟩ := exists_conjAut_of_fix_two hNodd hαN (fun g hg => hWX hg)
    hcov hfix hfixT
  have hu := mulVec_u_of_commute_stdT hk hT
  have hv := vecMul_v_of_commute_stdT hk hT
  have ha := ne_zero_of_mulVec_eq_smul hk hu
  have hμ : (B.1 (idxU hk) (idxU hk))⁻¹ * b ≠ 1 := by
    intro h
    have hba := ((inv_mul_eq_one₀ ha).mp h).symm
    apply hα1
    rw [hαB] at hαN ⊢
    exact eq_one_of_pow_four_of_pow_odd hNodd
      (conjAut_pow_four_of_rho_eq hk B hu hv (by rw [hb, hba])) hαN
  obtain ⟨u₀, hu₀X, hu₀⟩ := exists_conj_mem_range_blkSL₁_of_matrix hk hWperf hWX
    (fun g _ => blockOneShape_of_two _) (fixesStdEnds_inv_smul hk ha hu hv) hμ
    (torusOneShape_inv_smul_of_two _ b hb) fun g hg => by
      rw [Matrix.smul_mul, Matrix.mul_smul, hBS g hg]
  exact ⟨u₀, hu₀X, fun y hy => hu₀ _ ⟨y, hy, rfl⟩⟩

theorem exists_map_theta_rightConjugate_eq_two (h4 : 4 ≤ Nat.card K)
    (hq4 : ∃ s : Finset K, s.card = 4) {m : ℕ} (hm2 : 2 ≤ m) (hK : Nat.card K = 2 ^ m)
    {θ : ↥A →* projectiveSL (2 + 2) K} (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A)
    (hodd : Odd (Nat.card (center ↥A))) (hA : commutator ↥A = ⊤) {p : G} (hpA : p ∈ A)
    (hp2 : p ^ 2 = 1)
    (hθp : θ ⟨p, hpA⟩ = proj (2 + 2) K (trSL (idxU (le_rfl : 2 ≤ 2)) (idxV (le_rfl : 2 ≤ 2))
      (idxU_ne_idxV _) 1)) {c : G}
    (hXc : AschbacherTightEmbedding.rightConjugate (perfectCore (A ⊓ centralizer ({p} : Set G)))
      c = perfectCore (A ⊓ centralizer ({p} : Set G)))
    (hTN : AschbacherTightEmbedding.rightConjugate (liftSub θ (barT K)) c ≤
      normalizer (A : Set G))
    (hTC : AschbacherTightEmbedding.rightConjugate (liftSub θ (barT K)) c ≤
      centralizer ({p} : Set G)) :
    ∃ u₀ : SpecialLinearGroup (Fin (2 + 2)) K, u₀ ∈ stdX K (le_rfl : 2 ≤ 2) ∧
      ((AschbacherTightEmbedding.rightConjugate (leviW θ) c).subgroupOf A).map θ =
        (barW K 2).map (conjAut (2 + 2) K (SpecialLinearGroup.toGL u₀)).toMonoidHom := by
  have hk : (2 : ℕ) ≤ 2 := le_rfl
  obtain ⟨lam, ψ, hlamX, hlam, hψ⟩ := exists_linPsi hk hθ hker hodd hpA hp2 hθp
  have hYX := leviW_le_perfectCore hk hker hθ hq4 hpA hθp
  obtain ⟨γ, hγ⟩ : ∃ γ : MulAut ↥(perfectCore (A ⊓ centralizer ({p} : Set G))),
      ∀ x, ((γ x : ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))) : G) = c⁻¹ * x * c :=
    ⟨((MulAut.conj c⁻¹).subgroupMap _).trans (MulEquiv.subgroupCongr hXc), fun x => by
      change c⁻¹ * (x : G) * c⁻¹⁻¹ = _
      rw [inv_inv]⟩
  obtain ⟨β, hβ⟩ := exists_mulAut_linPsi hk h4 hq4 (by omega) hK hθ hker hodd hpA hp2 hθp hlamX
    hlam hψ γ
  obtain ⟨u₀, hu₀X, hu₀⟩ := exists_conj_lam_mem_range_two h4 hq4 (by omega) hK hθ hker hodd hA
    hpA hp2 hθp hlamX hlam hψ hγ hβ hTN hTC
  refine ⟨u₀, hu₀X, ?_⟩
  have hYcA : AschbacherTightEmbedding.rightConjugate (leviW θ) c ≤ A := by
    have h1 : AschbacherTightEmbedding.rightConjugate (leviW θ) c ≤
        AschbacherTightEmbedding.rightConjugate (perfectCore (A ⊓ centralizer ({p} : Set G))) c :=
      Subgroup.map_mono hYX
    rw [hXc] at h1
    exact h1.trans (perfectCore_inf_le A p)
  have hle : ((AschbacherTightEmbedding.rightConjugate (leviW θ) c).subgroupOf A).map θ ≤
      (barW K 2).map (conjAut (2 + 2) K (SpecialLinearGroup.toGL u₀)).toMonoidHom := by
    rintro _ ⟨a, ha, rfl⟩
    have hy : c * (a : G) * c⁻¹ ∈ leviW θ :=
      (AschbacherTightEmbedding.mem_rightConjugate_iff _ _ _).mp ha
    have hθa : θ a = proj (2 + 2) K (lam (γ ⟨c * a * c⁻¹, hYX hy⟩)) := by
      rw [hlam]
      congr 1
      apply Subtype.ext
      change (a : G) = ((γ ⟨c * a * c⁻¹, hYX hy⟩ :
        ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))) : G)
      rw [hγ]
      change (a : G) = c⁻¹ * (c * a * c⁻¹) * c
      group
    obtain ⟨X₃, hX₃⟩ := hu₀ ⟨c * a * c⁻¹, hYX hy⟩ hy
    have h1 : lam (γ ⟨c * a * c⁻¹, hYX hy⟩) = u₀ * blkSL₁ X₃ * u₀⁻¹ := by
      rw [hX₃]
      group
    refine ⟨proj (2 + 2) K (blkSL₁ X₃), ⟨X₃, rfl⟩, ?_⟩
    rw [hθa, h1]
    change conjAut (2 + 2) K (SpecialLinearGroup.toGL u₀) (proj (2 + 2) K (blkSL₁ X₃)) = _
    rw [conjAut_proj, slConjugation_toGL_eq_mul_mul_inv]
  refine (Subgroup.eq_of_le_of_card_ge hle ?_)
  rw [Subgroup.card_map_of_injective
      (f := (conjAut (2 + 2) K (SpecialLinearGroup.toGL u₀)).toMonoidHom)
      (conjAut (2 + 2) K (SpecialLinearGroup.toGL u₀)).injective,
    card_map_theta_rightConjugate_leviW hk hm2 hK hker hθ hodd hq4 hYcA]

end StepOne

section StepTwoHelpers

variable {K : Type} [Field K]

theorem commute_stdT_of_mem_stdX {k : ℕ} (hk : 2 ≤ k) {g : SpecialLinearGroup (Fin (2 + k)) K}
    (hg : g ∈ stdX K hk) :
    g * trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) 1 =
      trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) 1 * g := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_trSL,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    mul_single_uv_of_col hk fun x => by rw [stdX_apply_u hk hg, one_apply, Pi.single_apply],
    single_uv_mul_of_row hk fun y => by
      rw [stdX_apply_v hk hg, one_apply, Pi.single_apply]
      by_cases h : y = idxV hk
      · subst h
        simp
      · simp [h, Ne.symm h]]

theorem exists_scalar_of_conjAut_eq_one_charTwo [CharP K 2] {n : ℕ} (B : GL (Fin n) K)
    (h : conjAut n K B = 1) :
    ∃ z : K, (B : Matrix (Fin n) (Fin n) K) = scalar (Fin n) z := by
  obtain ⟨z, hz⟩ := mem_range_scalar_of_commute_single
    (M := (B : Matrix (Fin n) (Fin n) K)) fun i j hij => by
      have h1 := congrArg (fun α : MulAut (projectiveSL n K) => α (proj n K (trn i j hij 1))) h
      simp only [conjAut_proj, MulAut.one_apply] at h1
      have h2 := mul_eq_mul_of_proj_eq B (trn_sq i j hij 1) (trn_sq i j hij 1) h1
      rw [coe_trn, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h2
      exact (add_left_cancel h2).symm
  exact ⟨z, hz.symm⟩

theorem upper_of_commute_single01 {D : Matrix (Fin 2) (Fin 2) K}
    (h : D * single 0 1 1 = single 0 1 1 * D) : D 1 0 = 0 ∧ D 0 0 = D 1 1 := by
  have h11 := congrFun (congrFun h 1) 1
  have h01 := congrFun (congrFun h 0) 1
  simp [Matrix.mul_apply, single_apply] at h11 h01
  exact ⟨h11, h01⟩

theorem sq_eq_smul_one_of_upper [CharP K 2] {D : Matrix (Fin 2) (Fin 2) K} (h10 : D 1 0 = 0)
    (h01 : D 0 0 = D 1 1) : D * D = (D 0 0 * D 0 0) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have h : D 0 0 * D 0 1 + D 0 1 * D 0 0 = 0 := by
    rw [mul_comm (D 0 1), CharTwo.add_self_eq_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h, ← h01]

theorem apply_zero_one_eq_zero_of_pow_odd [CharP K 2] {D : Matrix (Fin 2) (Fin 2) K}
    (h10 : D 1 0 = 0) (h01 : D 0 0 = D 1 1) (hd : D 0 0 ≠ 0) {N : ℕ} (hN : Odd N) {s : K}
    (hDN : D ^ N = s • (1 : Matrix (Fin 2) (Fin 2) K)) : D 0 1 = 0 := by
  obtain ⟨j, rfl⟩ := hN
  have h1 : D ^ (2 * j + 1) = (D 0 0 * D 0 0) ^ j • D := by
    rw [pow_succ, pow_mul, sq, sq_eq_smul_one_of_upper h10 h01, smul_pow, one_pow, smul_mul_assoc,
      Matrix.one_mul]
  rw [h1] at hDN
  have h2 := congrFun (congrFun hDN 0) 1
  simp only [Matrix.smul_apply, smul_eq_mul, one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    mul_zero] at h2
  exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero _ (mul_ne_zero hd hd))

end StepTwoHelpers

section StepTwo

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem fixes_conj_barL_two {u₀ : SpecialLinearGroup (Fin (2 + 2)) K}
    (hu₀X : u₀ ∈ stdX K (le_rfl : 2 ≤ 2)) {α : MulAut (projectiveSL (2 + 2) K)} {N : ℕ}
    (hN : Odd N) (hαN : α ^ N = 1)
    (hW : ∀ w ∈ barW K 2, α (conjAut (2 + 2) K (SpecialLinearGroup.toGL u₀) w) =
      conjAut (2 + 2) K (SpecialLinearGroup.toGL u₀) w)
    (hT : α (proj (2 + 2) K (trSL (idxU (le_rfl : 2 ≤ 2)) (idxV (le_rfl : 2 ≤ 2))
      (idxU_ne_idxV _) 1)) = proj (2 + 2) K (trSL (idxU (le_rfl : 2 ≤ 2))
        (idxV (le_rfl : 2 ≤ 2)) (idxU_ne_idxV _) 1)) :
    ∀ l ∈ barL K 2, α (conjAut (2 + 2) K (SpecialLinearGroup.toGL u₀) l) =
      conjAut (2 + 2) K (SpecialLinearGroup.toGL u₀) l := by
  set H := conjAut (2 + 2) K (SpecialLinearGroup.toGL u₀) with hH
  set t₀ := trSL (idxU (le_rfl : 2 ≤ 2)) (idxV (le_rfl : 2 ≤ 2)) (idxU_ne_idxV _) (1 : K)
    with ht₀def
  have hα''N : (H⁻¹ * α * H) ^ N = 1 := by
    have h := conj_pow (a := H⁻¹) (b := α) (i := N)
    rw [inv_inv] at h
    rw [h, hαN, mul_one, inv_mul_cancel]
  have hHt : H (proj (2 + 2) K t₀) = proj (2 + 2) K t₀ := by
    rw [hH, conjAut_proj, slConjugation_toGL_eq_mul_mul_inv,
      commute_stdT_of_mem_stdX (le_rfl : 2 ≤ 2) hu₀X, mul_inv_cancel_right]
  have hW'' : ∀ w ∈ barW K 2, (H⁻¹ * α * H) w = w := by
    intro w hw
    rw [MulAut.mul_apply, MulAut.mul_apply, hW w hw, MulAut.inv_apply_self]
  have hT'' : (H⁻¹ * α * H) (proj (2 + 2) K t₀) = proj (2 + 2) K t₀ := by
    rw [MulAut.mul_apply, MulAut.mul_apply, hHt, hT]
    conv_lhs => rw [← hHt]
    rw [MulAut.inv_apply_self]
  obtain ⟨B, σ, hB⟩ := exists_conjAut_fieldAut_of_pow_odd (by norm_num) hN hα''N
  obtain ⟨hσ, c, D, hc, hBD⟩ := fix_barW_zero (B := B) (τ := σ) fun w hw => by
    rw [pow_zero, mul_one, ← hB]
    exact hW'' w hw
  rw [fieldAut_eq_one hσ, mul_one] at hB
  have ht2 : t₀ ^ 2 = 1 := by rw [sq, ht₀def, trSL_mul_self_charTwo]
  have hBt := mul_eq_mul_of_proj_eq B ht2 ht2 (by rw [← conjAut_proj, ← hB]; exact hT'')
  have ht₀ : (t₀ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) =
      blk 1 (1 + single ⟨0, by omega⟩ ⟨1, by omega⟩ 1) := by
    rw [ht₀def, coe_trSL, ← one_add_smul_stdE (le_rfl : 2 ≤ 2), one_smul, stdE_eq_single]
    rfl
  rw [hBD, ht₀, blk_mul, blk_mul] at hBt
  have hD := (blk_injective hBt).2
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at hD
  obtain ⟨h10, h01⟩ := upper_of_commute_single01 (add_left_cancel hD)
  have hBN : conjAut (2 + 2) K (B ^ N) = 1 := by rw [map_pow, ← hB, hα''N]
  obtain ⟨z, hz⟩ := exists_scalar_of_conjAut_eq_one_charTwo (B ^ N) hBN
  rw [Units.val_pow_eq_pow_val, hBD, blk_pow, scalar_eq_blk] at hz
  have hd : D 0 0 ≠ 0 := by
    have hdet := (det_ne_zero_of_blk hBD).2
    rw [det_fin_two, h10, mul_zero, sub_zero, ← h01] at hdet
    exact fun h0 => hdet (by rw [h0, mul_zero])
  have h0 := apply_zero_one_eq_zero_of_pow_odd h10 h01 hd hN (blk_injective hz).2
  have hDs : D = D 0 0 • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10, h0, ← h01]
  rintro _ ⟨S, rfl⟩
  have h1 : (H⁻¹ * α * H) (proj (2 + 2) K (blkSL₂ S)) = proj (2 + 2) K (blkSL₂ S) := by
    rw [hB, conjAut_proj, slConjugation_eq_of_mul_eq B (h' := blkSL₂ S) (by
      rw [hBD, coe_blkSL₂, blk_mul, blk_mul, hDs]
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one])]
  simp only [MonoidHom.comp_apply]
  calc α (H (proj (2 + 2) K (blkSL₂ S))) =
      H ((H⁻¹ * α * H) (proj (2 + 2) K (blkSL₂ S))) := by
        rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
    _ = H (proj (2 + 2) K (blkSL₂ S)) := by rw [h1]

end StepTwo

section StepThree

theorem levLift_le_centralizer_of_normalizer {G : Type} [Group G] {A : Subgroup G} {P : Type*}
    [Group P] {θ : ↥A →* P} (hker : θ.ker = center ↥A) {S : Subgroup P} {t : G}
    (ht : t ∈ normalizer (A : Set G)) {α : MulAut P}
    (hα : ∀ a, α (θ a) = θ (linNormConj ht a)) (hS : ∀ s ∈ S, α s = s) :
    levLift θ S ≤ centralizer ({t} : Set G) := by
  have key : ∀ a ∈ liftSub θ S, ∃ z : G, t * a * t⁻¹ = a * z ∧ ∃ hz : z ∈ A,
      (⟨z, hz⟩ : ↥A) ∈ center ↥A := by
    intro a ha
    obtain ⟨haA, haS⟩ := mem_liftSub.1 ha
    have hz : a⁻¹ * ((linNormConj ht ⟨a, haA⟩ : ↥A) : G) ∈ A :=
      mul_mem (inv_mem haA) (linNormConj ht ⟨a, haA⟩).2
    refine ⟨a⁻¹ * ((linNormConj ht ⟨a, haA⟩ : ↥A) : G), by rw [coe_linNormConj]; group, hz, ?_⟩
    rw [← hker, MonoidHom.mem_ker]
    have h1 : (⟨a⁻¹ * ((linNormConj ht ⟨a, haA⟩ : ↥A) : G), hz⟩ : ↥A) =
        (⟨a, haA⟩ : ↥A)⁻¹ * linNormConj ht ⟨a, haA⟩ := rfl
    rw [h1, map_mul, map_inv, ← hα, hS _ haS, inv_mul_cancel]
  rw [levLift, commutator_le]
  intro a ha b hb
  rw [mem_centralizer_singleton_iff]
  obtain ⟨z₁, hz₁, hz₁A, hz₁Z⟩ := key a ha
  obtain ⟨z₂, hz₂, hz₂A, hz₂Z⟩ := key b hb
  have hcomm : ∀ {z : G} (hzA : z ∈ A), (⟨z, hzA⟩ : ↥A) ∈ center ↥A → ∀ y ∈ A, z * y = y * z :=
    fun hzA hz y hy => congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩).symm
  have hconj : t * ⁅a, b⁆ * t⁻¹ = ⁅a, b⁆ := by
    rw [show t * ⁅a, b⁆ * t⁻¹ = ⁅t * a * t⁻¹, t * b * t⁻¹⁆ by
      simp only [commutatorElement_def]; group, hz₁, hz₂]
    exact commutatorElement_mul_mul_of_commute' (hcomm hz₁A hz₁Z b (liftSub_le hb))
      (hcomm hz₂A hz₂Z a (liftSub_le ha)) (hcomm hz₁A hz₁Z z₂ hz₂A)
  calc ⁅a, b⁆ * t = t * ⁅a, b⁆ * t⁻¹ * t := by rw [hconj]
    _ = t * ⁅a, b⁆ := by group

theorem eq_bot_of_map_theta_eq_bot {G : Type} [Group G] [Finite G] {A : Subgroup G} {P : Type*}
    [Group P] {θ : ↥A →* P} (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A)))
    {Q : Subgroup G} (hQA : Q ≤ A) (hQ2 : IsPGroup 2 ↥Q) (hbot : (Q.subgroupOf A).map θ = ⊥) :
    Q = ⊥ := by
  have hQ2' : IsPGroup 2 ↥(Q.subgroupOf A) := hQ2.of_equiv (subgroupOfEquivOfLe hQA).symm
  have hZ : Q.subgroupOf A ≤ center ↥A := by
    intro b hb
    rw [← hker, MonoidHom.mem_ker]
    have : θ b ∈ (Q.subgroupOf A).map θ := ⟨b, hb, rfl⟩
    rwa [hbot, mem_bot] at this
  have hbot' := eq_bot_of_isPGroup_two_of_odd hQ2'
    (Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hZ))
  rw [eq_bot_iff]
  intro q hq
  have : (⟨q, hQA hq⟩ : ↥A) ∈ Q.subgroupOf A := hq
  rw [hbot', mem_bot] at this
  exact (mem_bot).mpr (congrArg Subtype.val this)

theorem theta_mem_normalizer_map {G : Type} [Group G] {A : Subgroup G} {P : Type*} [Group P]
    (θ : ↥A →* P) {Q : Subgroup G} {a : ↥A} (ha : (a : G) ∈ normalizer (Q : Set G)) :
    θ a ∈ normalizer (((Q.subgroupOf A).map θ : Subgroup P) : Set P) :=
  le_normalizer_map θ ⟨a, mem_normalizer_iff.mpr fun h => mem_normalizer_iff.mp ha h, rfl⟩

end StepThree

section TransportBarW

variable {K : Type} [Field K] {k : ℕ}

theorem eq_bot_of_le_centralizer_map_barW [Finite K] [CharP K 2] (hk : 2 ≤ k)
    (hq4 : ∃ s : Finset K, s.card = 4) {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m)
    (H : MulAut (projectiveSL (2 + k) K)) {Q : Subgroup (projectiveSL (2 + k) K)}
    (hQ : Q ≤ centralizer (((barW K k).map H.toMonoidHom : Subgroup (projectiveSL (2 + k) K)) :
      Set (projectiveSL (2 + k) K)))
    (hQ2 : IsPGroup 2 ↥Q)
    (hLN : (barL K k).map H.toMonoidHom ≤ normalizer (Q : Set (projectiveSL (2 + k) K))) :
    Q = ⊥ := by
  have hQ' : Q.map H.symm.toMonoidHom ≤
      centralizer (barW K k : Set (projectiveSL (2 + k) K)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_iff]
    intro w hw
    apply H.injective
    change H (w * H.symm x) = H (H.symm x * w)
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact mem_centralizer_iff.mp (hQ hx) (H w) ⟨w, hw, rfl⟩
  have hLN' : barL K k ≤ normalizer ((Q.map H.symm.toMonoidHom :
      Subgroup (projectiveSL (2 + k) K)) : Set (projectiveSL (2 + k) K)) := by
    intro l hl
    have h2 : H.symm (H l) ∈ (normalizer (Q : Set (projectiveSL (2 + k) K))).map
        H.symm.toMonoidHom := ⟨H l, hLN ⟨l, hl, rfl⟩, rfl⟩
    rwa [H.symm_apply_apply, map_equiv_normalizer_eq] at h2
  have h1 := eq_bot_of_le_centralizer_barW hk hq4 hm hK hQ' (hQ2.map _) hLN'
  rw [eq_bot_iff]
  intro x hx
  have h3 : H.symm x ∈ Q.map H.symm.toMonoidHom := ⟨x, hx, rfl⟩
  rw [h1, mem_bot] at h3
  rw [mem_bot]
  simpa using congrArg H h3

end TransportBarW

section CoreTwo

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem levLift_conj_barL_le_centralizer_two {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m)
    {θ : ↥A →* projectiveSL (2 + 2) K} (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A)
    (hodd : Odd (Nat.card (center ↥A))) {p : G} (hpA : p ∈ A)
    (hθp : θ ⟨p, hpA⟩ = proj (2 + 2) K (trSL (idxU (le_rfl : 2 ≤ 2)) (idxV (le_rfl : 2 ≤ 2))
      (idxU_ne_idxV _) 1)) {c : G} {u₀ : SpecialLinearGroup (Fin (2 + 2)) K}
    (hu₀X : u₀ ∈ stdX K (le_rfl : 2 ≤ 2))
    (heq : ((AschbacherTightEmbedding.rightConjugate (leviW θ) c).subgroupOf A).map θ =
      (barW K 2).map (conjAut (2 + 2) K (SpecialLinearGroup.toGL u₀)).toMonoidHom)
    {t : G} (ht : t ∈ AschbacherTightEmbedding.rightConjugate (liftSub θ (barT K)) c)
    (htN : t ∈ normalizer (A : Set G)) (htp : t ∈ centralizer ({p} : Set G)) :
    levLift θ ((barL K 2).map (conjAut (2 + 2) K (SpecialLinearGroup.toGL u₀)).toMonoidHom) ≤
      centralizer ({t} : Set G) := by
  obtain ⟨hτA, hτT⟩ :=
    mem_liftSub.1 ((AschbacherTightEmbedding.mem_rightConjugate_iff _ _ _).mp ht)
  obtain ⟨l, hl⟩ := id hτT
  obtain ⟨α, hα, hαpow⟩ := exists_inducedAut_of_mem_normalizer hker hθ htN
  have hN := (odd_card_sub_one_of_two_pow hm hK).mul hodd
  have hαN : α ^ ((Nat.card K - 1) * Nat.card (center ↥A)) = 1 := hαpow _ (by
    have h1 : t = c⁻¹ * (c * t * c⁻¹) * c⁻¹⁻¹ := by group
    rw [h1, conj_pow, pow_eq_one_of_theta_torus hker hτA hl.symm]
    group)
  refine levLift_le_centralizer_of_normalizer hker htN hα ?_
  rintro _ ⟨x, hx, rfl⟩
  refine fixes_conj_barL_two hu₀X hN hαN ?_ ?_ x hx
  · intro w hw
    have hw' : conjAut (2 + 2) K (SpecialLinearGroup.toGL u₀) w ∈
        ((AschbacherTightEmbedding.rightConjugate (leviW θ) c).subgroupOf A).map θ := by
      rw [heq]
      exact ⟨w, hw, rfl⟩
    obtain ⟨a, ha, haw⟩ := hw'
    rw [← haw]
    refine inducedAut_eq_of_commute htN hα ?_
    have hy : c * (a : G) * c⁻¹ ∈ leviW θ :=
      (AschbacherTightEmbedding.mem_rightConjugate_iff _ _ _).mp ha
    have h1 : c * t * c⁻¹ * (c * a * c⁻¹) = c * a * c⁻¹ * (c * t * c⁻¹) :=
      (mem_centralizer_singleton_iff.mp (leviW_le_centralizer_of_barT hker hτA hτT hy)).symm
    calc t * (a : G) = c⁻¹ * (c * t * c⁻¹ * (c * a * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * a * c⁻¹ * (c * t * c⁻¹)) * c := by rw [h1]
      _ = a * t := by group
  · rw [← hθp]
    exact inducedAut_eq_of_commute htN hα (mem_centralizer_singleton_iff.mp htp)

theorem levLift_conj_barL_le_two {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m)
    (hq4 : ∃ s : Finset K, s.card = 4) {θ : ↥A →* projectiveSL (2 + 2) K}
    (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A)))
    {p : G} (hpA : p ∈ A)
    (hθp : θ ⟨p, hpA⟩ = proj (2 + 2) K (trSL (idxU (le_rfl : 2 ≤ 2)) (idxV (le_rfl : 2 ≤ 2))
      (idxU_ne_idxV _) 1)) {c : G}
    (hXc : AschbacherTightEmbedding.rightConjugate (perfectCore (A ⊓ centralizer ({p} : Set G)))
      c = perfectCore (A ⊓ centralizer ({p} : Set G)))
    (hTN : AschbacherTightEmbedding.rightConjugate (liftSub θ (barT K)) c ≤
      normalizer (A : Set G))
    (hTC : AschbacherTightEmbedding.rightConjugate (liftSub θ (barT K)) c ≤
      centralizer ({p} : Set G))
    {u₀ : SpecialLinearGroup (Fin (2 + 2)) K} (hu₀X : u₀ ∈ stdX K (le_rfl : 2 ≤ 2))
    (heq : ((AschbacherTightEmbedding.rightConjugate (leviW θ) c).subgroupOf A).map θ =
      (barW K 2).map (conjAut (2 + 2) K (SpecialLinearGroup.toGL u₀)).toMonoidHom) :
    levLift θ ((barL K 2).map (conjAut (2 + 2) K (SpecialLinearGroup.toGL u₀)).toMonoidHom) ≤
      A ⊓ centralizer (AschbacherTightEmbedding.rightConjugate (liftSub θ (barT K) ⊔ leviW θ) c :
        Set G) := by
  refine le_inf levLift_le ?_
  rw [le_centralizer_iff]
  have hsup : AschbacherTightEmbedding.rightConjugate (liftSub θ (barT K) ⊔ leviW θ) c =
      AschbacherTightEmbedding.rightConjugate (liftSub θ (barT K)) c ⊔
        AschbacherTightEmbedding.rightConjugate (leviW θ) c := map_sup _ _ _
  rw [hsup]
  refine sup_le ?_ ?_
  · intro t ht
    rw [mem_centralizer_iff]
    intro x hx
    exact mem_centralizer_singleton_iff.mp (levLift_conj_barL_le_centralizer_two hm hK hθ hker
      hodd hpA hθp hu₀X heq ht (hTN ht) (hTC ht) hx)
  · rw [← le_centralizer_iff]
    have hWA : AschbacherTightEmbedding.rightConjugate (leviW θ) c ≤ A := by
      have h1 : AschbacherTightEmbedding.rightConjugate (leviW θ) c ≤
          AschbacherTightEmbedding.rightConjugate
            (perfectCore (A ⊓ centralizer ({p} : Set G))) c :=
        Subgroup.map_mono (leviW_le_perfectCore le_rfl hker hθ hq4 hpA hθp)
      rw [hXc] at h1
      exact h1.trans (perfectCore_inf_le A p)
    have hYperf : ⁅leviW θ, leviW θ⁆ = leviW θ := commutator_levLift hker hθ (commutator_barW hq4)
    have hWperf : ⁅AschbacherTightEmbedding.rightConjugate (leviW θ) c,
        AschbacherTightEmbedding.rightConjugate (leviW θ) c⁆ =
        AschbacherTightEmbedding.rightConjugate (leviW θ) c := by
      change ⁅(leviW θ).map (MulAut.conj c⁻¹).toMonoidHom,
        (leviW θ).map (MulAut.conj c⁻¹).toMonoidHom⁆ = (leviW θ).map (MulAut.conj c⁻¹).toMonoidHom
      rw [← map_commutator, hYperf]
    intro x hx
    refine mem_centralizer_of_theta_commute hker hWA hWperf (a := ⟨x, levLift_le hx⟩)
      fun y hy => ?_
    have hyθ : θ ⟨y, hWA hy⟩ ∈
        (barW K 2).map (conjAut (2 + 2) K (SpecialLinearGroup.toGL u₀)).toMonoidHom := by
      rw [← heq]
      exact ⟨⟨y, hWA hy⟩, hy, rfl⟩
    obtain ⟨w, hw, hwe⟩ := hyθ
    obtain ⟨l, hl, hle⟩ := theta_mem_of_mem_levLift hx
    rw [← hwe, ← hle, ← map_mul, ← map_mul, barW_commute_barL hw hl]

theorem rigidCore_linear_two (h4 : 4 ≤ Nat.card K) (hq4 : ∃ s : Finset K, s.card = 4) {m : ℕ}
    (hm2 : 2 ≤ m) (hK : Nat.card K = 2 ^ m) {θ : ↥A →* projectiveSL (2 + 2) K}
    (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A)))
    (hA : commutator ↥A = ⊤) {p : G} (hpA : p ∈ A) (hp2 : p ^ 2 = 1)
    (hθp : θ ⟨p, hpA⟩ = proj (2 + 2) K (trSL (idxU (le_rfl : 2 ≤ 2)) (idxV (le_rfl : 2 ≤ 2))
      (idxU_ne_idxV _) 1)) :
    RigidCore A p (liftSub θ (barT K) ⊔ leviW θ) := by
  intro c hXc hYN hYC
  have hTY : AschbacherTightEmbedding.rightConjugate (liftSub θ (barT K)) c ≤
      AschbacherTightEmbedding.rightConjugate (liftSub θ (barT K) ⊔ leviW θ) c :=
    map_mono le_sup_left
  have hWY : AschbacherTightEmbedding.rightConjugate (leviW θ) c ≤
      AschbacherTightEmbedding.rightConjugate (liftSub θ (barT K) ⊔ leviW θ) c :=
    map_mono le_sup_right
  have hTN := hTY.trans hYN
  have hTC := hTY.trans hYC
  obtain ⟨u₀, hu₀X, heq⟩ := exists_map_theta_rightConjugate_eq_two h4 hq4 hm2 hK hθ hker hodd hA
    hpA hp2 hθp hXc hTN hTC
  have hLc := levLift_conj_barL_le_two (by omega) hK hq4 hθ hker hodd hpA hθp hXc hTN hTC hu₀X
    heq
  have hLperf : ⁅(barL K 2).map (conjAut (2 + 2) K (SpecialLinearGroup.toGL u₀)).toMonoidHom,
      (barL K 2).map (conjAut (2 + 2) K (SpecialLinearGroup.toGL u₀)).toMonoidHom⁆ =
      (barL K 2).map (conjAut (2 + 2) K (SpecialLinearGroup.toGL u₀)).toMonoidHom := by
    rw [← map_commutator, commutator_barL le_rfl hq4]
  intro Q hQ hQ2 hN
  have hQA : Q ≤ A := hQ.trans inf_le_left
  refine eq_bot_of_map_theta_eq_bot hker hodd hQA hQ2 ?_
  refine eq_bot_of_le_centralizer_map_barW le_rfl hq4 (by omega) hK
    (conjAut (2 + 2) K (SpecialLinearGroup.toGL u₀)) ?_
    ((hQ2.of_equiv (subgroupOfEquivOfLe hQA).symm).map θ) ?_
  · rw [← heq]
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have hab : (b : G) * a = a * b := mem_centralizer_iff.mp (hQ ha).2 b (hWY hb)
    rw [← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext hab)
  · intro l hl
    obtain ⟨x, hx, hxθ⟩ := exists_mem_levLift hθ hLperf hl
    rw [← hxθ]
    exact theta_mem_normalizer_map θ (hN (hLc hx))

end CoreTwo

end CFSG.ComponentClassification.RankTwoClassical
