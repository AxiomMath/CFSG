module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidLinSyl

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ABGLocalTools
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section StdX

variable {K : Type} [Field K] {k : ℕ}

variable (K) in
@[expose] def stdX (hk : 2 ≤ k) : Subgroup (SpecialLinearGroup (Fin (2 + k)) K) where
  carrier := {g | (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ Pi.single (idxU hk) 1 =
      Pi.single (idxU hk) 1 ∧
    Pi.single (idxV hk) 1 ᵥ* (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = Pi.single (idxV hk) 1}
  one_mem' := ⟨by
      change (1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ _ = _
      exact one_mulVec _, by
      change _ ᵥ* (1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = _
      exact vecMul_one _⟩
  mul_mem' := by
    rintro g h ⟨hg₁, hg₂⟩ ⟨hh₁, hh₂⟩
    refine ⟨?_, ?_⟩
    · change ((g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *
        (h : Matrix (Fin (2 + k)) (Fin (2 + k)) K)) *ᵥ _ = _
      rw [← mulVec_mulVec, hh₁, hg₁]
    · change _ ᵥ* ((g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *
        (h : Matrix (Fin (2 + k)) (Fin (2 + k)) K)) = _
      rw [← vecMul_vecMul, hg₂, hh₂]
  inv_mem' := by
    rintro g ⟨hg₁, hg₂⟩
    have hgi : (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *
        ((g⁻¹ : SpecialLinearGroup (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
          1 := by
      change (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) * adjugate _ = 1
      rw [mul_adjugate, g.2, one_smul]
    have hig : ((g⁻¹ : SpecialLinearGroup (Fin (2 + k)) K) :
        Matrix (Fin (2 + k)) (Fin (2 + k)) K) * (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
          1 := by
      change adjugate _ * (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = 1
      rw [adjugate_mul, g.2, one_smul]
    refine ⟨?_, ?_⟩
    · conv_lhs => rw [← hg₁]
      rw [mulVec_mulVec, hig, one_mulVec]
    · conv_lhs => rw [← hg₂]
      rw [vecMul_vecMul, hgi, vecMul_one]

theorem stdCen_mulVec {hk : 2 ≤ k} {g : SpecialLinearGroup (Fin (2 + k)) K}
    (hg : g ∈ stdCen K hk) : (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ Pi.single (idxU hk) 1 =
      (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxU hk) (idxU hk) • Pi.single (idxU hk) 1 := by
  rw [stdCen, mem_centralizer_singleton_iff] at hg
  have h := congrArg Subtype.val hg
  change (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) * (1 + single _ _ 1) =
    (1 + single _ _ 1) * (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) at h
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

theorem stdCen_vecMul {hk : 2 ≤ k} {g : SpecialLinearGroup (Fin (2 + k)) K}
    (hg : g ∈ stdCen K hk) : Pi.single (idxV hk) 1 ᵥ* (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxU hk) (idxU hk) • Pi.single (idxV hk) 1 := by
  rw [stdCen, mem_centralizer_singleton_iff] at hg
  have h := congrArg Subtype.val hg
  change (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) * (1 + single _ _ 1) =
    (1 + single _ _ 1) * (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) at h
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

variable (K) in
@[expose] def stdCenScalar (hk : 2 ≤ k) : ↥(stdCen K hk) →* K where
  toFun g := ((g : SpecialLinearGroup (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K)
    (idxU hk) (idxU hk)
  map_one' := one_apply_eq _
  map_mul' g h := by
    have hh := stdCen_mulVec h.2
    change (((g : SpecialLinearGroup (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *
      ((h : SpecialLinearGroup (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K))
        (idxU hk) (idxU hk) = _
    rw [Matrix.mul_apply, Finset.sum_eq_single (idxU hk)]
    · intro x _ hx
      have := congrFun hh x
      rw [mulVec_single_one, col_apply, Pi.smul_apply, Pi.single_eq_of_ne hx, smul_zero] at this
      rw [this, mul_zero]
    · intro h0
      exact absurd (Finset.mem_univ _) h0

theorem mem_stdX_of_mem_stdCen {hk : 2 ≤ k} {g : SpecialLinearGroup (Fin (2 + k)) K}
    (hg : g ∈ stdCen K hk)
    (h1 : (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxU hk) (idxU hk) = 1) : g ∈ stdX K hk :=
  ⟨by rw [stdCen_mulVec hg, h1, one_smul], by rw [stdCen_vecMul hg, h1, one_smul]⟩

theorem perfectCore_stdCen_le_stdX (hk : 2 ≤ k) : perfectCore (stdCen K hk) ≤ stdX K hk := by
  refine (CFSG.Quasithin.perfectCore_le_derivedSeriesOf _ 1).trans ?_
  change ⁅stdCen K hk, stdCen K hk⁆ ≤ stdX K hk
  rw [Subgroup.commutator_le]
  intro g hg h hh
  have hc : ⁅g, h⁆ ∈ stdCen K hk := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  refine mem_stdX_of_mem_stdCen hc ?_
  set s := stdCenScalar K hk
  set g' : ↥(stdCen K hk) := ⟨g, hg⟩
  set h' : ↥(stdCen K hk) := ⟨h, hh⟩
  have h1 : s g' * s g'⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h2 : s h' * s h'⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h3 : s ⁅g', h'⁆ = 1 := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul]
    calc s g' * s h' * s g'⁻¹ * s h'⁻¹ = (s g' * s g'⁻¹) * (s h' * s h'⁻¹) := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  exact h3

theorem centralizer_proj_stdT_eq [CharP K 2] (hk : 2 ≤ k) :
    centralizer ({(proj (2 + k) K (trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) (1 : K)))} :
      Set (projectiveSL (2 + k) K)) = (stdCen K hk).map (proj (2 + k) K) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨z, rfl⟩ := proj_surjective _ _ z
    refine ⟨z, ?_, rfl⟩
    change z ∈ stdCen K hk
    rw [stdCen, mem_centralizer_singleton_iff]
    exact commute_of_proj_commute_trSL _ (mem_centralizer_singleton_iff.mp hz)
  · exact map_centralizer_le _ _

theorem perfectCore_centralizer_proj_le [Finite K] [CharP K 2] (hk : 2 ≤ k) :
    perfectCore (centralizer ({(proj (2 + k) K
      (trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) (1 : K)))} : Set (projectiveSL (2 + k) K))) ≤
      (stdX K hk).map (proj (2 + k) K) := by
  rw [centralizer_proj_stdT_eq hk, ← CFSG.Quasithin.map_perfectCore]
  exact map_mono (perfectCore_stdCen_le_stdX hk)

theorem stdX_inf_scalars (hk : 2 ≤ k) : stdX K hk ⊓ scalars (2 + k) K = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨hg, -⟩, ⟨c, -, hc⟩⟩
  rw [mem_bot]
  apply Subtype.ext
  have h := congrFun hg (idxU hk)
  rw [hc, mulVec_single_one, col_apply, scalar_apply, diagonal_apply_eq, Pi.single_eq_same] at h
  rw [hc, h, map_one]
  rfl

theorem proj_injOn_stdX (hk : 2 ≤ k) {g h : SpecialLinearGroup (Fin (2 + k)) K}
    (hg : g ∈ stdX K hk) (hh : h ∈ stdX K hk) (he : proj (2 + k) K g = proj (2 + k) K h) :
    g = h := by
  rw [proj_eq_proj_iff] at he
  have h1 : g⁻¹ * h ∈ stdX K hk ⊓ scalars (2 + k) K :=
    Subgroup.mem_inf.mpr ⟨(stdX K hk).mul_mem ((stdX K hk).inv_mem hg) hh, he⟩
  rw [stdX_inf_scalars, mem_bot] at h1
  exact (inv_mul_eq_one.mp h1)

end StdX

section Rho

variable {K : Type} [Field K] {k : ℕ}

abbrev StdMid (hk : 2 ≤ k) : Type := {x : Fin (2 + k) // x ≠ idxU hk ∧ x ≠ idxV hk}

@[expose] def stdRhoMat (hk : 2 ≤ k) (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) :
    Matrix (StdMid hk) (StdMid hk) K :=
  g.submatrix Subtype.val Subtype.val

theorem stdRhoMat_mul (hk : 2 ≤ k) {g h : SpecialLinearGroup (Fin (2 + k)) K}
    (hg : g ∈ stdX K hk) (hh : h ∈ stdX K hk) :
    stdRhoMat hk ((g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *
      (h : Matrix (Fin (2 + k)) (Fin (2 + k)) K)) =
      stdRhoMat hk (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *
        stdRhoMat hk (h : Matrix (Fin (2 + k)) (Fin (2 + k)) K) := by
  ext a b
  simp only [stdRhoMat, submatrix_apply, Matrix.mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun x => x ≠ idxU hk ∧ x ≠ idxV hk)]
  have hzero : ∑ i : {x : Fin (2 + k) // ¬ (x ≠ idxU hk ∧ x ≠ idxV hk)},
      (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) a.1 i.1 *
        (h : Matrix (Fin (2 + k)) (Fin (2 + k)) K) i.1 b.1 = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases not_and_or.mp i.2 with hi | hi <;> push Not at hi
    · have := congrFun hg.1 a.1
      rw [mulVec_single_one, col_apply, Pi.single_eq_of_ne a.2.1] at this
      rw [hi, this, zero_mul]
    · have := congrFun hh.2 b.1
      rw [single_one_vecMul, row_apply, Pi.single_eq_of_ne b.2.2] at this
      rw [hi, this, mul_zero]
  rw [hzero, add_zero]

variable (K) in
@[expose] noncomputable def stdRho (hk : 2 ≤ k) : ↥(stdX K hk) →* GL (StdMid hk) K :=
  MonoidHom.toHomUnits
    { toFun := fun g => stdRhoMat hk ((g : SpecialLinearGroup (Fin (2 + k)) K) :
        Matrix (Fin (2 + k)) (Fin (2 + k)) K)
      map_one' := by
        ext a b
        change (1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) a.1 b.1 = _
        simp only [one_apply, Subtype.ext_iff]
      map_mul' := fun g h => stdRhoMat_mul hk g.2 h.2 }

theorem stdX_sub_one_sq_apply (hk : 2 ≤ k) {g : SpecialLinearGroup (Fin (2 + k)) K}
    (hg : g ∈ stdX K hk) (hρ : stdRhoMat hk (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = 1)
    {x y : Fin (2 + k)} (hxy : ¬ (x = idxU hk ∧ y = idxV hk)) :
    (((g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) - 1) *
      ((g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) - 1)) x y = 0 := by
  set N := (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) - 1 with hN
  have hcol : ∀ z, N z (idxU hk) = 0 := by
    intro z
    have := congrFun hg.1 z
    rw [mulVec_single_one, col_apply] at this
    rw [hN, Matrix.sub_apply, this]
    by_cases hz : z = idxU hk
    · rw [hz, Pi.single_eq_same, one_apply_eq, sub_self]
    · rw [Pi.single_eq_of_ne hz, one_apply_ne hz, sub_zero]
  have hrow : ∀ z, N (idxV hk) z = 0 := by
    intro z
    have := congrFun hg.2 z
    rw [single_one_vecMul, row_apply] at this
    rw [hN, Matrix.sub_apply, this]
    by_cases hz : z = idxV hk
    · rw [hz, Pi.single_eq_same, one_apply_eq, sub_self]
    · rw [Pi.single_eq_of_ne hz, one_apply_ne (Ne.symm hz), sub_zero]
  have hmid : ∀ a b : StdMid hk, N a.1 b.1 = 0 := by
    intro a b
    have := congrFun (congrFun hρ a) b
    rw [stdRhoMat, submatrix_apply, one_apply] at this
    rw [hN, Matrix.sub_apply, this, one_apply]
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

theorem stdX_pow_four_eq_one [CharP K 2] (hk : 2 ≤ k) {g : SpecialLinearGroup (Fin (2 + k)) K}
    (hg : g ∈ stdX K hk) (hρ : stdRhoMat hk (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = 1) :
    g ^ 4 = 1 := by
  apply Subtype.ext
  set N := (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) - 1 with hN
  have hg' : (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = 1 + N := by
    rw [hN, add_sub_cancel]
  have hNN : N * N * (N * N) = 0 := by
    ext x y
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases h1 : x = idxU hk ∧ z = idxV hk
    · have hz : ¬ (z = idxU hk ∧ y = idxV hk) := fun h => idxU_ne_idxV hk (h.1.symm.trans h1.2)
      rw [stdX_sub_one_sq_apply hk hg hρ hz, mul_zero]
    · rw [stdX_sub_one_sq_apply hk hg hρ h1, zero_mul]
  have hadd : ∀ M : Matrix (Fin (2 + k)) (Fin (2 + k)) K, M + M = 0 := by
    intro M
    ext x y
    rw [Matrix.add_apply, CharTwo.add_self_eq_zero, Matrix.zero_apply]
  have hNN' : N + N = 0 := hadd N
  have hsq : (1 + N) * (1 + N) = 1 + N * N := by
    rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, add_assoc, ← add_assoc N N,
      hNN', zero_add]
  have hsq' : (1 + N * N) * (1 + N * N) = 1 := by
    rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, hNN, add_zero, add_assoc,
      hadd, add_zero]
  have hpow : ((g ^ 4 : SpecialLinearGroup (Fin (2 + k)) K) :
      Matrix (Fin (2 + k)) (Fin (2 + k)) K) = (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) ^ 4 :=
    Matrix.SpecialLinearGroup.coe_pow g 4
  rw [hpow, hg', show ((1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) + N) ^ 4 =
    ((1 + N) * (1 + N)) * ((1 + N) * (1 + N)) by noncomm_ring, hsq, hsq']
  rfl

theorem stdRhoMat_eq_one_of_commute [CharP K 2] (hk : 2 ≤ k)
    {g : SpecialLinearGroup (Fin (2 + k)) K} (hg : g ∈ stdX K hk) (hc : ∀ a : StdMid hk,
      proj (2 + k) K g * proj (2 + k) K (trSL (idxU hk) a.1 (Ne.symm a.2.1) 1) =
        proj (2 + k) K (trSL (idxU hk) a.1 (Ne.symm a.2.1) 1) * proj (2 + k) K g) :
    stdRhoMat hk (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = 1 := by
  have huu : (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxU hk) (idxU hk) = 1 := by
    have := congrFun hg.1 (idxU hk)
    rwa [mulVec_single_one, col_apply, Pi.single_eq_same] at this
  ext a b
  have h1 := congrArg Subtype.val (commute_of_proj_commute_trSL (Ne.symm a.2.1) (hc a))
  change (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) * (1 + single _ _ 1) =
    (1 + single _ _ 1) * (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) at h1
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h1
  have h1' := add_left_cancel h1
  have h2 := congrFun (congrFun h1' (idxU hk)) b.1
  rw [single_mul_apply_same, one_mul] at h2
  rw [stdRhoMat, submatrix_apply, ← h2]
  by_cases hab : a = b
  · subst hab
    rw [mul_single_apply_same, mul_one, huu, one_apply_eq]
  · rw [mul_single_apply_of_ne _ _ _ _ _ (fun h => hab (Subtype.ext h).symm), one_apply_ne hab]

theorem trSL_mem_stdX (hk : 2 ≤ k) {i j : Fin (2 + k)} (hij : i ≠ j) (hiv : i ≠ idxV hk)
    (hju : j ≠ idxU hk) (c : K) : trSL i j hij c ∈ stdX K hk := by
  refine ⟨?_, ?_⟩
  · change (1 + single i j c) *ᵥ _ = _
    ext x
    rw [Matrix.add_mulVec, one_mulVec, Pi.add_apply, mulVec_single_one, col_apply]
    simp only [single_apply, hju, and_false, ite_false, add_zero]
  · change _ ᵥ* (1 + single i j c) = _
    ext y
    rw [Matrix.vecMul_add, vecMul_one, Pi.add_apply, single_one_vecMul, row_apply]
    simp only [single_apply, hiv, false_and, ite_false, add_zero]

theorem stdRhoMat_trSL (hk : 2 ≤ k) {a b : StdMid hk} (hab : a ≠ b) (c : K) :
    stdRhoMat hk ((trSL a.1 b.1 (fun h => hab (Subtype.ext h)) c :
      SpecialLinearGroup (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
        1 + single a b c := by
  ext x y
  rw [stdRhoMat, submatrix_apply, coe_trSL, Matrix.add_apply, Matrix.add_apply, one_apply,
    one_apply, single_apply, single_apply]
  simp only [Subtype.ext_iff]

end Rho

end CFSG.ComponentClassification.RankTwoClassical
