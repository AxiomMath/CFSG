module

public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.Open.StatedAPI
public import CFSG.LieType.Universal.SpinOmega.Range

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank

section Center

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem statedScalars_subgroupOf_le_center (H : Subgroup (GL ι K)) :
    (StatedScalars ι K).subgroupOf H ≤ Subgroup.center H :=
  CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _

theorem exists_mul_ne_mul_statedProj {H : Subgroup (GL ι K)} [Group.IsPerfect H]
    [IsSimpleGroup (StatedProj H)] : ∃ a b : StatedProj H, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  exact Group.IsPerfect.not_isMulCommutative (StatedProj H) ⟨⟨hcon⟩⟩

theorem center_eq_statedScalars_subgroupOf {H : Subgroup (GL ι K)} [Group.IsPerfect H]
    [IsSimpleGroup (StatedProj H)] :
    Subgroup.center H = (StatedScalars ι K).subgroupOf H :=
  CFSG.LieType.CurtisTits.center_eq_of_isSimpleGroup_quotient _
    (statedScalars_subgroupOf_le_center H) inferInstance exists_mul_ne_mul_statedProj

theorem isQuasisimple_of_isSimpleGroup_statedProj {H : Subgroup (GL ι K)}
    [hperf : Group.IsPerfect H] [IsSimpleGroup (StatedProj H)] : IsQuasisimple H :=
  CFSG.LieType.CurtisTits.isQuasisimple_of_isSimpleGroup_quotient _
    (statedScalars_subgroupOf_le_center H) hperf inferInstance exists_mul_ne_mul_statedProj

theorem isPerfect_statedOmega {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ₀ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hQ : (polarBilin Q).Nondegenerate) {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂)
    (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) : Group.IsPerfect (StatedOmega Q₀) := by
  have : Group.IsPerfect (elementaryGroup Q) :=
    Group.isPerfect_def.mpr (commutator_elementaryGroup_eq_top h₁₂ h₁₃ h₂₃ hQ)
  exact Group.IsPerfect.ofSurjective (f := (statedOmegaEquiv hQ₀ hE).symm.toMonoidHom)
    (statedOmegaEquiv hQ₀ hE).symm.surjective

end Center

section Clifford

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

theorem commute_of_forall_mul_ι_eq_neg {x : CliffordAlgebra Q}
    (hx : ∀ v, x * ι Q v = -(ι Q v * x)) {y : CliffordAlgebra Q} (hy : y ∈ evenOdd Q 0) :
    Commute x y := by
  have hx' : ∀ (v : V) (z : CliffordAlgebra Q), x * (ι Q v * z) = -(ι Q v * (x * z)) :=
    fun v z => by rw [← mul_assoc, hx, neg_mul, mul_assoc]
  induction y, hy using CliffordAlgebra.even_induction with
  | algebraMap r => exact Algebra.commute_algebraMap_right r x
  | add y z _ _ hy hz => exact hy.add_right hz
  | ι_mul_ι_mul m₁ m₂ z _ hz =>
    show x * (ι Q m₁ * ι Q m₂ * z) = ι Q m₁ * ι Q m₂ * z * x
    simp only [mul_assoc]
    rw [hx', hx', mul_neg, neg_neg, hz.eq]

theorem mem_center_of_spinAction_eq_smul (hv : ∃ v, Q v ≠ 0) {x : spinGroup Q} {c : K}
    (hc : ∀ v, spinAction Q x v = c • v) : x ∈ Subgroup.center (spinGroup Q) := by
  obtain ⟨v₀, hv₀⟩ := hv
  have hc2 : c * c = 1 := by
    have h := map_spinAction Q x v₀
    rw [hc, map_smul_eq_sq] at h
    have h' : (c ^ 2 - 1) * Q v₀ = 0 := by rw [sub_mul, h, one_mul, sub_self]
    linear_combination (mul_eq_zero.mp h').resolve_right hv₀
  rcases mul_self_eq_one_iff.mp hc2 with rfl | rfl
  · apply ker_spinAction_le_center Q
    rw [MonoidHom.mem_ker]
    exact LinearEquiv.ext fun v => by rw [hc, one_smul]; rfl
  · rw [Subgroup.mem_center_iff]
    intro g
    have hanti : ∀ v, (x : CliffordAlgebra Q) * ι Q v = -(ι Q v * x) := fun v => by
      rw [(spinAction_apply_eq_iff' Q x v (-v)).mp (by rw [hc, neg_one_smul]), map_neg, neg_mul]
    have hg : (g : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
      rw [← even_toSubmodule]
      exact (Subalgebra.mem_toSubmodule _).mpr (spinGroup.mem_even g.2)
    exact Subtype.ext (commute_of_forall_mul_ι_eq_neg Q hanti hg).eq.symm

theorem exists_map_ne_zero_of_hypPair (P : HypPair Q) : ∃ v, Q v ≠ 0 :=
  ⟨P.e + P.f, by rw [QuadraticMap.map_add Q, P.Q_e, P.Q_f, P.polar_ef]; norm_num⟩

end Clifford

section Proj

variable {σ : Type} [Fintype σ] [DecidableEq σ] {K : Type} [Field K] (Q : QuadraticForm K (σ → K))
  {Q₀ : (σ → K) → K}

theorem spinMatrix_mem_of_range_eq (hR : (spinMatrix Q).range = StatedOmega Q₀)
    (x : spinGroup Q) : spinMatrix Q x ∈ StatedOmega Q₀ :=
  hR ▸ MonoidHom.mem_range.mpr ⟨x, rfl⟩

noncomputable def spinToStatedProj (hR : (spinMatrix Q).range = StatedOmega Q₀) :
    spinGroup Q →* StatedProj (StatedOmega Q₀) :=
  (QuotientGroup.mk' _).comp
    ((spinMatrix Q).codRestrict (StatedOmega Q₀) (spinMatrix_mem_of_range_eq Q hR))

theorem spinToStatedProj_apply (hR : (spinMatrix Q).range = StatedOmega Q₀) (x : spinGroup Q) :
    spinToStatedProj Q hR x =
      ((⟨spinMatrix Q x, spinMatrix_mem_of_range_eq Q hR x⟩ : StatedOmega Q₀) :
        StatedProj (StatedOmega Q₀)) := by
  simp only [spinToStatedProj, MonoidHom.comp_apply, MonoidHom.codRestrict_apply,
    QuotientGroup.mk'_apply]

theorem spinToStatedProj_surjective (hR : (spinMatrix Q).range = StatedOmega Q₀) :
    Function.Surjective (spinToStatedProj Q hR) := by
  intro y
  obtain ⟨⟨A, hA⟩, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨x, hx⟩ : A ∈ (spinMatrix Q).range := hR ▸ hA
  exact ⟨x, by rw [spinToStatedProj_apply]; exact congrArg _ (Subtype.ext hx)⟩

theorem ker_spinToStatedProj (hR : (spinMatrix Q).range = StatedOmega Q₀) :
    (spinToStatedProj Q hR).ker = (StatedScalars σ K).comap (spinMatrix Q) := by
  ext x
  rw [MonoidHom.mem_ker, spinToStatedProj_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, Subgroup.mem_comap]

theorem comap_statedScalars_le_center (hv : ∃ v, Q v ≠ 0) :
    (StatedScalars σ K).comap (spinMatrix Q) ≤ Subgroup.center (spinGroup Q) := by
  intro x hx
  rw [Subgroup.mem_comap, mem_statedScalars_iff, toLinEquiv_spinMatrix] at hx
  obtain ⟨c, hc⟩ := mem_scalars.mp hx
  exact mem_center_of_spinAction_eq_smul Q hv hc

theorem ker_spinToStatedProj_le_center (hR : (spinMatrix Q).range = StatedOmega Q₀)
    (hv : ∃ v, Q v ≠ 0) : (spinToStatedProj Q hR).ker ≤ Subgroup.center (spinGroup Q) := by
  rw [ker_spinToStatedProj]
  exact comap_statedScalars_le_center Q hv

theorem center_le_comap_statedScalars (hR : (spinMatrix Q).range = StatedOmega Q₀)
    (hZ : Subgroup.center (StatedOmega Q₀) = (StatedScalars σ K).subgroupOf (StatedOmega Q₀)) :
    Subgroup.center (spinGroup Q) ≤ (StatedScalars σ K).comap (spinMatrix Q) := by
  intro x hx
  have hmem : (⟨spinMatrix Q x, spinMatrix_mem_of_range_eq Q hR x⟩ : StatedOmega Q₀) ∈
      Subgroup.center (StatedOmega Q₀) := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨A, hA⟩
    obtain ⟨y, rfl⟩ : A ∈ (spinMatrix Q).range := hR ▸ hA
    apply Subtype.ext
    change spinMatrix Q y * spinMatrix Q x = spinMatrix Q x * spinMatrix Q y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
  rw [hZ, Subgroup.mem_subgroupOf] at hmem
  exact hmem

theorem ker_spinToStatedProj_eq_center (hR : (spinMatrix Q).range = StatedOmega Q₀)
    (hZ : Subgroup.center (StatedOmega Q₀) = (StatedScalars σ K).subgroupOf (StatedOmega Q₀))
    (hv : ∃ v, Q v ≠ 0) : (spinToStatedProj Q hR).ker = Subgroup.center (spinGroup Q) := by
  rw [ker_spinToStatedProj]
  exact le_antisymm (comap_statedScalars_le_center Q hv) (center_le_comap_statedScalars Q hR hZ)

noncomputable def spinQuotientCenterEquiv (hR : (spinMatrix Q).range = StatedOmega Q₀)
    (hZ : Subgroup.center (StatedOmega Q₀) = (StatedScalars σ K).subgroupOf (StatedOmega Q₀))
    (hv : ∃ v, Q v ≠ 0) :
    spinGroup Q ⧸ Subgroup.center (spinGroup Q) ≃* StatedProj (StatedOmega Q₀) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_spinToStatedProj_eq_center Q hR hZ hv).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (spinToStatedProj_surjective Q hR))

end Proj

section Odd

variable {n : ℕ} {K : Type} [Field K]

private theorem oddPairs (hn : 3 ≤ n) :
    (oddPair K (⟨0, by omega⟩ : Fin n)).Orth (oddPair K ⟨1, by omega⟩) ∧
      (oddPair K (⟨0, by omega⟩ : Fin n)).Orth (oddPair K ⟨2, by omega⟩) ∧
      (oddPair K (⟨1, by omega⟩ : Fin n)).Orth (oddPair K ⟨2, by omega⟩) :=
  ⟨oddPair_orth (by simp [Fin.ext_iff]), oddPair_orth (by simp [Fin.ext_iff]),
    oddPair_orth (by simp [Fin.ext_iff])⟩

theorem isPerfect_statedOmega_quadOdd (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    Group.IsPerfect (StatedOmega (StatedQuadOdd n K)) :=
  isPerfect_statedOmega (coe_quadOdd n K) (commutator_orthogonalGroup_quadOdd h2 hn)
    (nondegenerate_polarBilin_quadOdd n K h2) (oddPairs hn).1 (oddPairs hn).2.1 (oddPairs hn).2.2

theorem center_statedOmega_quadOdd (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    Subgroup.center (StatedOmega (StatedQuadOdd n K)) =
      (StatedScalars _ K).subgroupOf (StatedOmega (StatedQuadOdd n K)) := by
  have := isPerfect_statedOmega_quadOdd h2 hn
  have := isSimpleGroup_statedProj_statedOmega_quadOdd_of_two_ne_zero h2 hn
  exact center_eq_statedScalars_subgroupOf

theorem isQuasisimple_statedOmega_quadOdd (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    IsQuasisimple (StatedOmega (StatedQuadOdd n K)) := by
  have := isPerfect_statedOmega_quadOdd h2 hn
  have := isSimpleGroup_statedProj_statedOmega_quadOdd_of_two_ne_zero h2 hn
  exact isQuasisimple_of_isSimpleGroup_statedProj

theorem spinToStatedProj_quadOdd (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    Function.Surjective (spinToStatedProj (quadOdd n K) (range_spinMatrix_quadOdd h2 hn)) ∧
      (spinToStatedProj (quadOdd n K) (range_spinMatrix_quadOdd h2 hn)).ker =
        (StatedScalars _ K).comap (spinMatrix (quadOdd n K)) ∧
      (spinToStatedProj (quadOdd n K) (range_spinMatrix_quadOdd h2 hn)).ker =
        Subgroup.center (spinGroup (quadOdd n K)) :=
  ⟨spinToStatedProj_surjective _ _, ker_spinToStatedProj _ _,
    ker_spinToStatedProj_eq_center _ _ (center_statedOmega_quadOdd h2 hn)
      (exists_map_ne_zero_of_hypPair _ (oddPair K (⟨0, by omega⟩ : Fin n)))⟩

noncomputable def spinQuotientCenterEquivQuadOdd (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    spinGroup (quadOdd n K) ⧸ Subgroup.center (spinGroup (quadOdd n K)) ≃*
      StatedProj (StatedOmega (StatedQuadOdd n K)) :=
  spinQuotientCenterEquiv _ (range_spinMatrix_quadOdd h2 hn) (center_statedOmega_quadOdd h2 hn)
    (exists_map_ne_zero_of_hypPair _ (oddPair K (⟨0, by omega⟩ : Fin n)))

end Odd

section Plus

variable {n : ℕ} {K : Type} [Field K]

private theorem plusPairs (hn : 3 ≤ n) :
    (plusPair K (⟨0, by omega⟩ : Fin n)).Orth (plusPair K ⟨1, by omega⟩) ∧
      (plusPair K (⟨0, by omega⟩ : Fin n)).Orth (plusPair K ⟨2, by omega⟩) ∧
      (plusPair K (⟨1, by omega⟩ : Fin n)).Orth (plusPair K ⟨2, by omega⟩) :=
  ⟨plusPair_orth (by simp [Fin.ext_iff]), plusPair_orth (by simp [Fin.ext_iff]),
    plusPair_orth (by simp [Fin.ext_iff])⟩

theorem isPerfect_statedOmega_quadPlus (hn : 3 ≤ n) :
    Group.IsPerfect (StatedOmega (StatedQuadPlus n K)) :=
  isPerfect_statedOmega (coe_quadPlus n K) (commutator_orthogonalGroup_quadPlus hn)
    (nondegenerate_polarBilin_quadPlus n K) (plusPairs hn).1 (plusPairs hn).2.1 (plusPairs hn).2.2

theorem center_statedOmega_quadPlus (hn : 3 ≤ n) :
    Subgroup.center (StatedOmega (StatedQuadPlus n K)) =
      (StatedScalars _ K).subgroupOf (StatedOmega (StatedQuadPlus n K)) := by
  have := isPerfect_statedOmega_quadPlus (K := K) hn
  have := isSimpleGroup_statedProj_statedOmega_quadPlus (K := K) hn
  exact center_eq_statedScalars_subgroupOf

theorem isQuasisimple_statedOmega_quadPlus (hn : 3 ≤ n) :
    IsQuasisimple (StatedOmega (StatedQuadPlus n K)) := by
  have := isPerfect_statedOmega_quadPlus (K := K) hn
  have := isSimpleGroup_statedProj_statedOmega_quadPlus (K := K) hn
  exact isQuasisimple_of_isSimpleGroup_statedProj

theorem spinToStatedProj_quadPlus (hn : 3 ≤ n) :
    Function.Surjective (spinToStatedProj (quadPlus n K) (range_spinMatrix_quadPlus hn)) ∧
      (spinToStatedProj (quadPlus n K) (range_spinMatrix_quadPlus hn)).ker =
        (StatedScalars _ K).comap (spinMatrix (quadPlus n K)) ∧
      (spinToStatedProj (quadPlus n K) (range_spinMatrix_quadPlus hn)).ker =
        Subgroup.center (spinGroup (quadPlus n K)) :=
  ⟨spinToStatedProj_surjective _ _, ker_spinToStatedProj _ _,
    ker_spinToStatedProj_eq_center _ _ (center_statedOmega_quadPlus hn)
      (exists_map_ne_zero_of_hypPair _ (plusPair K (⟨0, by omega⟩ : Fin n)))⟩

noncomputable def spinQuotientCenterEquivQuadPlus (hn : 3 ≤ n) :
    spinGroup (quadPlus n K) ⧸ Subgroup.center (spinGroup (quadPlus n K)) ≃*
      StatedProj (StatedOmega (StatedQuadPlus n K)) :=
  spinQuotientCenterEquiv _ (range_spinMatrix_quadPlus hn) (center_statedOmega_quadPlus hn)
    (exists_map_ne_zero_of_hypPair _ (plusPair K (⟨0, by omega⟩ : Fin n)))

end Plus

section Minus

variable {n : ℕ} {K : Type} [Field K] {b c : K}

private theorem minusPairs (hn : 4 ≤ n) :
    (minusPair K b c (⟨0, by omega⟩ : Fin (n - 1))).Orth (minusPair K b c ⟨1, by omega⟩) ∧
      (minusPair K b c (⟨0, by omega⟩ : Fin (n - 1))).Orth (minusPair K b c ⟨2, by omega⟩) ∧
      (minusPair K b c (⟨1, by omega⟩ : Fin (n - 1))).Orth (minusPair K b c ⟨2, by omega⟩) :=
  ⟨minusPair_orth (by simp [Fin.ext_iff]), minusPair_orth (by simp [Fin.ext_iff]),
    minusPair_orth (by simp [Fin.ext_iff])⟩

theorem isPerfect_statedOmega_quadMinus [Finite K] (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Group.IsPerfect (StatedOmega (StatedQuadMinus n K b c)) :=
  isPerfect_statedOmega (coe_quadMinus n K b c) (commutator_orthogonalGroup_quadMinus hn hirr)
    (nondegenerate_polarBilin_quadMinus_of_finite n K hirr) (minusPairs hn).1
    (minusPairs hn).2.1 (minusPairs hn).2.2

theorem center_statedOmega_quadMinus [Finite K] (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Subgroup.center (StatedOmega (StatedQuadMinus n K b c)) =
      (StatedScalars _ K).subgroupOf (StatedOmega (StatedQuadMinus n K b c)) := by
  have := isPerfect_statedOmega_quadMinus hn hirr
  have := isSimpleGroup_statedProj_statedOmega_quadMinus hn hirr
  exact center_eq_statedScalars_subgroupOf

theorem isQuasisimple_statedOmega_quadMinus [Finite K] (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsQuasisimple (StatedOmega (StatedQuadMinus n K b c)) := by
  have := isPerfect_statedOmega_quadMinus hn hirr
  have := isSimpleGroup_statedProj_statedOmega_quadMinus hn hirr
  exact isQuasisimple_of_isSimpleGroup_statedProj

theorem spinToStatedProj_quadMinus [Finite K] (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Function.Surjective
        (spinToStatedProj (quadMinus n K b c) (range_spinMatrix_quadMinus hn hirr)) ∧
      (spinToStatedProj (quadMinus n K b c) (range_spinMatrix_quadMinus hn hirr)).ker =
        (StatedScalars _ K).comap (spinMatrix (quadMinus n K b c)) ∧
      (spinToStatedProj (quadMinus n K b c) (range_spinMatrix_quadMinus hn hirr)).ker =
        Subgroup.center (spinGroup (quadMinus n K b c)) :=
  ⟨spinToStatedProj_surjective _ _, ker_spinToStatedProj _ _,
    ker_spinToStatedProj_eq_center _ _ (center_statedOmega_quadMinus hn hirr)
      (exists_map_ne_zero_of_hypPair _ (minusPair K b c (⟨0, by omega⟩ : Fin (n - 1))))⟩

noncomputable def spinQuotientCenterEquivQuadMinus [Finite K] (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    spinGroup (quadMinus n K b c) ⧸ Subgroup.center (spinGroup (quadMinus n K b c)) ≃*
      StatedProj (StatedOmega (StatedQuadMinus n K b c)) :=
  spinQuotientCenterEquiv _ (range_spinMatrix_quadMinus hn hirr)
    (center_statedOmega_quadMinus hn hirr)
    (exists_map_ne_zero_of_hypPair _ (minusPair K b c (⟨0, by omega⟩ : Fin (n - 1))))

end Minus

end CFSG.LieType.Universal.Spin
