module

public import CFSG.LargeExtraspecial.S4EightF2
public import CFSG.LargeExtraspecial.S4SevenA
public import CFSG.CGT.Timmesfeld75.StdPair

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module Matrix CFSG.CGT.Timmesfeld75 CFSG.Assembly.LowTwoRank

variable {m : ℕ} {K : Type} [Field K]

theorem conj_one_add_vecMulVec (A : GL (Fin m) K) (u v : Fin m → K) :
    (A : Matrix (Fin m) (Fin m) K) * (1 + vecMulVec u v) * ((A⁻¹ : GL (Fin m) K) :
      Matrix (Fin m) (Fin m) K) =
      1 + vecMulVec ((A : Matrix (Fin m) (Fin m) K) *ᵥ u)
        (v ᵥ* ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.mul_inv, mul_vecMulVec,
    vecMulVec_mul]

theorem det_one_add_vecMulVec {u v : Fin m → K} (h : v ⬝ᵥ u = 0) :
    (1 + vecMulVec u v).det = 1 := by
  rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, h, add_zero]

noncomputable def transvSL {u v : Fin m → K} (h : v ⬝ᵥ u = 0) : StatedSL m K :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (1 + vecMulVec u v)
    (by rw [det_one_add_vecMulVec h]; exact one_ne_zero),
    Subgroup.subset_closure (by
      show (GeneralLinearGroup.mkOfDetNeZero (1 + vecMulVec u v) _ :
        Matrix (Fin m) (Fin m) K).det = 1
      rw [GeneralLinearGroup.val_mkOfDetNeZero, det_one_add_vecMulVec h])⟩

theorem coe_transvSL {u v : Fin m → K} (h : v ⬝ᵥ u = 0) :
    (((transvSL h : StatedSL m K) : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      1 + vecMulVec u v :=
  GeneralLinearGroup.val_mkOfDetNeZero _ _

theorem exists_ne_zero_dotProduct_eq_zero (hm : 3 ≤ m) (c c' : Fin m → K) :
    ∃ b : Fin m → K, b ≠ 0 ∧ b ⬝ᵥ c = 0 ∧ b ⬝ᵥ c' = 0 := by
  let δ : (Fin m → K) → (Fin m → K) →ₗ[K] K := fun x =>
    { toFun := fun b => b ⬝ᵥ x
      map_add' := fun y z => add_dotProduct y z x
      map_smul' := fun r y => smul_dotProduct r y x }
  have hr : ∀ x, finrank K (LinearMap.range (δ x)) ≤ 1 := fun x =>
    (Submodule.finrank_le _).trans (by simp)
  exact exists_ne_zero_mem_ker_inf (δ c) (δ c') (hr c) (hr c') (by simpa using hm)

theorem vecMulVec_ne_zero {u v : Fin m → K} (hu : u ≠ 0) (hv : v ≠ 0) : vecMulVec u v ≠ 0 := by
  intro h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  have := congrFun (congrFun h i) j
  rw [vecMulVec_apply, Matrix.zero_apply] at this
  exact mul_ne_zero hi hj this

theorem eq_one_of_mem_scalars {X : GL (Fin m) K} (hX : X ∈ StatedScalars (Fin m) K)
    {c : Fin m → K} (hc : c ≠ 0) (hXc : (X : Matrix (Fin m) (Fin m) K) *ᵥ c = c) : X = 1 := by
  obtain ⟨u, rfl⟩ := hX
  have h1 : ((u : K) - 1) • c = 0 := by
    have : ((GeneralLinearGroup.scalar (Fin m) u : GL (Fin m) K) :
        Matrix (Fin m) (Fin m) K) *ᵥ c = (u : K) • c := by
      rw [GeneralLinearGroup.coe_scalar]
      ext i
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    rw [sub_smul, one_smul, ← this, hXc, sub_self]
  have hu : (u : K) = 1 := by
    rcases smul_eq_zero.mp h1 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hc
  have : u = 1 := Units.ext hu
  rw [this, map_one]

theorem eq_one_of_mem_scalars' {X : GL (Fin m) K} (hX : X ∈ StatedScalars (Fin m) K)
    {a : Fin m → K} (ha : a ≠ 0) (hXa : a ᵥ* (X : Matrix (Fin m) (Fin m) K) = a) : X = 1 := by
  obtain ⟨u, rfl⟩ := hX
  have h1 : ((u : K) - 1) • a = 0 := by
    have : a ᵥ* ((GeneralLinearGroup.scalar (Fin m) u : GL (Fin m) K) :
        Matrix (Fin m) (Fin m) K) = (u : K) • a := by
      rw [GeneralLinearGroup.coe_scalar]
      ext i
      simp [Matrix.scalar_apply, Matrix.vecMul_diagonal, mul_comm]
    rw [sub_smul, one_smul, ← this, hXa, sub_self]
  have hu : (u : K) = 1 := by
    rcases smul_eq_zero.mp h1 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h ha
  have : u = 1 := Units.ext hu
  rw [this, map_one]

theorem one_add_vecMulVec_mulVec (u v x : Fin m → K) :
    (1 + vecMulVec u v) *ᵥ x = x + (v ⬝ᵥ x) • u := by
  rw [add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]

theorem vecMul_one_add_vecMulVec (u v x : Fin m → K) :
    x ᵥ* (1 + vecMulVec u v) = x + (x ⬝ᵥ u) • v := by
  rw [vecMul_add, vecMul_one, vecMul_vecMulVec]

theorem inv_mulVec_mulVec (A : GL (Fin m) K) (x : Fin m → K) :
    ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ ((A : Matrix (Fin m) (Fin m) K) *ᵥ x) =
      x := by
  rw [mulVec_mulVec, Units.inv_mul, one_mulVec]

theorem vecMul_inv_vecMul (A : GL (Fin m) K) (x : Fin m → K) :
    (x ᵥ* ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) ᵥ* (A : Matrix (Fin m) (Fin m) K) =
      x := by
  rw [vecMul_vecMul, Units.inv_mul, vecMul_one]

theorem vecMul_vecMul_inv (A : GL (Fin m) K) (x : Fin m → K) :
    (x ᵥ* (A : Matrix (Fin m) (Fin m) K)) ᵥ* ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      x := by
  rw [vecMul_vecMul, Units.mul_inv, vecMul_one]

theorem inv_mul_one_add_vecMulVec_mul (A : GL (Fin m) K) (c b : Fin m → K) :
    (((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *
      (1 + vecMulVec ((A : Matrix (Fin m) (Fin m) K) *ᵥ c) b) * (A : Matrix (Fin m) (Fin m) K)) =
      1 + vecMulVec c (b ᵥ* (A : Matrix (Fin m) (Fin m) K)) := by
  have := conj_one_add_vecMulVec A⁻¹ ((A : Matrix (Fin m) (Fin m) K) *ᵥ c) b
  rw [inv_inv, inv_mulVec_mulVec] at this
  exact this

section Proj

variable [Finite K]

noncomputable abbrev psl (m : ℕ) (K : Type) [Field K] :
    StatedSL m K →* StatedProj (StatedSL m K) :=
  QuotientGroup.mk' _

omit [Finite K] in
theorem mem_conjSubgroup_transvImage {U : Subgroup (GL (Fin m) K)} {A Y : StatedSL m K}
    (h : ((A⁻¹ * Y * A : StatedSL m K) : GL (Fin m) K) ∈ U) :
    psl m K Y ∈ conjSubgroup (psl m K A) (transvImage m K U) := by
  refine ⟨psl m K (A⁻¹ * Y * A), ⟨_, mem_subgroupOf.mpr h, rfl⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  group

theorem mem_normalizer_transvImage {U : Subgroup (GL (Fin m) K)} {X : StatedSL m K}
    (h : ∀ Y : StatedSL m K, (Y : GL (Fin m) K) ∈ U →
      ((X * Y * X⁻¹ : StatedSL m K) : GL (Fin m) K) ∈ U) :
    psl m K X ∈ normalizer (transvImage m K U : Set (StatedProj (StatedSL m K))) := by
  refine mem_normalizer_of_conj_le fun t ht => ?_
  obtain ⟨Y, hY, rfl⟩ := ht
  exact ⟨X * Y * X⁻¹, mem_subgroupOf.mpr (h Y (mem_subgroupOf.mp hY)), by
    simp only [map_mul, map_inv]⟩

omit [Finite K] in
theorem psl_ne_one {X : StatedSL m K} (h : (X : GL (Fin m) K) ∉ StatedScalars (Fin m) K) :
    psl m K X ≠ 1 := by
  intro h1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h (mem_subgroupOf.mp h1)

theorem transvCenter_meet (hm : 3 ≤ m) {c : Fin m → K} (hc0 : c ≠ 0)
    (g : StatedProj (StatedSL m K)) :
    conjSubgroup g (transvImage m K (transvCenter m K c)) ⊓
      normalizer (transvImage m K (transvCenter m K c) : Set (StatedProj (StatedSL m K))) ≠
        ⊥ := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ g
  set c' := ((A : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ c with hc'def
  have hc' : c' ≠ 0 := fun h => hc0 (by
    rw [← inv_mulVec_mulVec (A : GL (Fin m) K) c, ← hc'def, h, mulVec_zero])
  obtain ⟨b, hb0, hbc, hbc'⟩ := exists_ne_zero_dotProduct_eq_zero hm c c'
  set X := transvSL hbc' with hX
  have hXc : (((X : StatedSL m K) : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ c = c := by
    rw [hX, coe_transvSL, one_add_vecMulVec_mulVec, hbc, zero_smul, add_zero]
  have hXc' : ((((X : StatedSL m K) : GL (Fin m) K)⁻¹ : GL (Fin m) K) :
      Matrix (Fin m) (Fin m) K) *ᵥ c = c := by
    conv_lhs => rw [← hXc]
    exact inv_mulVec_mulVec _ c
  refine (Subgroup.ne_bot_iff_exists_ne_one).mpr ⟨⟨psl m K X, mem_inf.mpr ⟨?_, ?_⟩⟩, ?_⟩
  · apply mem_conjSubgroup_transvImage
    refine ⟨b ᵥ* ((A : GL (Fin m) K) : Matrix (Fin m) (Fin m) K), ?_, ?_⟩
    · rw [← dotProduct_mulVec]
      exact hbc'
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hX, coe_transvSL]
      exact inv_mul_one_add_vecMulVec_mul (A : GL (Fin m) K) c b
  · apply mem_normalizer_transvImage
    rintro Y ⟨a, ha, hY⟩
    refine ⟨a ᵥ* ((((X : StatedSL m K) : GL (Fin m) K)⁻¹ : GL (Fin m) K) :
      Matrix (Fin m) (Fin m) K), ?_, ?_⟩
    · rw [← dotProduct_mulVec, hXc', ha]
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hY]
      rw [conj_one_add_vecMulVec, hXc]
  · intro h1
    have h1' : psl m K X = 1 := congrArg Subtype.val h1
    refine psl_ne_one (fun hsc => vecMulVec_ne_zero hc' hb0 ?_) h1'
    have h2 := congrArg (fun Y : GL (Fin m) K => (Y : Matrix (Fin m) (Fin m) K))
      (eq_one_of_mem_scalars hsc hc0 hXc)
    simp only [hX, coe_transvSL, Units.val_one] at h2
    exact add_eq_left.mp h2

theorem transvAxis_meet (hm : 3 ≤ m) {a : Fin m → K} (ha0 : a ≠ 0)
    (g : StatedProj (StatedSL m K)) :
    conjSubgroup g (transvImage m K (transvAxis m K a)) ⊓
      normalizer (transvImage m K (transvAxis m K a) : Set (StatedProj (StatedSL m K))) ≠ ⊥ := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ g
  set a' := a ᵥ* ((((A : GL (Fin m) K))⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)
    with ha'def
  have ha' : a' ≠ 0 := fun h => ha0 (by
    rw [← vecMul_inv_vecMul (A : GL (Fin m) K) a, ← ha'def, h, zero_vecMul])
  obtain ⟨w, hw0, hwa, hwa'⟩ := exists_ne_zero_dotProduct_eq_zero hm a a'
  have hw : a' ⬝ᵥ w = 0 := by rw [dotProduct_comm]; exact hwa'
  set X := transvSL hw with hX
  have haX : a ᵥ* (((X : StatedSL m K) : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = a := by
    rw [hX, coe_transvSL, vecMul_one_add_vecMulVec, dotProduct_comm, hwa, zero_smul, add_zero]
  have haX' : a ᵥ* ((((X : StatedSL m K) : GL (Fin m) K)⁻¹ : GL (Fin m) K) :
      Matrix (Fin m) (Fin m) K) = a := by
    conv_lhs => rw [← haX]
    exact vecMul_vecMul_inv _ a
  refine (Subgroup.ne_bot_iff_exists_ne_one).mpr ⟨⟨psl m K X, mem_inf.mpr ⟨?_, ?_⟩⟩, ?_⟩
  · apply mem_conjSubgroup_transvImage
    refine ⟨(((A : GL (Fin m) K))⁻¹ : GL (Fin m) K) *ᵥ w, ?_, ?_⟩
    · rw [dotProduct_mulVec, ← ha'def]
      exact hw
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hX, coe_transvSL]
      have := conj_one_add_vecMulVec (A : GL (Fin m) K)⁻¹ w a'
      rw [inv_inv, ha'def, vecMul_inv_vecMul] at this
      exact this
  · apply mem_normalizer_transvImage
    rintro Y ⟨v, hv, hY⟩
    refine ⟨(((X : StatedSL m K) : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ v, ?_, ?_⟩
    · rw [dotProduct_mulVec, haX, hv]
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hY]
      rw [conj_one_add_vecMulVec, haX']
  · intro h1
    have h1' : psl m K X = 1 := congrArg Subtype.val h1
    refine psl_ne_one (fun hsc => vecMulVec_ne_zero hw0 ha' ?_) h1'
    have h2 := congrArg (fun Y : GL (Fin m) K => (Y : Matrix (Fin m) (Fin m) K))
      (eq_one_of_mem_scalars' hsc ha0 haX)
    simp only [hX, coe_transvSL, Units.val_one] at h2
    exact add_eq_left.mp h2

end Proj

theorem pslTransvectionMeetInput :
    ∀ (m : ℕ) (K : Type) [Field K] [Finite K], 3 ≤ m →
      (∀ c : Fin m → K, c ≠ 0 → ∀ g : StatedProj (StatedSL m K),
        conjSubgroup g (transvImage m K (transvCenter m K c)) ⊓
          Subgroup.normalizer (transvImage m K (transvCenter m K c) :
            Set (StatedProj (StatedSL m K))) ≠ ⊥) ∧
      (∀ a : Fin m → K, a ≠ 0 → ∀ g : StatedProj (StatedSL m K),
        conjSubgroup g (transvImage m K (transvAxis m K a)) ⊓
          Subgroup.normalizer (transvImage m K (transvAxis m K a) :
            Set (StatedProj (StatedSL m K))) ≠ ⊥) := fun _ _ _ _ hm =>
  ⟨fun _ hc0 g => transvCenter_meet hm hc0 g, fun _ ha0 g => transvAxis_meet hm ha0 g⟩

end CFSG.LargeExtraspecial.S4
