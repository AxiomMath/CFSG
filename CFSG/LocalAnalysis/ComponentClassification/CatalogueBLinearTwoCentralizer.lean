module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoCentralizerCharacter
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBLinearTwo

open Matrix CatalogueSchreierLinearTwo CFSG.GorensteinWalter

@[expose] def projectiveCentralizerProjection {K : Type*} [Field K]
    (A : GeneralLinearGroup (Fin 2) K) :
    projectiveCentralizerLift A →* Subgroup.centralizer {ProjGenLinGroup.mk A} :=
  (ProjGenLinGroup.mk.comp (projectiveCentralizerLift A).subtype).codRestrict _
    (fun B => B.property)

theorem projectiveCentralizerProjection_surjective {K : Type*} [Field K]
    (A : GeneralLinearGroup (Fin 2) K) :
    Function.Surjective (projectiveCentralizerProjection A) := by
  intro b
  obtain ⟨B, hB⟩ := ProjGenLinGroup.mk_surjective b.val
  refine ⟨⟨B, ?_⟩, Subtype.ext hB⟩
  change ProjGenLinGroup.mk B ∈ Subgroup.centralizer {ProjGenLinGroup.mk A}
  rw [hB]
  exact b.property

theorem projectiveCentralizerProjection_kernel_le {K : Type*} [Field K]
    (A : GeneralLinearGroup (Fin 2) K) :
    (projectiveCentralizerProjection A).ker ≤ (scalarDisplacementHom A).ker := by
  intro B hB
  change scalarDisplacement A B = 1
  apply (scalarDisplacement_eq_one_iff A B).mpr
  have hmk : ProjGenLinGroup.mk B.val = 1 := congrArg Subtype.val hB
  exact (Subgroup.mem_center_iff.mp (ProjGenLinGroup.mk_eq_one.mp hmk) A).symm

@[expose] def projectiveCentralizerQuotientEquiv {K : Type*} [Field K]
    (A : GeneralLinearGroup (Fin 2) K) :
    (projectiveCentralizerLift A ⧸ (projectiveCentralizerProjection A).ker) ≃*
      Subgroup.centralizer {ProjGenLinGroup.mk A} :=
  QuotientGroup.quotientKerEquivOfSurjective _ (projectiveCentralizerProjection_surjective A)

@[expose] def projectiveScalarCharacter {K : Type*} [Field K]
    (A : GeneralLinearGroup (Fin 2) K) :
    Subgroup.centralizer {ProjGenLinGroup.mk A} →* Kˣ :=
  (QuotientGroup.lift (projectiveCentralizerProjection A).ker
    (scalarDisplacementHom A) (projectiveCentralizerProjection_kernel_le A)).comp
      (projectiveCentralizerQuotientEquiv A).symm.toMonoidHom

theorem projectiveScalarCharacter_projection {K : Type*} [Field K]
    (A : GeneralLinearGroup (Fin 2) K) (B : projectiveCentralizerLift A) :
    projectiveScalarCharacter A (projectiveCentralizerProjection A B) =
      scalarDisplacement A B := by
  have h := (projectiveCentralizerQuotientEquiv A).symm_apply_apply
    ((QuotientGroup.mk' (projectiveCentralizerProjection A).ker) B)
  change (projectiveCentralizerQuotientEquiv A).symm
    (projectiveCentralizerProjection A B) = _ at h
  change QuotientGroup.lift _ (scalarDisplacementHom A)
    (projectiveCentralizerProjection_kernel_le A)
    ((projectiveCentralizerQuotientEquiv A).symm (projectiveCentralizerProjection A B)) = _
  rw [h]
  rfl

theorem scalarDisplacement_kernel_abelian {K : Type*} [Field K]
    (A : GeneralLinearGroup (Fin 2) K) (hne : ProjGenLinGroup.mk A ≠ 1) :
    IsMulCommutative (scalarDisplacementHom A).ker := by
  have hns : ¬ ∃ a : K, A.val = Matrix.scalar (Fin 2) a := by
    rintro ⟨a, ha⟩
    apply hne
    apply ProjGenLinGroup.mk_eq_one.mpr
    exact GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨a, ha.symm⟩
  refine ⟨⟨fun B C => ?_⟩⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  have hB := (scalarDisplacement_eq_one_iff A B.val).mp B.property
  have hC := (scalarDisplacement_eq_one_iff A C.val).mp C.property
  exact nonscalar_matrix_centralizer_commutative A.val B.val.val.val C.val.val.val
    hns (congrArg Units.val hB.symm) (congrArg Units.val hC.symm)

theorem projectiveScalarCharacter_kernel_eq {K : Type*} [Field K]
    (A : GeneralLinearGroup (Fin 2) K) :
    (projectiveScalarCharacter A).ker =
      (scalarDisplacementHom A).ker.map (projectiveCentralizerProjection A) := by
  ext b
  obtain ⟨B, rfl⟩ := projectiveCentralizerProjection_surjective A b
  constructor
  · intro hb
    refine ⟨B, ?_, rfl⟩
    change scalarDisplacement A B = 1
    exact (projectiveScalarCharacter_projection A B).symm.trans hb
  · rintro ⟨C, hC, hCB⟩
    rw [← hCB]
    change projectiveScalarCharacter A (projectiveCentralizerProjection A C) = 1
    rw [projectiveScalarCharacter_projection]
    exact hC

theorem projectiveScalarCharacter_kernel_abelian {K : Type*} [Field K]
    (A : GeneralLinearGroup (Fin 2) K) (hne : ProjGenLinGroup.mk A ≠ 1) :
    IsMulCommutative (projectiveScalarCharacter A).ker := by
  let : IsMulCommutative (scalarDisplacementHom A).ker :=
    scalarDisplacement_kernel_abelian A hne
  rw [projectiveScalarCharacter_kernel_eq]
  infer_instance

theorem projectiveScalarCharacter_square_eq_one {K : Type*} [Field K]
    (A : GeneralLinearGroup (Fin 2) K) (hsquare : ProjGenLinGroup.mk A ^ 2 = 1)
    (b : Subgroup.centralizer {ProjGenLinGroup.mk A}) :
    projectiveScalarCharacter A b ^ 2 = 1 := by
  obtain ⟨B, rfl⟩ := projectiveCentralizerProjection_surjective A b
  rw [projectiveScalarCharacter_projection]
  exact scalarDisplacement_square_eq_one A hsquare B

@[expose] def projectiveScalarRangeToRoots {K : Type*} [Field K]
    (A : GeneralLinearGroup (Fin 2) K) (hsquare : ProjGenLinGroup.mk A ^ 2 = 1) :
    (projectiveScalarCharacter A).range →* rootsOfUnity 2 K where
  toFun b := ⟨b.val, by
    obtain ⟨c, hc⟩ := b.property
    rw [mem_rootsOfUnity, ← hc]
    exact projectiveScalarCharacter_square_eq_one A hsquare c⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem projectiveScalarRangeToRoots_injective {K : Type*} [Field K]
    (A : GeneralLinearGroup (Fin 2) K) (hsquare : ProjGenLinGroup.mk A ^ 2 = 1) :
    Function.Injective (projectiveScalarRangeToRoots A hsquare) := by
  intro b c h
  apply Subtype.ext
  exact congrArg (fun x : rootsOfUnity 2 K => x.val) h

theorem projectiveScalarCharacter_kernel_index_le_two {K : Type*} [Field K]
    (A : GeneralLinearGroup (Fin 2) K) (hsquare : ProjGenLinGroup.mk A ^ 2 = 1) :
    (projectiveScalarCharacter A).ker.index ≤ 2 := by
  rw [Subgroup.index_ker]
  exact (Nat.card_le_card_of_injective _ (projectiveScalarRangeToRoots_injective A hsquare)).trans
    (card_rootsOfUnity K 2)

theorem secondDerived_eq_bot_of_abelian_character_kernel
    {G H : Type*} [Group G] [Group H] [IsMulCommutative H]
    (f : G →* H) [IsMulCommutative f.ker] : derivedSeries G 2 = ⊥ := by
  have hcommutator : commutator G ≤ f.ker := Abelianization.commutator_subset_ker f
  apply le_bot_iff.mp
  change ⁅commutator G, commutator G⁆ ≤ ⊥
  exact (Subgroup.commutator_mono hcommutator hcommutator).trans
    (Subgroup.commutator_self_eq_bot_iff.mpr inferInstance).le

theorem pgl_involution_centralizer_structure {K : Type*} [Field K]
    (a : ProjGenLinGroup (Fin 2) K) (hne : a ≠ 1) (hsquare : a ^ 2 = 1) :
    (∃ N : Subgroup (Subgroup.centralizer {a}), N.Normal ∧ IsMulCommutative N ∧
      N.index ≤ 2) ∧ derivedSeries (Subgroup.centralizer {a}) 2 = ⊥ ∧
        Group.IsSolvable (Subgroup.centralizer {a}) := by
  obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective a
  let : IsMulCommutative (projectiveScalarCharacter A).ker :=
    projectiveScalarCharacter_kernel_abelian A hne
  have hderived := secondDerived_eq_bot_of_abelian_character_kernel (projectiveScalarCharacter A)
  exact ⟨⟨(projectiveScalarCharacter A).ker, inferInstance, inferInstance,
      projectiveScalarCharacter_kernel_index_le_two A hsquare⟩,
    hderived, ⟨⟨2, hderived⟩⟩⟩

theorem coordinatePGLAction_injective_all_fields (K : Type*) [Field K] :
    Function.Injective (coordinatePGLAction K) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective g
  have hinf := congrArg (fun c : Equiv.Perm (Omega K) => c none) hg
  have hzero := congrArg (fun c : Equiv.Perm (Omega K) => c (some 0)) hg
  have hone := congrArg (fun c : Equiv.Perm (Omega K) => c (some 1)) hg
  change coordinateGLAction K A none = none at hinf
  change coordinateGLAction K A (some 0) = some 0 at hzero
  change coordinateGLAction K A (some 1) = some 1 at hone
  have hc : A.val 1 0 = 0 := by
    by_contra hc
    rw [coordinateGLAction_infinity K A hc] at hinf
    cases hinf
  have hdet := A.det_ne_zero
  rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
  have hd : A.val 1 1 ≠ 0 := (mul_ne_zero_iff.mp hdet).2
  have hb : A.val 0 1 = 0 := by
    rw [coordinateGLAction_finite K A 0 (by simpa [hc] using hd)] at hzero
    have hquotient : A.val 0 1 / A.val 1 1 = 0 := by simpa [hc] using hzero
    exact (div_eq_zero_iff).mp hquotient |>.resolve_right hd
  have had : A.val 0 0 = A.val 1 1 := by
    rw [coordinateGLAction_finite K A 1 (by simpa [hc] using hd)] at hone
    have hquotient : A.val 0 0 / A.val 1 1 = 1 := by simpa [hc, hb] using hone
    exact (div_eq_one_iff_eq hd).mp hquotient
  apply ProjGenLinGroup.mk_eq_one.mpr
  apply GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
  refine ⟨A.val 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar, hb, hc, had]

@[expose] def pglEquivCoordinateD_all_fields (K : Type*) [Field K] :
    ProjGenLinGroup (Fin 2) K ≃* coordinateD K :=
  (MulEquiv.ofBijective (coordinatePGLAction K).rangeRestrict
    ⟨fun _ _ h => coordinatePGLAction_injective_all_fields K (congrArg Subtype.val h),
      (coordinatePGLAction K).rangeRestrict_surjective⟩).trans
    (MulEquiv.subgroupCongr (coordinatePGLAction_range_eq_D K))

@[expose] def centralizerEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (a : G) : Subgroup.centralizer {a} ≃* Subgroup.centralizer {e a} :=
  { toFun b := ⟨e b.val, Subgroup.mem_centralizer_singleton_iff.mpr (by
      simpa only [map_mul] using congrArg e
        (Subgroup.mem_centralizer_singleton_iff.mp b.property))⟩
    invFun b := ⟨e.symm b.val, Subgroup.mem_centralizer_singleton_iff.mpr (by
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using
        (Subgroup.mem_centralizer_singleton_iff.mp b.property))⟩
    left_inv b := Subtype.ext (e.symm_apply_apply b.val)
    right_inv b := Subtype.ext (e.apply_symm_apply b.val)
    map_mul' _ _ := Subtype.ext (map_mul e _ _) }

@[expose] def coordinateSpecialCentralizerInclusion (K : Type*) [Field K]
    (a : coordinateD K) :
    (Subgroup.centralizer {a.val}).subgroupOf (coordinateG K) →*
      Subgroup.centralizer {a} where
  toFun b := ⟨⟨b.val.val, coordinateG_le_D K b.val.property⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp b.property))⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem coordinate_involution_centralizer_structure (K : Type*) [Field K]
    (_hchar : (2 : K) ≠ 0) (a : coordinateD K) (hne : a ≠ 1) (hsquare : a ^ 2 = 1) :
    (∃ N : Subgroup (Subgroup.centralizer {a}), N.Normal ∧ IsMulCommutative N ∧
      N.index ≤ 2) ∧ derivedSeries (Subgroup.centralizer {a}) 2 = ⊥ ∧
        Group.IsSolvable (Subgroup.centralizer {a}) ∧
          Group.IsSolvable ((Subgroup.centralizer {a.val}).subgroupOf (coordinateG K)) := by
  let e := pglEquivCoordinateD_all_fields K
  let b := e.symm a
  have hbne : b ≠ 1 := by intro h; apply hne; simpa [b] using congrArg e h
  have hbsquare : b ^ 2 = 1 := by
    change e.symm a ^ 2 = 1
    rw [← map_pow, hsquare, map_one]
  let c : Subgroup.centralizer {b} ≃* Subgroup.centralizer {a} :=
    (centralizerEquiv e b).trans
      (MulEquiv.subgroupCongr (by rw [show e b = a from e.apply_symm_apply a]))
  obtain ⟨⟨N, hNnormal, hNabelian, hNindex⟩, hderived, hsolvable⟩ :=
    pgl_involution_centralizer_structure b hbne hbsquare
  let : N.Normal := hNnormal
  let : IsMulCommutative N := hNabelian
  let M := N.map c.toMonoidHom
  have hMnormal : M.Normal := hNnormal.map c.toMonoidHom c.surjective
  have hMabelian : IsMulCommutative M := inferInstance
  have hMindex : M.index ≤ 2 := by
    change (N.map c.toMonoidHom).index ≤ 2
    exact (N.index_map_eq c.surjective (by
      rw [(MonoidHom.ker_eq_bot_iff c.toMonoidHom).mpr c.injective]
      exact bot_le)).le.trans hNindex
  have hderived' : derivedSeries (Subgroup.centralizer {a}) 2 = ⊥ :=
    secondDerived_eq_bot_of_surjective c.toMonoidHom c.surjective hderived
  let : Group.IsSolvable (Subgroup.centralizer {a}) := ⟨⟨2, hderived'⟩⟩
  have hspecial : Group.IsSolvable
      ((Subgroup.centralizer {a.val}).subgroupOf (coordinateG K)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := coordinateSpecialCentralizerInclusion K a) (by
        intro x y hxy
        exact Subtype.ext (Subtype.ext
          (congrArg (fun z : Subgroup.centralizer {a} => z.val.val) hxy)))
  exact ⟨⟨M, hMnormal, hMabelian, hMindex⟩, hderived', inferInstance, hspecial⟩

end CFSG.ComponentClassification.CatalogueBLinearTwo
