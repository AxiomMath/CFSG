module

public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.ThreePlaneData
public import CFSG.LinearAlgebra.ProjectiveLinearKernel
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Semidihedral.GL2Recognition

open Matrix CFSG.Assembly.LowTwoRank

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev ProjPoint : Type :=
  {L : Submodule (ZMod 3) (Fin 3 → ZMod 3) // Module.finrank (ZMod 3) L = 1}

@[expose] def projPointSet (H : Submodule (ZMod 3) (Fin 3 → ZMod 3)) : Set ProjPoint :=
  {L | L.1 ≤ H}

@[expose] def projLineSets : Set (Set ProjPoint) :=
  {S | ∃ H : Submodule (ZMod 3) (Fin 3 → ZMod 3), Module.finrank (ZMod 3) H = 2 ∧
    projPointSet H = S}

@[expose] def projCollineationGroup : Subgroup (Equiv.Perm ProjPoint) where
  carrier := {f | Set.BijOn (fun S => (f : ProjPoint → ProjPoint) '' S) projLineSets projLineSets}
  one_mem' := by
    change Set.BijOn (fun S => ((1 : Equiv.Perm ProjPoint) : ProjPoint → ProjPoint) '' S) _ _
    have : (fun S : Set ProjPoint => ((1 : Equiv.Perm ProjPoint) : ProjPoint → ProjPoint) '' S) =
        id := funext fun S => Set.image_id S
    rw [this]
    exact Set.bijOn_id _
  mul_mem' := by
    intro f g hf hg
    change Set.BijOn (fun S => ((f * g : Equiv.Perm ProjPoint) : ProjPoint → ProjPoint) '' S) _ _
    have : (fun S => ((f * g : Equiv.Perm ProjPoint) : ProjPoint → ProjPoint) '' S) =
        (fun S => (f : ProjPoint → ProjPoint) '' S) ∘
          (fun S => (g : ProjPoint → ProjPoint) '' S) :=
      funext fun S => by rw [Equiv.Perm.coe_mul, Set.image_comp]; rfl
    rw [this]
    exact hf.comp hg
  inv_mem' := by
    intro f hf
    refine Set.BijOn.symm ⟨fun S _ => ?_, fun S _ => ?_⟩ hf
    · simp [Set.image_image]
    · simp [Set.image_image]

theorem projSubspace_map_mul (A B : SpecialLinearGroup (Fin 3) (ZMod 3))
    (N : Submodule (ZMod 3) (Fin 3 → ZMod 3)) :
    N.map (Matrix.toLin' ((A * B : SpecialLinearGroup (Fin 3) (ZMod 3)) :
      Matrix (Fin 3) (Fin 3) (ZMod 3))) =
      (N.map (Matrix.toLin' (B : Matrix (Fin 3) (Fin 3) (ZMod 3)))).map
        (Matrix.toLin' (A : Matrix (Fin 3) (Fin 3) (ZMod 3))) := by
  rw [show ((A * B : SpecialLinearGroup (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
    (A : Matrix (Fin 3) (Fin 3) (ZMod 3)) * B from rfl, Matrix.toLin'_mul, Submodule.map_comp]

theorem projSubspace_map_one (N : Submodule (ZMod 3) (Fin 3 → ZMod 3)) :
    N.map (Matrix.toLin' ((1 : SpecialLinearGroup (Fin 3) (ZMod 3)) :
      Matrix (Fin 3) (Fin 3) (ZMod 3))) = N := by
  rw [show ((1 : SpecialLinearGroup (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = 1 from
    rfl, Matrix.toLin'_one, Submodule.map_id]

@[expose] def projPointMap (A : SpecialLinearGroup (Fin 3) (ZMod 3)) (L : ProjPoint) :
    ProjPoint :=
  ⟨L.1.map (Matrix.toLin' (A : Matrix (Fin 3) (Fin 3) (ZMod 3))), by
    rw [← SpecialLinearGroup.toLin'_to_linearMap, LinearEquiv.finrank_map_eq]
    exact L.2⟩

theorem projPointMap_mul (A B : SpecialLinearGroup (Fin 3) (ZMod 3)) (L : ProjPoint) :
    projPointMap (A * B) L = projPointMap A (projPointMap B L) :=
  Subtype.ext (projSubspace_map_mul A B L.1)

theorem projPointMap_one (L : ProjPoint) : projPointMap 1 L = L :=
  Subtype.ext (projSubspace_map_one L.1)

@[expose] def projPointPerm : SpecialLinearGroup (Fin 3) (ZMod 3) →* Equiv.Perm ProjPoint where
  toFun A :=
    { toFun := projPointMap A
      invFun := projPointMap A⁻¹
      left_inv := fun L => by rw [← projPointMap_mul, inv_mul_cancel, projPointMap_one]
      right_inv := fun L => by rw [← projPointMap_mul, mul_inv_cancel, projPointMap_one] }
  map_one' := Equiv.ext projPointMap_one
  map_mul' A B := Equiv.ext (projPointMap_mul A B)

theorem projPointPerm_apply (A : SpecialLinearGroup (Fin 3) (ZMod 3)) (L : ProjPoint) :
    ((projPointPerm A) L).1 = L.1.map (Matrix.toLin' (A : Matrix (Fin 3) (Fin 3) (ZMod 3))) :=
  rfl

theorem image_projPointSet (A : SpecialLinearGroup (Fin 3) (ZMod 3))
    (H : Submodule (ZMod 3) (Fin 3 → ZMod 3)) :
    (projPointPerm A) '' projPointSet H =
      projPointSet (H.map (Matrix.toLin' (A : Matrix (Fin 3) (Fin 3) (ZMod 3)))) := by
  ext L
  constructor
  · rintro ⟨L', hL', rfl⟩
    exact Submodule.map_mono hL'
  · intro hL
    refine ⟨projPointPerm A⁻¹ L, ?_, ?_⟩
    · show (L.1.map _) ≤ H
      have := Submodule.map_mono (f := Matrix.toLin'
        ((A⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3))) hL
      rwa [← projSubspace_map_mul, inv_mul_cancel, projSubspace_map_one] at this
    · rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]

theorem projPointPerm_mem (A : SpecialLinearGroup (Fin 3) (ZMod 3)) :
    projPointPerm A ∈ projCollineationGroup := by
  have hmaps : ∀ B : SpecialLinearGroup (Fin 3) (ZMod 3),
      Set.MapsTo (fun S => (projPointPerm B : ProjPoint → ProjPoint) '' S)
        projLineSets projLineSets := by
    rintro B S ⟨H, hH, rfl⟩
    refine ⟨H.map (Matrix.toLin' (B : Matrix (Fin 3) (Fin 3) (ZMod 3))), ?_,
      (image_projPointSet B H).symm⟩
    rw [← SpecialLinearGroup.toLin'_to_linearMap, LinearEquiv.finrank_map_eq]
    exact hH
  refine Set.InvOn.bijOn ⟨fun S _ => ?_, fun S _ => ?_⟩ (hmaps A) (hmaps A⁻¹)
  · simp only [Set.image_image, ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Equiv.Perm.one_apply, Set.image_id']
  · simp only [Set.image_image, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Equiv.Perm.one_apply, Set.image_id']

@[expose] def projCollineationHom : SpecialLinearGroup (Fin 3) (ZMod 3) →* projCollineationGroup :=
  projPointPerm.codRestrict projCollineationGroup projPointPerm_mem

theorem projCollineationHom_apply (A : SpecialLinearGroup (Fin 3) (ZMod 3)) (L : ProjPoint) :
    (((projCollineationHom A : Equiv.Perm ProjPoint)) L).1 =
      L.1.map (Matrix.toLin' (A : Matrix (Fin 3) (Fin 3) (ZMod 3))) :=
  rfl

@[expose] def projPointOf (i : Fin 13) : ProjPoint :=
  ⟨ZMod 3 ∙ planeVec i, finrank_span_singleton (planeVec_ne_zero i)⟩

theorem projPointOf_injective : Function.Injective projPointOf := by
  intro i j h
  obtain ⟨c, hc⟩ := Submodule.span_singleton_eq_span_singleton.mp (congrArg Subtype.val h)
  exact eq_of_unit_smul_planeVec i j c hc

theorem projPointOf_surjective : Function.Surjective projPointOf := by
  intro L
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp L.2
  have hvL : (v : Fin 3 → ZMod 3) ≠ 0 := by simpa using hv0
  obtain ⟨i, c, hc⟩ := exists_unit_smul_planeVec (v : Fin 3 → ZMod 3) hvL
  refine ⟨i, Subtype.ext ?_⟩
  have hspan : (ZMod 3 ∙ (v : Fin 3 → ZMod 3)) = L.1 := by
    apply le_antisymm
    · rw [Submodule.span_singleton_le_iff_mem]
      exact v.2
    · intro w hw
      obtain ⟨a, ha⟩ := hv ⟨w, hw⟩
      rw [Submodule.mem_span_singleton]
      exact ⟨a, by simpa using congrArg Subtype.val ha⟩
  rw [← hspan]
  exact Submodule.span_singleton_eq_span_singleton.mpr ⟨c, hc⟩

@[expose] noncomputable def projPointEquiv : Fin 13 ≃ ProjPoint :=
  Equiv.ofBijective projPointOf ⟨projPointOf_injective, projPointOf_surjective⟩

theorem projPointEquiv_apply (i : Fin 13) : projPointEquiv i = projPointOf i := rfl

@[expose] def projForm (w : Fin 3 → ZMod 3) : (Fin 3 → ZMod 3) →ₗ[ZMod 3] ZMod 3 where
  toFun v := planeDot w v
  map_add' u v := by simp only [planeDot, Pi.add_apply]; ring
  map_smul' c v := by simp only [planeDot, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[expose] def projLineSubspace (j : Fin 13) : Submodule (ZMod 3) (Fin 3 → ZMod 3) :=
  LinearMap.ker (projForm (planeVec j))

theorem planeDot_surjective :
    ∀ j : Fin 13, ∀ c : ZMod 3, ∃ v : Fin 3 → ZMod 3, planeDot (planeVec j) v = c := by
  decide

theorem finrank_projLineSubspace (j : Fin 13) :
    Module.finrank (ZMod 3) (projLineSubspace j) = 2 := by
  have hrange : LinearMap.range (projForm (planeVec j)) = ⊤ :=
    LinearMap.range_eq_top.mpr fun c => planeDot_surjective j c
  have := LinearMap.finrank_range_add_finrank_ker (projForm (planeVec j))
  rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at this
  unfold projLineSubspace
  omega

theorem projPointOf_le_iff (i j : Fin 13) :
    (projPointOf i).1 ≤ projLineSubspace j ↔ i ∈ planeLine j := by
  rw [show (projPointOf i).1 = (ZMod 3 ∙ planeVec i) from rfl,
    Submodule.span_singleton_le_iff_mem, projLineSubspace, LinearMap.mem_ker]
  simp only [planeLine, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

theorem planeDot_units_smul (c : (ZMod 3)ˣ) (v x : Fin 3 → ZMod 3) :
    planeDot (c • v) x = (c : ZMod 3) * planeDot v x := by
  simp only [planeDot, Units.smul_def, Pi.smul_apply, smul_eq_mul]
  ring

theorem exists_eq_projLineSubspace (H : Submodule (ZMod 3) (Fin 3 → ZMod 3))
    (hH : Module.finrank (ZMod 3) H = 2) : ∃ j, H = projLineSubspace j := by
  have hlt : H < ⊤ := by
    rw [lt_top_iff_ne_top]
    rintro rfl
    rw [finrank_top, Module.finrank_fin_fun] at hH
    omega
  obtain ⟨f, hf0, hHf⟩ := Submodule.exists_le_ker_of_lt_top H hlt
  have hfw : ∀ x, f x = planeDot (fun i => f (fun k => if i = k then 1 else 0)) x := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ f x, Fin.sum_univ_three]
    simp only [planeDot, smul_eq_mul]
    ring
  have hw0 : (fun i => f (fun k => if i = k then 1 else 0)) ≠ 0 := by
    intro hw
    apply hf0
    refine LinearMap.ext fun x => ?_
    rw [hfw, hw]
    simp [planeDot]
  obtain ⟨j, c, hc⟩ := exists_unit_smul_planeVec _ hw0
  refine ⟨j, Submodule.eq_of_le_of_finrank_eq ?_ (by rw [hH, finrank_projLineSubspace])⟩
  intro x hx
  have hfx : f x = 0 := hHf hx
  rw [hfw, ← hc, planeDot_units_smul] at hfx
  exact (Units.mul_right_eq_zero c).mp hfx

theorem projPointSet_projLineSubspace (j : Fin 13) :
    projPointSet (projLineSubspace j) = projPointOf '' (planeLine j : Set (Fin 13)) := by
  ext L
  obtain ⟨i, rfl⟩ := projPointOf_surjective L
  rw [projPointOf_injective.mem_set_image]
  exact projPointOf_le_iff i j

theorem mem_projLineSets_iff (S : Set ProjPoint) :
    S ∈ projLineSets ↔ ∃ j, projPointOf '' (planeLine j : Set (Fin 13)) = S := by
  constructor
  · rintro ⟨H, hH, rfl⟩
    obtain ⟨j, rfl⟩ := exists_eq_projLineSubspace H hH
    exact ⟨j, (projPointSet_projLineSubspace j).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨projLineSubspace j, finrank_projLineSubspace j, projPointSet_projLineSubspace j⟩

theorem isPlaneCollineation_permCongr {f : Equiv.Perm ProjPoint}
    (hf : f ∈ projCollineationGroup) :
    IsPlaneCollineation (Equiv.permCongrHom projPointEquiv.symm f) := by
  intro j
  have hS : projPointOf '' (planeLine j : Set (Fin 13)) ∈ projLineSets :=
    (mem_projLineSets_iff _).mpr ⟨j, rfl⟩
  obtain ⟨j', hj'⟩ := (mem_projLineSets_iff _).mp (hf.mapsTo hS)
  refine ⟨j', Finset.coe_injective ?_⟩
  rw [Finset.coe_map]
  have h1 : ((Equiv.permCongrHom projPointEquiv.symm f).toEmbedding : Fin 13 → Fin 13) =
      projPointEquiv.symm ∘ f ∘ projPointOf := rfl
  rw [h1, Set.image_comp, Set.image_comp, ← hj', Set.image_image]
  simp [← projPointEquiv_apply]

theorem card_projCollineationGroup_le : Nat.card projCollineationGroup ≤ 5616 := by
  rw [← Subgroup.card_map_of_injective (K := projCollineationGroup)
    (f := (Equiv.permCongrHom projPointEquiv.symm).toMonoidHom)
    (Equiv.permCongrHom projPointEquiv.symm).injective]
  apply card_le_of_forall_isPlaneCollineation
  rintro _ ⟨f, hf, rfl⟩
  exact isPlaneCollineation_permCongr hf

theorem zmod_three_eq_one_of_pow_three_eq_one : ∀ x : ZMod 3, x ^ 3 = 1 → x = 1 := by decide

theorem projPointPerm_injective : Function.Injective projPointPerm := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have hfix : ∀ L : Submodule (ZMod 3) (Fin 3 → ZMod 3), Module.finrank (ZMod 3) L = 1 →
      L.map (Matrix.toLin' ((SpecialLinearGroup.toGL A : GL (Fin 3) (ZMod 3)) :
        Matrix (Fin 3) (Fin 3) (ZMod 3))) = L := fun L hL =>
    congrArg Subtype.val (Equiv.ext_iff.mp hA ⟨L, hL⟩)
  obtain ⟨c, hc⟩ := (CFSG.LinearAlgebra.projective_linear_kernel _).mp hfix
  have hAc : (A : Matrix (Fin 3) (Fin 3) (ZMod 3)) = Matrix.scalar (Fin 3) (c : ZMod 3) := by
    have := congrArg (fun B : GL (Fin 3) (ZMod 3) => (B : Matrix (Fin 3) (Fin 3) (ZMod 3))) hc
    simpa using this
  have hdet := A.2
  rw [hAc, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hdet
  have hc1 := zmod_three_eq_one_of_pow_three_eq_one _ hdet
  ext i k
  rw [hAc, hc1]
  simp [Matrix.one_apply]

theorem card_specialLinearGroup_fin_three_zmod_three :
    Nat.card (SpecialLinearGroup (Fin 3) (ZMod 3)) = 5616 := by
  rw [Matrix.card_SL_field 3, ZMod.card, Fin.prod_univ_three]
  norm_num

theorem projCollineationHom_bijective : Function.Bijective projCollineationHom := by
  have hinj : Function.Injective projCollineationHom := fun A B h =>
    projPointPerm_injective (congrArg Subtype.val h)
  refine hinj.bijective_of_nat_card_le ?_
  rw [card_specialLinearGroup_fin_three_zmod_three]
  exact card_projCollineationGroup_le

@[expose] noncomputable def projCollineationEquiv :
    SpecialLinearGroup (Fin 3) (ZMod 3) ≃* projCollineationGroup :=
  MulEquiv.ofBijective projCollineationHom projCollineationHom_bijective

theorem projCollineationEquiv_apply (A : SpecialLinearGroup (Fin 3) (ZMod 3)) :
    projCollineationEquiv A = projCollineationHom A :=
  rfl

theorem statedSL_three_inf_statedScalars :
    StatedSL 3 (ZMod 3) ⊓ StatedScalars (Fin 3) (ZMod 3) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxSL, c, rfl⟩
  rw [SetLike.mem_coe, statedSL_eq_range_toGL] at hxSL
  obtain ⟨A, hA⟩ := hxSL
  have hdet : ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) (ZMod 3)) :
      Matrix (Fin 3) (Fin 3) (ZMod 3)).det = 1 := by
    rw [← hA]
    exact A.2
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at hdet
  have hc : c = 1 := Units.ext (zmod_three_eq_one_of_pow_three_eq_one _ hdet)
  rw [hc, map_one]
  exact Subgroup.one_mem _

theorem three_element_projective_plane_full_collineation_group :
    Function.Bijective projCollineationHom ∧ Nat.card projCollineationGroup = 5616 ∧
      Nat.card (SpecialLinearGroup (Fin 3) (ZMod 3)) = 5616 ∧
      StatedSL 3 (ZMod 3) ⊓ StatedScalars (Fin 3) (ZMod 3) = ⊥ := by
  refine ⟨projCollineationHom_bijective, ?_, card_specialLinearGroup_fin_three_zmod_three,
    statedSL_three_inf_statedScalars⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ projCollineationHom_bijective),
    card_specialLinearGroup_fin_three_zmod_three]

end CFSG.Semidihedral.GL2Recognition
