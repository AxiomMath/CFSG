module

public import CFSG.LieType.Chevalley.RootWeightChambersFixed
public import CFSG.LieType.Chevalley.RootWeightFiltrationData

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley RootWeightSpace
open scoped RealInnerProductSpace

namespace RootWeightDatum

variable {K : Type} [Field K] (D : RootWeightDatum K)

theorem rank_pos : 0 < D.rank := by
  cases D with
  | ordinary τ => exact τ.rank_pos
  | fixed t σ hσ => exact t.foldedTag.rank_pos

theorem exists_inner_simpleVec_eq
    (j : Fin D.tag.rank) :
    ∃ i : Fin D.rank, ∃ c : ℝ, 0 < c ∧ ∀ x ∈ D.space,
      ⟪D.simpleVec i, x⟫ = c * ⟪ofLattice (Pi.single j 1), x⟫ := by
  cases D with
  | ordinary τ => exact ⟨j, 1, one_pos, fun x _ => (one_mul _).symm⟩
  | fixed t σ hσ =>
    refine ⟨t.orbitIndex j, (t.orbit (t.orbitIndex j)).card,
      by exact_mod_cast card_orbit_pos t _, fun x hx => ?_⟩
    exact inner_orbitSum hx (t.mem_orbit_orbitIndex j)

variable {D}

theorem inner_single_nonneg
    {l : D.space} (hl : l ∈ D.dominant) (j : Fin D.tag.rank) :
    0 ≤ ⟪ofLattice (Pi.single j 1), (l : RootWeightSpace D.tag)⟫ := by
  obtain ⟨i, c, hc, h⟩ := D.exists_inner_simpleVec_eq j
  have hi : 0 ≤ ⟪D.simpleVec i, (l : RootWeightSpace D.tag)⟫ := hl i
  rw [h _ l.2] at hi
  exact (mul_nonneg_iff_of_pos_left hc).1 hi

theorem inner_single_pos
    {l : D.space} (hl : l ∈ D.openDominant) (j : Fin D.tag.rank) :
    0 < ⟪ofLattice (Pi.single j 1), (l : RootWeightSpace D.tag)⟫ := by
  obtain ⟨i, c, hc, h⟩ := D.exists_inner_simpleVec_eq j
  have hi : 0 < ⟪D.simpleVec i, (l : RootWeightSpace D.tag)⟫ := hl i
  rw [h _ l.2] at hi
  exact (mul_pos_iff_of_pos_left hc).1 hi

theorem inner_rootWeight
    (α : Fin D.tag.rank → ℤ) (l : D.space) :
    ⟪D.rootWeight α, l⟫ = ⟪ofLattice α, (l : RootWeightSpace D.tag)⟫ :=
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right l (ofLattice α)

theorem inner_rootWeight_nonneg
    {l : D.space} (hl : l ∈ D.dominant) {α : Fin D.tag.rank → ℤ}
    (hα : IsRoot D.tag α) (hpos : 0 < height α) : 0 ≤ ⟪D.rootWeight α, l⟫ := by
  rw [inner_rootWeight]
  exact inner_ofLattice_nonneg_of_single ((IsRoot.height_pos_iff hα).1 hpos)
    (inner_single_nonneg hl)

theorem inner_rootWeight_pos
    {l : D.space} (hl : l ∈ D.openDominant) {α : Fin D.tag.rank → ℤ}
    (hα : IsRoot D.tag α) (hpos : 0 < height α) : 0 < ⟪D.rootWeight α, l⟫ := by
  rw [inner_rootWeight]
  exact inner_ofLattice_pos_of_single ((IsRoot.height_pos_iff hα).1 hpos) hα.ne_zero
    (inner_single_pos hl)

variable (D)

theorem weylIsometry_simpleReflAmbient
    (i : Fin D.rank) {x : RootWeightSpace D.tag}
    (hx : x ∈ D.space) :
    weylIsometry D.tag (D.simpleReflAmbient i) x =
      x - (2 * ⟪D.simpleVec i, x⟫ / ⟪D.simpleVec i, D.simpleVec i⟫) • D.simpleVec i := by
  cases D with
  | ordinary τ => exact weylIsometry_simple_eq_reflection i x
  | fixed t σ hσ => exact weylIsometry_orbitReflection hx i

theorem inner_simpleVec_self_pos
    (i : Fin D.rank) : 0 < ⟪D.simpleVec i, D.simpleVec i⟫ := by
  cases D with
  | ordinary τ => exact inner_single_self_pos i
  | fixed t σ hσ => exact inner_orbitSum_self_pos i

theorem heightVec_mem_space
    : heightVec D.tag ∈ D.space := by
  cases D with
  | ordinary τ => trivial
  | fixed t σ hσ => exact heightVec_mem_twistFixedSpace

theorem inner_simpleVec_heightVec_pos
    (i : Fin D.rank) :
    0 < ⟪D.simpleVec i, heightVec D.tag⟫ := by
  cases D with
  | ordinary τ => exact inner_single_heightVec_pos i
  | fixed t σ hσ => exact inner_orbitSum_heightVec_pos i

theorem weyl_eq_closure :
    D.weyl = Subgroup.closure (Set.range D.simpleReflAmbient) := by
  cases D with
  | ordinary τ => exact (coxeterSystem τ).subgroup_closure_range_simple.symm
  | fixed t σ hσ => exact (fixed_Weyl_folded_identification t).2.2.1

theorem closure_range_simpleRefl :
    Subgroup.closure (Set.range D.simpleRefl) = ⊤ := by
  apply Subgroup.map_injective D.weyl.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype, ← Set.range_comp]
  exact (D.weyl_eq_closure).symm

theorem parabolicWeyl_eq_closure
    (J : Set (Fin D.rank)) :
    D.parabolicWeyl J = Subgroup.closure (D.simpleReflAmbient '' J) := by
  cases D <;> rfl

theorem parabolicWeyl_le
    (J : Set (Fin D.rank)) : D.parabolicWeyl J ≤ D.weyl := by
  rw [parabolicWeyl_eq_closure, Subgroup.closure_le]
  rintro _ ⟨i, -, rfl⟩
  exact D.simpleReflAmbient_mem i

theorem weylAction_injective :
    Function.Injective D.weylAction := by
  refine (injective_iff_map_eq_one _).2 fun w hw => Subtype.ext ?_
  have hfix : ∀ x ∈ D.space, weylIsometry D.tag w x = x := fun x hx => by
    exact congrArg (fun f => ((f ⟨x, hx⟩ : D.space) : RootWeightSpace D.tag)) hw
  change (w : WeylGroup D.tag) = 1
  cases D with
  | ordinary τ =>
    refine weylIsometry_injective (LinearIsometryEquiv.ext fun x => ?_)
    rw [hfix x trivial, map_one]
    rfl
  | fixed t σ hσ => exact eq_one_of_forall_weylIsometry_eq w.2 hfix

theorem coe_proj_weylIsometry
    {w : WeylGroup D.tag} (hw : w ∈ D.weyl) (x : RootWeightSpace D.tag) :
    (D.proj (weylIsometry D.tag w x) : RootWeightSpace D.tag) =
      weylIsometry D.tag w (D.proj x) := by
  refine coe_orthogonalProjectionOnto_apply_map D.space (weylIsometry D.tag w)
    (fun y hy => D.weylIsometry_mem_space hw hy) (fun y hy => ?_) x
  rw [← LinearIsometryEquiv.coe_inv, ← map_inv]
  exact D.weylIsometry_mem_space (inv_mem hw) hy

theorem weylAction_rootWeight
    (w : D.weyl) (α : Fin D.tag.rank → ℤ) :
    D.weylAction w (D.rootWeight α) = D.rootWeight ((w : WeylGroup D.tag) • α) := by
  apply Subtype.ext
  change weylIsometry D.tag w (D.proj (ofLattice α)) =
    (D.proj (ofLattice ((w : WeylGroup D.tag) • α)) : _)
  rw [← weylIsometry_ofLattice, D.coe_proj_weylIsometry w.2]

theorem weylAction_inv_apply
    (w : D.weyl) (x : D.space) :
    D.weylAction w⁻¹ (D.weylAction w x) = x := by
  rw [map_inv, LinearIsometryEquiv.coe_inv, LinearIsometryEquiv.symm_apply_apply]

theorem weylAction_mem_weights
    (w : D.weyl) {χ : D.space} (hχ : χ ∈ D.weights) :
    D.weylAction w χ ∈ D.weights := by
  classical
  rcases Finset.mem_insert.1 hχ with rfl | hχ
  · rw [map_zero]
    exact Finset.mem_insert_self _ _
  · obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hχ
    rw [weylAction_rootWeight]
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
      (mem_rootFinset.2 (IsRoot.smul (mem_rootFinset.1 hα) _)))

theorem weylAction_mem_weights_iff
    (w : D.weyl) (χ : D.space) :
    D.weylAction w χ ∈ D.weights ↔ χ ∈ D.weights := by
  refine ⟨fun h => ?_, D.weylAction_mem_weights w⟩
  have := D.weylAction_mem_weights w⁻¹ h
  rwa [weylAction_inv_apply] at this

theorem span_weights
    : Submodule.span ℝ (D.weights : Set D.space) = ⊤ := by
  classical
  refine eq_top_iff.2 fun x _ => ?_
  have hx : D.proj (x : RootWeightSpace D.tag) = x :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x
  rw [← hx, ← (simpleBasis D.tag).sum_repr (x : RootWeightSpace D.tag), map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  rw [simpleBasis_apply]
  exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (mem_rootFinset.2 (isRoot_single _ j)))

theorem simpleRoot_ne_zero
    (i : Fin D.rank) : D.simpleRoot i ≠ 0 := fun h => by
  have := D.inner_simpleVec_self_pos i
  have h' : D.simpleVec i = 0 := congrArg Subtype.val h
  rw [h', inner_zero_left] at this
  exact lt_irrefl 0 this

theorem finrank_pos :
    0 < Module.finrank ℝ D.space :=
  Module.finrank_pos_iff_exists_ne_zero.2 ⟨_, D.simpleRoot_ne_zero ⟨0, D.rank_pos⟩⟩

theorem linearIndependent_simpleRoot :
    LinearIndependent ℝ D.simpleRoot := by
  cases D with
  | ordinary τ => exact linearIndependent_single_top
  | fixed t σ hσ => exact linearIndependent_orbitSum

theorem span_simpleRoot :
    Submodule.span ℝ (Set.range D.simpleRoot) = ⊤ := by
  cases D with
  | ordinary τ => exact span_single_top
  | fixed t σ hσ => exact span_orbitSum

theorem exists_weylAction_mem_dominant
    (x : D.space) :
    ∃ w : D.weyl, ∃ l ∈ D.dominant, D.weylAction w l = x := by
  obtain ⟨u, hu, hpos⟩ := exists_forall_inner_nonneg (weylIsometry D.tag) D.weyl D.space
    (fun w hw y hy => D.weylIsometry_mem_space hw hy) D.simpleVec D.simpleReflAmbient
    D.simpleReflAmbient_mem (fun i y hy => D.weylIsometry_simpleReflAmbient i hy)
    D.inner_simpleVec_self_pos D.inner_simpleVec_heightVec_pos x.2
  exact ⟨⟨u, hu⟩⁻¹, D.weylAction ⟨u, hu⟩ x, fun i => hpos i, D.weylAction_inv_apply _ x⟩

theorem weylIsometry_simpleReflAmbient_fix
    {l : D.space} (i : Fin D.rank)
    (hi : ⟪D.simpleVec i, (l : RootWeightSpace D.tag)⟫ = 0) :
    weylIsometry D.tag (D.simpleReflAmbient i) l = l := by
  rw [D.weylIsometry_simpleReflAmbient i l.2, hi, mul_zero, zero_div, zero_smul, sub_zero]

theorem face_eq
    (l : D.space) :
    D.face l = {i | ⟪D.simpleVec i, (l : RootWeightSpace D.tag)⟫ = 0} :=
  rfl

theorem weylAction_eq_iff
    {l : D.space} (hl : l ∈ D.dominant) (w : D.weyl) :
    D.weylAction w l = l ↔ (w : WeylGroup D.tag) ∈ D.parabolicWeyl (D.face l) := by
  have hcoe : D.weylAction w l = l ↔
      weylIsometry D.tag w (l : RootWeightSpace D.tag) = l := Subtype.ext_iff
  rw [hcoe, parabolicWeyl_eq_closure, face_eq]
  refine ⟨fun hfix => ?_, fun hmem => fix_of_mem_closure (weylIsometry D.tag)
    (fun i hi => D.weylIsometry_simpleReflAmbient_fix i hi) hmem⟩
  have hl' : ∀ i, 0 ≤ ⟪D.simpleVec i, (l : RootWeightSpace D.tag)⟫ := fun i => hl i
  have hexch : ∃ len : WeylGroup D.tag → ℕ, ∀ v ∈ D.weyl, v ≠ 1 → ∃ i,
      len (v * D.simpleReflAmbient i) < len v ∧
        ⟪weylIsometry D.tag v (D.simpleVec i), (l : RootWeightSpace D.tag)⟫ ≤ 0 := by
    cases D with
    | ordinary τ =>
      refine ⟨(coxeterSystem τ).length, fun v _ h1 => ?_⟩
      obtain ⟨i, hlen, hneg⟩ := exists_length_mul_simple_lt h1
      exact ⟨i, hlen, inner_weylIsometry_single_nonpos hneg (inner_single_nonneg hl)⟩
    | fixed t σ hσ =>
      refine ⟨t.orbitLength, fun v hv h1 => ?_⟩
      obtain ⟨a, hlen, hneg⟩ := exists_orbitLength_mul_lt hv h1
      exact ⟨a, hlen, inner_weylIsometry_orbitSum_nonpos hneg (inner_single_nonneg hl)⟩
  obtain ⟨len, hexch⟩ := hexch
  exact mem_closure_of_fix (weylIsometry D.tag) D.weyl D.simpleReflAmbient_mem hl'
    (fun i hi => D.weylIsometry_simpleReflAmbient_fix i hi) len hexch w w.2 hfix

theorem face_ne_univ
    {l : D.space} (hl : l ≠ 0) : D.face l ≠ Set.univ := fun h =>
  hl (eq_zero_of_forall_inner_eq_zero D.span_simpleRoot fun i => by
    have : i ∈ D.face l := h ▸ Set.mem_univ i
    exact this)

theorem root_weight_chambers_and_faces
    (D : RootWeightDatum K) :
    FiniteDimensional ℝ D.space ∧ 0 < Module.finrank ℝ D.space ∧
    (D.weights : Set D.space).Finite ∧ Submodule.span ℝ (D.weights : Set D.space) = ⊤ ∧
    Finite D.weyl ∧ Function.Injective D.weylAction ∧
    (∀ (w : D.weyl) (χ : D.space), D.weylAction w χ ∈ D.weights ↔ χ ∈ D.weights) ∧
    (∃ b : Module.Basis (Fin D.rank) ℝ D.space, ⇑b = D.simpleRoot) ∧
    (∀ (i : Fin D.rank) (x : D.space), D.weylAction (D.simpleRefl i) x =
      x - (2 * ⟪D.simpleRoot i, x⟫ / ⟪D.simpleRoot i, D.simpleRoot i⟫) • D.simpleRoot i) ∧
    Subgroup.closure (Set.range D.simpleRefl) = ⊤ ∧
    D.weyl = Subgroup.closure (Set.range D.simpleReflAmbient) ∧
    (∃ h : RootWeightSpace D.tag, (∀ j, ⟪ofLattice (Pi.single j 1), h⟫ = 1) ∧
      (∀ h' : RootWeightSpace D.tag, (∀ j, ⟪ofLattice (Pi.single j 1), h'⟫ = 1) → h' = h) ∧
      ∃ hE : h ∈ D.space, (⟨h, hE⟩ : D.space) ∈ D.openDominant ∧
        ∀ α, IsRoot D.tag α → 0 < height α → 0 < ⟪D.rootWeight α, ⟨h, hE⟩⟫) ∧
    (∀ x : D.space, ∃ w : D.weyl, ∃ l ∈ D.dominant, D.weylAction w l = x) ∧
    (∀ J : Set (Fin D.rank), D.parabolicWeyl J = Subgroup.closure (D.simpleReflAmbient '' J) ∧
      D.parabolicWeyl J ≤ D.weyl) ∧
    (∀ l ∈ D.dominant, ∀ w : D.weyl,
      D.weylAction w l = l ↔ (w : WeylGroup D.tag) ∈ D.parabolicWeyl (D.face l)) ∧
    (∀ l ∈ D.dominant, l ≠ 0 → D.face l ≠ Set.univ) ∧
    (∀ l ∈ D.dominant, ∀ α, IsRoot D.tag α → 0 < height α → 0 ≤ ⟪D.rootWeight α, l⟫) ∧
    (∀ l ∈ D.openDominant, ∀ α, IsRoot D.tag α → 0 < height α → 0 < ⟪D.rootWeight α, l⟫) := by
  have hhE := D.heightVec_mem_space
  have hhD : (⟨heightVec D.tag, hhE⟩ : D.space) ∈ D.openDominant := fun i =>
    D.inner_simpleVec_heightVec_pos i
  refine ⟨inferInstance, D.finrank_pos, D.weights.finite_toSet, D.span_weights, inferInstance,
    D.weylAction_injective, D.weylAction_mem_weights_iff,
    ⟨Module.Basis.mk D.linearIndependent_simpleRoot D.span_simpleRoot.ge,
      funext fun i => Module.Basis.mk_apply _ _ i⟩,
    fun i x => Subtype.ext (D.weylIsometry_simpleReflAmbient i x.2), D.closure_range_simpleRefl,
    D.weyl_eq_closure,
    ⟨heightVec D.tag, inner_single_heightVec, fun h' hh' => eq_heightVec_iff.1 hh', hhE, hhD,
      fun α hα hpos => inner_rootWeight_pos hhD hα hpos⟩,
    D.exists_weylAction_mem_dominant, fun J => ⟨D.parabolicWeyl_eq_closure J, D.parabolicWeyl_le J⟩,
    fun l hl w => D.weylAction_eq_iff hl w, fun l _ hl0 => D.face_ne_univ hl0,
    fun l hl α hα hpos => inner_rootWeight_nonneg hl hα hpos,
    fun l hl α hα hpos => inner_rootWeight_pos hl hα hpos⟩

end RootWeightDatum

end CFSG.LieType.Chevalley
