module

public import CFSG.LieType.Chevalley.RootWeightStabilizersGrading
public import CFSG.LieType.Chevalley.RootWeightChambers
public import CFSG.LieType.Chevalley.RootWeightFiltrationShifts
public import CFSG.LieType.Chevalley.GraphFixedParabolicCells

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley RootWeightSpace RootWeight
open scoped RealInnerProductSpace Pointwise

theorem adjointGroup_eq_iUnion_top
    (τ : Tag) (K : Type) [Field K] :
    (adjointGroup τ K : Set (ModGL τ K)) = ⋃ w : (⊤ : Subgroup (WeylGroup τ)),
      (borelGroup τ K : Set (ModGL τ K)) * {canonicalRep (coxeterSystem τ) K (w : WeylGroup τ)} *
        (borelGroup τ K : Set (ModGL τ K)) := by
  rw [adjointGroup_eq_iUnion_bruhatCell]
  ext g
  simp only [Set.mem_iUnion]
  exact ⟨fun ⟨w, hw⟩ => ⟨⟨w, trivial⟩, hw⟩, fun ⟨w, hw⟩ => ⟨w, hw⟩⟩

theorem mem_parabolicSubgroup_iff_cells
    (τ : Tag) (K : Type) [Field K] (J : Set (Fin τ.rank))
    (g : ModGL τ K) :
    g ∈ parabolicSubgroup τ K J ↔ ∃ w : (⊤ : Subgroup (WeylGroup τ)),
      (w : WeylGroup τ) ∈ parabolicWeylGroup τ J ∧
      g ∈ (borelGroup τ K : Set (ModGL τ K)) *
        {canonicalRep (coxeterSystem τ) K (w : WeylGroup τ)} *
          (borelGroup τ K : Set (ModGL τ K)) := by
  rw [← SetLike.mem_coe, (standard_parabolic_cells τ K).1 J]
  simp only [Set.mem_iUnion, exists_prop]
  exact ⟨fun ⟨w, hw, hg⟩ => ⟨⟨w, trivial⟩, hw, hg⟩, fun ⟨w, hw, hg⟩ => ⟨w, hw, hg⟩⟩

theorem mem_graphFixedParabolic_iff_cells
    (t : TwistTag) (K : Type) [Field K] (σ : K ≃+* K)
    (J : Set (Fin t.foldedTag.rank)) (g : ModGL t.tag K) :
    g ∈ graphFixedParabolic t K σ.toRingHom J ↔ ∃ w : relWeylTwist t,
      (w : WeylGroup t.tag) ∈ foldedParabolicWeylGroup t J ∧
      g ∈ (graphFixedRootBorel t K σ.toRingHom : Set (ModGL t.tag K)) *
        {canonicalRep (coxeterSystem t.tag) K (w : WeylGroup t.tag)} *
          (graphFixedRootBorel t K σ.toRingHom : Set (ModGL t.tag K)) := by
  rw [← SetLike.mem_coe, (fixed_standard_parabolic_cells t K σ).1 J]
  simp only [Set.mem_iUnion]
  exact ⟨fun ⟨w, hg⟩ => ⟨⟨w, foldedParabolicWeylGroup_le t J w.2⟩, w.2, hg⟩,
    fun ⟨w, hw, hg⟩ => ⟨⟨w, hw⟩, hg⟩⟩

theorem canonicalRep_simple_mem_parabolicSubgroup_iff
    (τ : Tag) (K : Type) [Field K]
    (J : Set (Fin τ.rank)) (i : Fin τ.rank) :
    canonicalRep (coxeterSystem τ) K (simple τ i) ∈ parabolicSubgroup τ K J ↔ i ∈ J := by
  rw [canonicalRep_simple]
  exact (standard_parabolic_cells τ K).2.2.1 J i

namespace RootWeightDatum

variable {K : Type} [Field K] (D : RootWeightDatum K)

theorem labelWeight_eq_proj
    (b : Label D.tag) :
    D.labelWeight b = D.proj (ofLattice b.latticeWeight) := by
  rcases b with j | α
  · simp [labelWeight, Label.latticeWeight]
  · rfl

theorem inner_labelWeight
    (b : Label D.tag) (l : D.space) :
    ⟪D.labelWeight b, l⟫ = latticeGrade (l : RootWeightSpace D.tag) b := by
  rw [labelWeight_eq_proj]
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right l _

theorem filtration_eq_supported
    (l : D.space) (c : ℝ) :
    D.filtration l c = Finsupp.supported K K {b | c ≤ ⟪D.labelWeight b, l⟫} := by
  apply le_antisymm
  · refine weightFiltration_le_iff.2 fun χ _ hc => ?_
    rw [weightSpace_eq_supported]
    refine Finsupp.supported_mono fun b hb => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hb
    simp only [Set.mem_ofPred_eq, hb]
    exact hc
  · rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    exact le_weightFiltration (D.labelWeight_mem_weights b) hb
      ((D.single_mem_weightSpace_iff b _).2 rfl)

theorem single_mem_filtration_iff
    (l : D.space) (c : ℝ) (b : Label D.tag) :
    Finsupp.single b (1 : K) ∈ D.filtration l c ↔ c ≤ ⟪D.labelWeight b, l⟫ := by
  rw [filtration_eq_supported, Finsupp.mem_supported, Finsupp.support_single _ one_ne_zero,
    Finset.coe_singleton, Set.singleton_subset_iff, Set.mem_ofPred_eq]

theorem map_filtration_le_of_labelRaises
    {T : Module.End K (RootModule D.tag K)} {ε : ℝ}
    (l : D.space) (hT : LabelRaises (latticeGrade (l : RootWeightSpace D.tag)) ε T) (c : ℝ) :
    (D.filtration l c).map T ≤ D.filtration l (c + ε) := by
  rw [filtration_eq_supported, filtration_eq_supported]
  refine map_supported_le_of_entries T fun a b hb hab => ?_
  simp only [Set.mem_ofPred_eq, inner_labelWeight] at hb ⊢
  have := hT a b hab
  linarith

theorem eq_of_forall_weights_inner_eq
    {x y : D.space} (h : ∀ χ ∈ D.weights, ⟪χ, x⟫ = ⟪χ, y⟫) :
    x = y := by
  have hspan : Submodule.span ℝ (Set.range fun χ : D.weights => (χ : D.space)) = ⊤ := by
    rw [Subtype.range_coe_subtype]
    exact D.span_weights
  have := eq_zero_of_forall_inner_eq_zero hspan (l := x - y) fun χ => by
    rw [inner_sub_right, h χ χ.2, sub_self]
  exact sub_eq_zero.1 this

@[expose] def filtrationStab
    (l : D.space) : Subgroup (ModGL D.tag K) where
  carrier := {g | ∀ c, (D.filtration l c).map (g : Module.End K (RootModule D.tag K)) =
    D.filtration l c}
  one_mem' c := by
    rw [Units.val_one, Module.End.one_eq_id, Submodule.map_id]
  mul_mem' {g h} hg hh c := by
    rw [Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp, hh c, hg c]
  inv_mem' {g} hg c := by
    conv_lhs => rw [← hg c]
    rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Module.End.one_eq_id, Submodule.map_id]

theorem mem_filtrationStab
    {l : D.space} {g : ModGL D.tag K} :
    g ∈ D.filtrationStab l ↔
      ∀ c, (D.filtration l c).map (g : Module.End K (RootModule D.tag K)) = D.filtration l c :=
  Iff.rfl

theorem labelRaisingSubgroup_le_filtrationStab
    (l : D.space) :
    labelRaisingSubgroup D.tag K (latticeGrade (l : RootWeightSpace D.tag)) 0 le_rfl ≤
      D.filtrationStab l := by
  intro g hg c
  have h1 := D.map_filtration_le_of_labelRaises l (LabelRaises.of_sub_one hg.1) c
  have h2 := D.map_filtration_le_of_labelRaises l (LabelRaises.of_sub_one hg.2) c
  rw [add_zero] at h1 h2
  refine le_antisymm h1 ?_
  calc D.filtration l c = ((D.filtration l c).map (↑g⁻¹ : Module.End K (RootModule D.tag K))).map
        (g : Module.End K (RootModule D.tag K)) := by
        rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← Units.val_mul, mul_inv_cancel,
          Units.val_one, Module.End.one_eq_id, Submodule.map_id]
    _ ≤ (D.filtration l c).map (g : Module.End K (RootModule D.tag K)) := Submodule.map_mono h2

theorem borel_le_borelGroup
    : D.borel ≤ borelGroup D.tag K := by
  cases D with
  | ordinary τ => exact le_rfl
  | fixed t σ hσ => exact inf_le_left.trans inf_le_left

theorem unipotent_le_posUnipotent
    : D.unipotent ≤ posUnipotent D.tag K := by
  cases D with
  | ordinary τ => exact le_rfl
  | fixed t σ hσ => exact inf_le_left

theorem inner_ofLattice_nonneg_of_dominant
    {l : D.space} (hl : l ∈ D.dominant)
    {α : Fin D.tag.rank → ℤ} (hα : IsRoot D.tag α) (hpos : 0 < height α) :
    0 ≤ ⟪ofLattice α, (l : RootWeightSpace D.tag)⟫ := by
  rw [← inner_rootWeight]
  exact D.inner_rootWeight_nonneg hl hα hpos

theorem borel_le_filtrationStab
    {l : D.space} (hl : l ∈ D.dominant) :
    D.borel ≤ D.filtrationStab l :=
  D.borel_le_borelGroup.trans ((borelGroup_le_labelRaisingSubgroup
    fun _ hα hpos => D.inner_ofLattice_nonneg_of_dominant hl hα hpos).trans
    (D.labelRaisingSubgroup_le_filtrationStab l))

theorem exists_pos_le_inner_ofLattice
    {l : D.space} (hl : l ∈ D.openDominant) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ α : Fin D.tag.rank → ℤ, IsRoot D.tag α → 0 < height α →
      ε ≤ ⟪ofLattice α, (l : RootWeightSpace D.tag)⟫ := by
  classical
  set S := ((rootFinset D.tag).filter fun α => 0 < height α).image
    fun α => ⟪ofLattice α, (l : RootWeightSpace D.tag)⟫
  refine ⟨(insert 1 S).min' (Finset.insert_nonempty _ _), ?_, fun α hα hpos => ?_⟩
  · rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨hα, hpos⟩ := Finset.mem_filter.1 hα
      rw [← inner_rootWeight]
      exact D.inner_rootWeight_pos hl (mem_rootFinset.1 hα) hpos
  · exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
      (Finset.mem_filter.2 ⟨mem_rootFinset.2 hα, hpos⟩)))

theorem labelWeight_eq_weylAction
    {w : D.weyl} {a b : Label D.tag}
    (h : a.latticeWeight = (w : WeylGroup D.tag) • b.latticeWeight) :
    D.labelWeight a = D.weylAction w (D.labelWeight b) := by
  rw [labelWeight_eq_proj, labelWeight_eq_proj, h, ← weylIsometry_ofLattice]
  apply Subtype.ext
  rw [coe_proj_weylIsometry D w.2]
  rfl

theorem map_weightSpace_le_of_mapsWeights
    {T : Module.End K (RootModule D.tag K)} {w : D.weyl}
    (hT : MapsWeights T ((w : WeylGroup D.tag) • ·)) (χ : D.space) :
    (D.weightSpace χ).map T ≤ D.weightSpace (D.weylAction w χ) := by
  rw [weightSpace_eq_supported, weightSpace_eq_supported]
  refine map_supported_le_of_entries T fun a b hb hab => ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hb ⊢
  rw [D.labelWeight_eq_weylAction (hT a b hab), hb]

theorem map_weightSpace_rep
    (w : D.weyl) (χ : D.space) :
    (D.weightSpace χ).map (D.rep w : Module.End K (RootModule D.tag K)) =
      D.weightSpace (D.weylAction w χ) := by
  obtain ⟨h1, h2⟩ := mapsWeights_canonicalRep (K := K) (w : WeylGroup D.tag)
  refine le_antisymm (D.map_weightSpace_le_of_mapsWeights h1 χ) ?_
  have h2' : MapsWeights (↑(D.rep w)⁻¹ : Module.End K (RootModule D.tag K))
      (((w⁻¹ : D.weyl) : WeylGroup D.tag) • ·) := by
    rw [Subgroup.coe_inv]
    exact h2
  have h3 := Submodule.map_mono (f := (D.rep w : Module.End K (RootModule D.tag K)))
    (D.map_weightSpace_le_of_mapsWeights h2' (D.weylAction w χ))
  rwa [weylAction_inv_apply, ← Submodule.map_comp, ← Module.End.mul_eq_comp, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, Module.End.one_eq_id, Submodule.map_id] at h3

theorem image_weylAction_weights
    [DecidableEq D.space] (w : D.weyl) :
    D.weights.image (D.weylAction w) = D.weights := by
  refine Finset.Subset.antisymm (fun χ hχ => ?_) (fun χ hχ => ?_)
  · obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_image.1 hχ
    exact D.weylAction_mem_weights w hψ
  · refine Finset.mem_image.2 ⟨D.weylAction w⁻¹ χ, D.weylAction_mem_weights w⁻¹ hχ, ?_⟩
    have h := D.weylAction_inv_apply w⁻¹ χ
    rwa [inv_inv] at h

theorem map_filtration_rep
    (w : D.weyl) (l : D.space) (c : ℝ) :
    (D.filtration l c).map (D.rep w : Module.End K (RootModule D.tag K)) =
      D.filtration (D.weylAction w l) c := by
  classical
  exact map_weightFiltration (D.rep w : Module.End K (RootModule D.tag K)) (D.weylAction w)
    (D.image_weylAction_weights w) (fun χ _ => D.map_weightSpace_rep w χ) l c

theorem rep_mem_filtrationStab_iff
    {l : D.space} (hl : l ∈ D.dominant) (w : D.weyl) :
    D.rep w ∈ D.filtrationStab l ↔ (w : WeylGroup D.tag) ∈ D.parabolicWeyl (D.face l) := by
  rw [← D.weylAction_eq_iff hl w]
  constructor
  · intro h
    have hF : ∀ c, D.filtration (D.weylAction w l) c = D.filtration l c := fun c => by
      rw [← D.map_filtration_rep w l c]
      exact h c
    have hb : ∀ b, ⟪D.labelWeight b, D.weylAction w l⟫ = ⟪D.labelWeight b, l⟫ := fun b => by
      apply le_antisymm
      · have h' : Finsupp.single b (1 : K) ∈
            D.filtration l ⟪D.labelWeight b, D.weylAction w l⟫ := by
          rw [← hF]
          exact (D.single_mem_filtration_iff _ _ b).2 le_rfl
        exact (D.single_mem_filtration_iff _ _ b).1 h'
      · have h' : Finsupp.single b (1 : K) ∈
            D.filtration (D.weylAction w l) ⟪D.labelWeight b, l⟫ := by
          rw [hF]
          exact (D.single_mem_filtration_iff _ _ b).2 le_rfl
        exact (D.single_mem_filtration_iff _ _ b).1 h'
    refine D.eq_of_forall_weights_inner_eq fun χ hχ => ?_
    classical
    rcases Finset.mem_insert.1 hχ with rfl | hχ
    · rw [inner_zero_left, inner_zero_left]
    · obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hχ
      exact hb (.inr ⟨α, mem_rootFinset.1 hα⟩)
  · intro h c
    rw [D.map_filtration_rep w l c, h]

theorem rep_mem_group
    (w : D.weyl) : D.rep w ∈ D.group := by
  cases D with
  | ordinary τ => exact canonicalRep_mem_adjointGroup _ K _
  | fixed t σ hσ => exact canonicalRep_mem_graphFixedRootGroup w.2

theorem group_eq_iUnion :
    (D.group : Set (ModGL D.tag K)) =
    ⋃ w : D.weyl,
      (D.borel : Set (ModGL D.tag K)) * {D.rep w} * (D.borel : Set (ModGL D.tag K)) := by
  cases D with
  | ordinary τ => exact adjointGroup_eq_iUnion_top τ K
  | fixed t σ hσ => exact graphFixedRootGroup_eq_iUnion σ.surjective

theorem mem_parabolic_iff
    (J : Set (Fin D.rank)) (g : ModGL D.tag K) :
    g ∈ D.parabolic J ↔ ∃ w : D.weyl, (w : WeylGroup D.tag) ∈ D.parabolicWeyl J ∧
      g ∈ (D.borel : Set (ModGL D.tag K)) * {D.rep w} * (D.borel : Set (ModGL D.tag K)) := by
  cases D with
  | ordinary τ => exact mem_parabolicSubgroup_iff_cells τ K J g
  | fixed t σ hσ => exact mem_graphFixedParabolic_iff_cells t K σ J g

theorem parabolic_le_group
    (J : Set (Fin D.rank)) : D.parabolic J ≤ D.group := by
  cases D with
  | ordinary τ => exact parabolicSubgroup_le_adjointGroup τ K J
  | fixed t σ hσ => exact graphFixedParabolic_le t K σ.toRingHom J

theorem borel_le_parabolic
    (J : Set (Fin D.rank)) : D.borel ≤ D.parabolic J := by
  cases D with
  | ordinary τ => exact le_sup_left
  | fixed t σ hσ => exact graphFixedRootBorel_le_graphFixedParabolic t K σ.toRingHom J

theorem rep_mem_parabolic
    {J : Set (Fin D.rank)} {w : D.weyl}
    (hw : (w : WeylGroup D.tag) ∈ D.parabolicWeyl J) : D.rep w ∈ D.parabolic J :=
  (D.mem_parabolic_iff J _).2 ⟨w, hw, mem_subgroup_mul_singleton_mul_iff.2
    ⟨1, one_mem _, 1, one_mem _, by rw [one_mul, mul_one]⟩⟩

theorem rep_simpleRefl_mem_parabolic_iff
    (J : Set (Fin D.rank)) (i : Fin D.rank) :
    D.rep (D.simpleRefl i) ∈ D.parabolic J ↔ i ∈ J := by
  cases D with
  | ordinary τ => exact canonicalRep_simple_mem_parabolicSubgroup_iff τ K J i
  | fixed t σ hσ => exact (fixed_standard_parabolic_cells t K σ).2.2.1 J i

theorem mem_group_and_filtrationStab_iff
    {l : D.space} (hl : l ∈ D.dominant)
    (g : ModGL D.tag K) :
    g ∈ D.group ∧ g ∈ D.filtrationStab l ↔ g ∈ D.parabolic (D.face l) := by
  have hB := D.borel_le_filtrationStab hl
  constructor
  · rintro ⟨hg, hgF⟩
    have hg' : g ∈ (D.group : Set (ModGL D.tag K)) := hg
    rw [D.group_eq_iUnion] at hg'
    obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
    obtain ⟨b, hb, b', hb', rfl⟩ := mem_subgroup_mul_singleton_mul_iff.1 hw
    have hn : D.rep w ∈ D.filtrationStab l := by
      have e : D.rep w = b⁻¹ * (b * D.rep w * b') * b'⁻¹ := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem (hB hb)) hgF) (inv_mem (hB hb'))
    have hBP := D.borel_le_parabolic (D.face l)
    exact mul_mem (mul_mem (hBP hb)
      (D.rep_mem_parabolic ((D.rep_mem_filtrationStab_iff hl w).1 hn))) (hBP hb')
  · intro hg
    refine ⟨D.parabolic_le_group _ hg, ?_⟩
    obtain ⟨w, hw, hgw⟩ := (D.mem_parabolic_iff _ g).1 hg
    obtain ⟨b, hb, b', hb', rfl⟩ := mem_subgroup_mul_singleton_mul_iff.1 hgw
    exact mul_mem (mul_mem (hB hb) ((D.rep_mem_filtrationStab_iff hl w).2 hw)) (hB hb')

theorem parabolic_face_lt_group
    {l : D.space} (hl0 : l ≠ 0) :
    D.parabolic (D.face l) < D.group := by
  refine lt_of_le_of_ne (D.parabolic_le_group _) fun h => ?_
  obtain ⟨i, hi⟩ : ∃ i, i ∉ D.face l := by
    by_contra hne
    push Not at hne
    exact D.face_ne_univ hl0 (Set.eq_univ_of_forall hne)
  exact hi ((D.rep_simpleRefl_mem_parabolic_iff _ i).1 (h ▸ D.rep_mem_group _))

open _root_.Classical in
theorem unipotent_minWeightShift_pos
    {l : D.space} (hl : l ∈ D.openDominant)
    {u : ModGL D.tag K} (hu : u ∈ D.unipotent) (hu1 : u ≠ 1) :
    (∀ χ ψ : D.weights, weightBlock D.isInternal_weightSpace
        ((u : Module.End K (RootModule D.tag K)) - 1) χ ψ ≠ 0 → 0 < ⟪(ψ : D.space) - χ, l⟫) ∧
    (shiftSupport D.isInternal_weightSpace
      {(u : Module.End K (RootModule D.tag K)) - 1}).Nonempty ∧
    0 < minWeightShift D.isInternal_weightSpace
      {(u : Module.End K (RootModule D.tag K)) - 1} l := by
  obtain ⟨ε, hε, hm⟩ := D.exists_pos_le_inner_ofLattice hl
  have hR : LabelRaises (latticeGrade (l : RootWeightSpace D.tag)) ε
      ((u : Module.End K (RootModule D.tag K)) - 1) :=
    (posUnipotent_le_labelRaisingSubgroup hε.le hm (D.unipotent_le_posUnipotent hu)).1
  have hA : ({(u : Module.End K (RootModule D.tag K)) - 1} :
      Finset (Module.End K (RootModule D.tag K))).Nonempty := Finset.singleton_nonempty _
  have hA0 : (0 : Module.End K (RootModule D.tag K)) ∉
      ({(u : Module.End K (RootModule D.tag K)) - 1} :
        Finset (Module.End K (RootModule D.tag K))) := by
    rw [Finset.mem_singleton]
    intro h
    exact hu1 (Units.ext (sub_eq_zero.1 h.symm))
  have hle : ε ≤ minWeightShift D.isInternal_weightSpace
      {(u : Module.End K (RootModule D.tag K)) - 1} l :=
    (le_minWeightShift_iff D.isInternal_weightSpace hA hA0 l ε).2 fun a ha c => by
      rw [Finset.mem_singleton.1 ha]
      exact D.map_filtration_le_of_labelRaises l hR c
  have hS := shiftSupport_nonempty D.isInternal_weightSpace hA hA0
  refine ⟨fun χ ψ hχψ => ?_, hS, lt_of_lt_of_le hε hle⟩
  have hmem : (χ, ψ) ∈ shiftSupport D.isInternal_weightSpace
      {(u : Module.End K (RootModule D.tag K)) - 1} :=
    (mem_shiftSupport D.isInternal_weightSpace).2 ⟨_, Finset.mem_singleton_self _,
      (weightBlock_ne_zero_iff D.isInternal_weightSpace).1 hχψ⟩
  have h1 := Finset.inf'_le (fun p : D.weights × D.weights => ⟪(p.2 : D.space) - p.1, l⟫) hmem
  rw [minWeightShift_eq D.isInternal_weightSpace hS] at hle
  exact lt_of_lt_of_le hε (hle.trans h1)

open _root_.Classical in
theorem root_weight_filtration_stabilizers
    (D : RootWeightDatum K) :
    (∀ w : D.weyl, D.rep w ∈ D.group ∧ ∀ χ ∈ D.weights,
      (D.weightSpace χ).map (D.rep w : Module.End K (RootModule D.tag K)) =
        D.weightSpace (D.weylAction w χ)) ∧
    (D.group : Set (ModGL D.tag K)) = ⋃ w : D.weyl,
      (D.borel : Set (ModGL D.tag K)) * {D.rep w} * (D.borel : Set (ModGL D.tag K)) ∧
    (∀ l ∈ D.dominant, ∀ b ∈ D.borel, ∀ c : ℝ,
      (D.filtration l c).map (b : Module.End K (RootModule D.tag K)) = D.filtration l c) ∧
    (∀ l ∈ D.dominant,
      {g : ModGL D.tag K | g ∈ D.group ∧ ∀ c : ℝ,
          (D.filtration l c).map (g : Module.End K (RootModule D.tag K)) = D.filtration l c} =
        (D.parabolic (D.face l) : Set (ModGL D.tag K)) ∧
      (l ≠ 0 → D.parabolic (D.face l) < D.group)) ∧
    (∀ l ∈ D.openDominant, ∀ u ∈ D.unipotent, u ≠ 1 →
      (∀ χ ψ : D.weights, weightBlock D.isInternal_weightSpace
          ((u : Module.End K (RootModule D.tag K)) - 1) χ ψ ≠ 0 →
        0 < ⟪(ψ : D.space) - χ, l⟫) ∧
      (shiftSupport D.isInternal_weightSpace
        {(u : Module.End K (RootModule D.tag K)) - 1}).Nonempty ∧
      0 < minWeightShift D.isInternal_weightSpace
        {(u : Module.End K (RootModule D.tag K)) - 1} l) :=
  ⟨fun w => ⟨D.rep_mem_group w, fun χ _ => D.map_weightSpace_rep w χ⟩, D.group_eq_iUnion,
    fun _ hl _ hb c => D.borel_le_filtrationStab hl hb c,
    fun _ hl => ⟨Set.ext fun g => D.mem_group_and_filtrationStab_iff hl g,
      D.parabolic_face_lt_group⟩,
    fun _ hl _ hu hu1 => D.unipotent_minWeightShift_pos hl hu hu1⟩

end RootWeightDatum

end CFSG.LieType.Chevalley
