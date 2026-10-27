module

public import CFSG.LieType.Chevalley.RootWeightFiltration
public import CFSG.LieType.Chevalley.RootWeightFiltrationSpace
public import CFSG.LieType.Chevalley.GraphFixedStandardParabolic
public import CFSG.LieType.Chevalley.StandardParabolic

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley RootWeightSpace RootWeight
open scoped RealInnerProductSpace

section Restrict

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℝ M] {G : Type*} [Group G]

@[expose] def restrictIsometry (ρ : G →* (M ≃ₗᵢ[ℝ] M)) (F : Submodule ℝ M)
    (hF : ∀ g x, x ∈ F → ρ g x ∈ F) : G →* (F ≃ₗᵢ[ℝ] F) where
  toFun g :=
    { toFun := fun x => ⟨ρ g (x : M), hF g x x.2⟩
      invFun := fun x => ⟨ρ g⁻¹ (x : M), hF g⁻¹ x x.2⟩
      map_add' := fun x y => Subtype.ext (map_add (ρ g) (x : M) y)
      map_smul' := fun c x => Subtype.ext (map_smul (ρ g) c (x : M))
      left_inv := fun x => Subtype.ext (by
        change (ρ g⁻¹ * ρ g) (x : M) = x
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl)
      right_inv := fun x => Subtype.ext (by
        change (ρ g * ρ g⁻¹) (x : M) = x
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl)
      norm_map' := fun x => (ρ g).norm_map x }
  map_one' := LinearIsometryEquiv.ext fun x => Subtype.ext (by
    change ρ 1 (x : M) = x
    rw [map_one]
    rfl)
  map_mul' g g' := LinearIsometryEquiv.ext fun x => Subtype.ext (by
    change ρ (g * g') (x : M) = ρ g (ρ g' x)
    rw [map_mul]
    rfl)

theorem coe_restrictIsometry_apply (ρ : G →* (M ≃ₗᵢ[ℝ] M)) (F : Submodule ℝ M)
    (hF : ∀ g x, x ∈ F → ρ g x ∈ F) (g : G) (x : F) :
    (restrictIsometry ρ F hF g x : M) = ρ g x :=
  rfl

end Restrict

inductive RootWeightDatum (K : Type) [Field K] : Type
  | ordinary (τ : Tag)
  | fixed (t : TwistTag) (σ : K ≃+* K) (hσ : σ ^ t.order = 1)

namespace RootWeightDatum

variable {K : Type} [Field K]

@[expose] def tag : RootWeightDatum K → Tag
  | ordinary τ => τ
  | fixed t _ _ => t.tag

@[expose] def group
    : (D : RootWeightDatum K) → Subgroup (ModGL D.tag K)
  | ordinary τ => adjointGroup τ K
  | fixed t σ _ => graphFixedRootGroup t K σ.toRingHom

@[expose] def borel
    : (D : RootWeightDatum K) → Subgroup (ModGL D.tag K)
  | ordinary τ => borelGroup τ K
  | fixed t σ _ => graphFixedRootBorel t K σ.toRingHom

@[expose] def unipotent
    : (D : RootWeightDatum K) → Subgroup (ModGL D.tag K)
  | ordinary τ => posUnipotent τ K
  | fixed t σ _ => graphFixedPosUnipotent t K σ.toRingHom

@[expose] def space
    : (D : RootWeightDatum K) → Submodule ℝ (RootWeightSpace D.tag)
  | ordinary _ => ⊤
  | fixed t _ _ => twistFixedSpace t

@[expose] def weyl :
    (D : RootWeightDatum K) → Subgroup (WeylGroup D.tag)
  | ordinary _ => ⊤
  | fixed t _ _ => relWeylTwist t

@[expose] def rank : RootWeightDatum K → ℕ
  | ordinary τ => τ.rank
  | fixed t _ _ => t.foldedTag.rank

@[expose] def simpleVec
    : (D : RootWeightDatum K) → Fin D.rank → RootWeightSpace D.tag
  | ordinary _, i => ofLattice (Pi.single i 1)
  | fixed t _ _, i => ofLattice (t.orbitSum i)

@[expose] def simpleReflAmbient
    : (D : RootWeightDatum K) → Fin D.rank → WeylGroup D.tag
  | ordinary τ, i => simple τ i
  | fixed t _ _, i => t.orbitReflection i

@[expose] def parabolicWeyl
    : (D : RootWeightDatum K) → Set (Fin D.rank) →
    Subgroup (WeylGroup D.tag)
  | ordinary τ, J => parabolicWeylGroup τ J
  | fixed t _ _, J => foldedParabolicWeylGroup t J

@[expose] def parabolic
    : (D : RootWeightDatum K) → Set (Fin D.rank) → Subgroup (ModGL D.tag K)
  | ordinary τ, J => parabolicSubgroup τ K J
  | fixed t σ _, J => graphFixedParabolic t K σ.toRingHom J

variable (D : RootWeightDatum K)

theorem simpleVec_mem
    (i : Fin D.rank) : D.simpleVec i ∈ D.space := by
  cases D with
  | ordinary τ => trivial
  | fixed t σ hσ => exact ofLattice_mem_twistFixedSpace (t.orbitSum_mem_fixedLattice i)

theorem simpleReflAmbient_mem
    (i : Fin D.rank) : D.simpleReflAmbient i ∈ D.weyl := by
  cases D with
  | ordinary τ => trivial
  | fixed t σ hσ => exact t.orbitReflection_mem i

@[expose] def simpleRoot
    (i : Fin D.rank) : D.space :=
  ⟨D.simpleVec i, D.simpleVec_mem i⟩

@[expose] def simpleRefl
    (i : Fin D.rank) : D.weyl :=
  ⟨D.simpleReflAmbient i, D.simpleReflAmbient_mem i⟩

theorem weylIsometry_mem_space
    {w : WeylGroup D.tag} (hw : w ∈ D.weyl)
    {x : RootWeightSpace D.tag} (hx : x ∈ D.space) : weylIsometry D.tag w x ∈ D.space := by
  cases D with
  | ordinary τ => trivial
  | fixed t σ hσ => exact weylIsometry_mem_twistFixedSpace hw hx

@[expose] def weylAction
    : D.weyl →* (D.space ≃ₗᵢ[ℝ] D.space) :=
  restrictIsometry ((weylIsometry D.tag).comp D.weyl.subtype) D.space fun w _ hx =>
    D.weylIsometry_mem_space w.2 hx

@[expose] def proj
    : RootWeightSpace D.tag →L[ℝ] D.space :=
  D.space.orthogonalProjectionOnto

@[expose] def rootWeight
    (α : Fin D.tag.rank → ℤ) : D.space :=
  D.proj (ofLattice α)

open _root_.Classical in
@[expose] def weights
    : Finset D.space :=
  insert 0 ((rootFinset D.tag).image D.rootWeight)

@[expose] def weightSpace
    (χ : D.space) : Submodule K (RootModule D.tag K) :=
  Submodule.span K ({x | ∃ α, IsRoot D.tag α ∧ D.rootWeight α = χ ∧ x = rootVec D.tag K α} ∪
    {x | χ = 0 ∧ ∃ j, x = hVec D.tag K j})

@[expose] def rep
    (w : D.weyl) : ModGL D.tag K :=
  canonicalRep (coxeterSystem D.tag) K (w : WeylGroup D.tag)

@[expose] def filtration
    (l : D.space) (c : ℝ) : Submodule K (RootModule D.tag K) :=
  weightFiltration D.weights D.weightSpace l c

@[expose] def dominant :
    Set D.space :=
  {l | ∀ i, 0 ≤ ⟪D.simpleRoot i, l⟫}

@[expose] def openDominant :
    Set D.space :=
  {l | ∀ i, 0 < ⟪D.simpleRoot i, l⟫}

@[expose] def face
    (l : D.space) : Set (Fin D.rank) :=
  {i | ⟪D.simpleRoot i, l⟫ = 0}

@[expose] def labelWeight
    : Label D.tag → D.space
  | .inl _ => 0
  | .inr α => D.rootWeight α.1

theorem labelWeight_mem_weights
    (l : Label D.tag) : D.labelWeight l ∈ D.weights := by
  classical
  rcases l with j | ⟨α, hα⟩
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (mem_rootFinset.2 hα))

theorem weightSpace_eq_supported
    (χ : D.space) :
    D.weightSpace χ = Finsupp.supported K K (D.labelWeight ⁻¹' {χ}) := by
  rw [Finsupp.supported_eq_span_single, weightSpace]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_image, Set.mem_preimage,
    Set.mem_singleton_iff]
  constructor
  · rintro (⟨α, hα, hχ, rfl⟩ | ⟨rfl, j, rfl⟩)
    · exact ⟨.inr ⟨α, hα⟩, hχ, (rootVec_eq_single_of_isRoot hα).symm⟩
    · exact ⟨.inl j, rfl, rfl⟩
  · rintro ⟨j | ⟨α, hα⟩, hl, rfl⟩
    · exact Or.inr ⟨hl.symm, j, rfl⟩
    · exact Or.inl ⟨α, hα, hl, (rootVec_eq_single_of_isRoot hα).symm⟩

theorem single_mem_weightSpace_iff
    (l : Label D.tag) (χ : D.space) :
    Finsupp.single l (1 : K) ∈ D.weightSpace χ ↔ D.labelWeight l = χ := by
  rw [weightSpace_eq_supported, Finsupp.mem_supported, Finsupp.support_single _ one_ne_zero,
    Finset.coe_singleton, Set.singleton_subset_iff, Set.mem_preimage, Set.mem_singleton_iff]

open _root_.Classical in
theorem isInternal_weightSpace :
    DirectSum.IsInternal fun χ : D.weights => D.weightSpace χ := by
  classical
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · rw [iSupIndep_def]
    intro χ
    simp only [weightSpace_eq_supported]
    refine (Finsupp.disjoint_supported_supported
      (disjoint_compl_right (a := D.labelWeight ⁻¹' {(χ : D.space)}))).mono_right ?_
    refine iSup₂_le fun ψ hψ => Finsupp.supported_mono fun l hl => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hl
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, hl]
    exact fun h => hψ (Subtype.ext h)
  · simp only [weightSpace_eq_supported]
    rw [← Finsupp.supported_iUnion, eq_top_iff, ← Finsupp.supported_univ]
    refine Finsupp.supported_mono fun l _ => Set.mem_iUnion.2
      ⟨⟨D.labelWeight l, D.labelWeight_mem_weights l⟩, rfl⟩

open _root_.Classical in
theorem root_weight_filtration_data
    (D : RootWeightDatum K) :
    (∀ x y : RootWeightSpace D.tag,
      ⟪x, y⟫ = ∑ i, ∑ j, x i * (D.tag.symmetrizedCartan i j : ℝ) * y j) ∧
    (∀ x y : D.space, ⟪x, y⟫ = ⟪(x : RootWeightSpace D.tag), (y : RootWeightSpace D.tag)⟫) ∧
    (∀ l : D.space, ‖l‖ ^ 2 = ⟪l, l⟫) ∧
    (∀ w ∈ D.weyl, ∀ x ∈ D.space, weylIsometry D.tag w x ∈ D.space) ∧
    (∀ (w : D.weyl) (x : D.space),
      (D.weylAction w x : RootWeightSpace D.tag) = weylIsometry D.tag w x) ∧
    (∀ (x : RootWeightSpace D.tag), ∀ y ∈ D.space, ⟪x - D.proj x, y⟫ = 0) ∧
    (∀ x : D.space, D.proj x = x) ∧
    (∀ χ : D.space, χ ∈ D.weights ↔ χ = 0 ∨ ∃ α, IsRoot D.tag α ∧ D.proj (ofLattice α) = χ) ∧
    (∀ (j : Fin D.tag.rank) (χ : D.space), hVec D.tag K j ∈ D.weightSpace χ ↔ χ = 0) ∧
    (∀ (α : Fin D.tag.rank → ℤ), IsRoot D.tag α → ∀ χ : D.space,
      rootVec D.tag K α ∈ D.weightSpace χ ↔ D.proj (ofLattice α) = χ) ∧
    (∀ l : Label D.tag, D.labelWeight l ∈ D.weights) ∧
    DirectSum.IsInternal (fun χ : D.weights => D.weightSpace χ) ∧
    (∀ (w : D.weyl) (ω : List (Fin D.tag.rank)), (coxeterSystem D.tag).IsReduced ω →
      (coxeterSystem D.tag).wordProd ω = w →
      D.rep w = (ω.map fun i => weylElt D.tag K i 1).prod) := by
  classical
  refine ⟨fun x y => inner_eq_sum x y, fun x y => rfl, fun l => (real_inner_self_eq_norm_sq l).symm,
    fun w hw x hx => D.weylIsometry_mem_space hw hx, fun w x => rfl, fun x y hy => ?_,
    fun x => Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x, fun χ => ?_,
    fun j χ => ?_, fun α hα χ => ?_, D.labelWeight_mem_weights, D.isInternal_weightSpace,
    fun w ω hω hw => ?_⟩
  · exact Submodule.starProjection_inner_eq_zero x y hy
  · simp only [weights, Finset.mem_insert, Finset.mem_image, mem_rootFinset, rootWeight]
  · have := D.single_mem_weightSpace_iff (.inl j) χ
    rw [labelWeight] at this
    rw [hVec, this, eq_comm]
  · have := D.single_mem_weightSpace_iff (.inr ⟨α, hα⟩) χ
    rw [labelWeight] at this
    rw [rootVec_eq_single_of_isRoot hα, this]
    rfl
  · rw [rep, ← hw]
    exact canonicalRep_wordProd hω

end RootWeightDatum

end CFSG.LieType.Chevalley
