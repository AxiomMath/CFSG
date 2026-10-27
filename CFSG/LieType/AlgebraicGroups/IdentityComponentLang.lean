module

public import CFSG.LieType.AlgebraicGroups.SupportedNativeLang
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
import CFSG.LieType.AlgebraicGroups.ToralCentralizerComponent

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint WithConv
  Topology

open scoped CFSG.ConvolutionPoints

set_option linter.unusedSectionVars false

section PointSets

variable {k : Type} [Field k] {A : Type} [CommRing A] [Algebra k A]

private theorem isPointConstructible_of_isPointClosed [Algebra.FiniteType k A]
    {S : Set (A →ₐ[k] k)} (h : IsPointClosed k S) : IsPointConstructible k S := by
  obtain ⟨Zc, hZc, rfl⟩ := h
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  refine ⟨Zc, ?_, rfl⟩
  rw [← Topology.isConstructible_compl]
  exact (TopologicalSpace.NoetherianSpace.isCompact Zcᶜ).isConstructible hZc.isOpen_compl

private theorem isPointClosed_iInter {ι : Sort*} {S : ι → Set (A →ₐ[k] k)}
    (h : ∀ i, IsPointClosed k (S i)) : IsPointClosed k (⋂ i, S i) := by
  choose Zc hZc hS using h
  exact ⟨⋂ i, Zc i, isClosed_iInter hZc, by rw [Set.preimage_iInter]; exact Set.iInter_congr hS⟩

end PointSets

variable {τ : Tag} {k : Type} [Field k]

theorem mem_transportPoints_modGLPoint {S : Set (ModGL τ k)} {y : GLCoord k (Label τ) →ₐ[k] k} :
    y ∈ transportPoints (modGLPoint τ k) S ↔ (modGLPoint τ k).symm (toConv y) ∈ S := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    simpa only [toConv_ofConv, MulEquiv.symm_apply_apply] using hg
  · intro h
    exact ⟨_, h, by simp only [MulEquiv.apply_symm_apply, ofConv_toConv]⟩

private theorem bijective_ofConv_modGLPoint :
    Function.Bijective fun g : ModGL τ k => (modGLPoint τ k g).ofConv :=
  ⟨fun _ _ h => (modGLPoint τ k).injective (WithConv.ext h), fun y =>
    ⟨(modGLPoint τ k).symm (toConv y), by simp only [MulEquiv.apply_symm_apply, ofConv_toConv]⟩⟩

theorem isPointClosed_iff_isClosed_image (S : Set (ModGL τ k)) :
    IsPointClosed k (transportPoints (modGLPoint τ k) S) ↔ IsClosed (modGLZariski τ k '' S) := by
  rw [transportPoints_eq_image_modGLZariski]
  exact (SeminaireExp3.isClosed_iff_isPointClosed SeminaireExp3.ZariskiGL.isInducing_pt).symm

theorem isPointIrreducible_iff_isIrreducible_image (S : Set (ModGL τ k)) :
    IsPointIrreducible k (transportPoints (modGLPoint τ k) S) ↔
      IsIrreducible (modGLZariski τ k '' S) := by
  rw [transportPoints_eq_image_modGLZariski]
  exact (SeminaireExp3.isIrreducible_iff_isPointIrreducible
    SeminaireExp3.ZariskiGL.isInducing_pt).symm

@[expose] def closedIdentityComponent (Z : Subgroup (ModGL τ k)) : Subgroup (ModGL τ k) :=
  (SeminaireExp3.ZariskiGL.identityComponent (Z.map (modGLZariski τ k).toMonoidHom)).comap
    (modGLZariski τ k).toMonoidHom

theorem mem_closedIdentityComponent {Z : Subgroup (ModGL τ k)} {g : ModGL τ k} :
    g ∈ closedIdentityComponent Z ↔
      modGLZariski τ k g ∈
        SeminaireExp3.ZariskiGL.identityComponent (Z.map (modGLZariski τ k).toMonoidHom) :=
  Iff.rfl

theorem image_modGLZariski_closedIdentityComponent (Z : Subgroup (ModGL τ k)) :
    modGLZariski τ k '' (closedIdentityComponent Z : Set (ModGL τ k)) =
      (SeminaireExp3.ZariskiGL.identityComponent (Z.map (modGLZariski τ k).toMonoidHom) :
        Set (SeminaireExp3.ZariskiGL (Label τ) k)) := by
  rw [closedIdentityComponent, Subgroup.coe_comap, MulEquiv.coe_toMonoidHom,
    Set.image_preimage_eq _ (modGLZariski τ k).surjective]

theorem closedIdentityComponent_le (Z : Subgroup (ModGL τ k)) : closedIdentityComponent Z ≤ Z := by
  intro g hg
  have h := SeminaireExp3.ZariskiGL.identityComponent_le _ (mem_closedIdentityComponent.1 hg)
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at h
  exact h

theorem isPointClosed_closedIdentityComponent {Z : Subgroup (ModGL τ k)}
    (hZ : IsPointClosed k (transportPoints (modGLPoint τ k) (Z : Set (ModGL τ k)))) :
    IsPointClosed k
      (transportPoints (modGLPoint τ k) (closedIdentityComponent Z : Set (ModGL τ k))) := by
  rw [isPointClosed_iff_isClosed_image] at hZ ⊢
  rw [image_modGLZariski_closedIdentityComponent]
  refine SeminaireExp3.ZariskiGL.isClosed_identityComponent ?_
  rw [Subgroup.coe_map, MulEquiv.coe_toMonoidHom]
  exact hZ

theorem isPointIrreducible_closedIdentityComponent (Z : Subgroup (ModGL τ k)) :
    IsPointIrreducible k
      (transportPoints (modGLPoint τ k) (closedIdentityComponent Z : Set (ModGL τ k))) := by
  rw [isPointIrreducible_iff_isIrreducible_image, image_modGLZariski_closedIdentityComponent]
  exact SeminaireExp3.ZariskiGL.isIrreducible_identityComponent _

theorem closedIdentityComponent_subgroupOf (Z : Subgroup (ModGL τ k)) :
    (closedIdentityComponent Z).subgroupOf Z =
      ((SeminaireExp3.ZariskiGL.identityComponent
        (Z.map (modGLZariski τ k).toMonoidHom)).subgroupOf
          (Z.map (modGLZariski τ k).toMonoidHom)).comap
        ((modGLZariski τ k).toMonoidHom.subgroupMap Z) :=
  Subgroup.ext fun _ => Iff.rfl

instance closedIdentityComponent_normal (Z : Subgroup (ModGL τ k)) :
    ((closedIdentityComponent Z).subgroupOf Z).Normal := by
  rw [closedIdentityComponent_subgroupOf]
  exact Subgroup.Normal.comap inferInstance _

instance closedIdentityComponent_finiteIndex (Z : Subgroup (ModGL τ k)) :
    ((closedIdentityComponent Z).subgroupOf Z).FiniteIndex := by
  rw [closedIdentityComponent_subgroupOf]
  infer_instance

theorem subset_closedIdentityComponent {Z : Subgroup (ModGL τ k)} {X : Set (ModGL τ k)}
    (hXZ : X ⊆ Z) (h1 : (1 : ModGL τ k) ∈ X)
    (hX : IsPointIrreducible k (transportPoints (modGLPoint τ k) X)) :
    X ⊆ closedIdentityComponent Z := by
  rw [isPointIrreducible_iff_isIrreducible_image] at hX
  obtain ⟨Z', hZ'⟩ : ∃ Z', Z' = Z.map (modGLZariski τ k).toMonoidHom := ⟨_, rfl⟩
  have hmem : ∀ x ∈ X, modGLZariski τ k x ∈ Z' := fun x hx => by
    rw [hZ', Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    exact hXZ hx
  obtain ⟨Y, hY⟩ : ∃ Y : Set Z', Y = Subtype.val ⁻¹' (modGLZariski τ k '' X) := ⟨_, rfl⟩
  have hYX : Subtype.val '' Y = modGLZariski τ k '' X := by
    rw [hY]
    refine Set.image_preimage_eq_of_subset ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨_, hmem x hx⟩, rfl⟩
  have hYirr : IsIrreducible Y := by
    refine (SeminaireExp3.isIrreducible_image_iff_of_isInducing
      IsEmbedding.subtypeVal.toIsInducing).1 ?_
    rw [hYX]
    exact hX
  have hY1 : (1 : Z') ∈ Y := by
    rw [hY, Set.mem_preimage]
    exact ⟨1, h1, map_one _⟩
  have hsub := SeminaireExp3.subset_identityComponent hYirr hY1
  intro x hx
  rw [SetLike.mem_coe, mem_closedIdentityComponent, ← hZ']
  refine ⟨⟨_, hmem x hx⟩, hsub ?_, rfl⟩
  rw [hY, Set.mem_preimage]
  exact ⟨x, hx, rfl⟩

theorem conj_mem_closedIdentityComponent {Z : Subgroup (ModGL τ k)}
    {n g : ModGL τ k} (hn : n ∈ Subgroup.normalizer (Z : Set (ModGL τ k)))
    (hg : g ∈ closedIdentityComponent Z) :
    n * g * n⁻¹ ∈ closedIdentityComponent Z := by
  refine subset_closedIdentityComponent
    (X := (fun x => n * x * n⁻¹) '' (closedIdentityComponent Z : Set (ModGL τ k))) ?_
    ⟨1, one_mem _, by group⟩ ?_ ⟨g, hg, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hn x).mp (closedIdentityComponent_le Z hx)
  · have h := isPointIrreducible_closedIdentityComponent Z
    unfold IsPointIrreducible at h ⊢
    have hc : ∀ x : ModGL τ k,
        (modGLPoint τ k (n * x * n⁻¹)).ofConv =
          (modGLPoint τ k x).ofConv.comp (innerCo (modGLPoint τ k n)) := by
      intro x
      apply WithConv.toConv_injective
      rw [toConv_ofConv, point_comp_innerCo, ← map_inv, ← map_mul, ← map_mul]
    have hpts : pointSpec '' transportPoints (modGLPoint τ k)
        ((fun x => n * x * n⁻¹) '' (closedIdentityComponent Z : Set (ModGL τ k))) =
        PrimeSpectrum.comap (innerCo (modGLPoint τ k n) :
          GLCoord k (Label τ) →+* GLCoord k (Label τ)) ''
          (pointSpec '' transportPoints (modGLPoint τ k)
            (closedIdentityComponent Z : Set (ModGL τ k))) := by
      simp only [transportPoints, Set.image_image, comap_pointSpec, hc]
    rw [hpts]
    exact h.image _ (PrimeSpectrum.continuous_comap _).continuousOn

theorem normalizer_le_normalizer_closedIdentityComponent (Z : Subgroup (ModGL τ k)) :
    Subgroup.normalizer (Z : Set (ModGL τ k)) ≤
      Subgroup.normalizer (closedIdentityComponent Z : Set (ModGL τ k)) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨conj_mem_closedIdentityComponent hn, fun hg => ?_⟩
  have h := conj_mem_closedIdentityComponent (Subgroup.inv_mem _ hn) hg
  simpa only [inv_inv, inv_mul_cancel_left, mul_inv_cancel_right, mul_assoc, inv_mul_cancel, mul_one] using h

theorem closedIdentityComponent_eq_self {Z : Subgroup (ModGL τ k)}
    (hZ : IsPointIrreducible k (transportPoints (modGLPoint τ k) (Z : Set (ModGL τ k)))) :
    closedIdentityComponent Z = Z :=
  le_antisymm (closedIdentityComponent_le Z)
    (subset_closedIdentityComponent subset_rfl Z.one_mem hZ)

@[expose] def IsPolynomialCurve (c : k → ModGL τ k) : Prop :=
  ∃ P : Matrix (Label τ) (Label τ) (Polynomial k),
    ∀ t a b, endMatrix τ (c t : Module.End k (RootModule τ k)) a b = (P a b).eval t

theorem IsPolynomialCurve.mul {c₁ c₂ : k → ModGL τ k} (h₁ : IsPolynomialCurve c₁)
    (h₂ : IsPolynomialCurve c₂) : IsPolynomialCurve fun t => c₁ t * c₂ t := by
  obtain ⟨P₁, hP₁⟩ := h₁
  obtain ⟨P₂, hP₂⟩ := h₂
  have hmul : ∀ A B : Module.End k (RootModule τ k),
      endMatrix τ (A * B) = endMatrix τ A * endMatrix τ B := fun A B => by
    unfold endMatrix
    rw [map_mul]
  refine ⟨P₁ * P₂, fun t a b => ?_⟩
  beta_reduce
  rw [Units.val_mul, hmul, Matrix.mul_apply, Matrix.mul_apply, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, hP₁, hP₂]

theorem isPolynomialCurve_of_baseChange {c : k → ModGL τ k}
    (A : Module.End (Polynomial k) (RootModule τ (Polynomial k)))
    (hA : ∀ t, BaseChange (Polynomial.evalRingHom t) A (c t : Module.End k (RootModule τ k))) :
    IsPolynomialCurve c := by
  refine ⟨fun a b => A (Finsupp.single b 1) a, fun t a b => ?_⟩
  rw [endMatrix_apply, ← hA t b, Finsupp.mapRange_apply, Polynomial.coe_evalRingHom]

section Words


theorem isPolynomialCurve_wordUnit (w : List (Letter τ × Polynomial k)) :
    IsPolynomialCurve fun t => wordUnit τ k (mapWord (Polynomial.evalRingHom t) w) :=
  isPolynomialCurve_of_baseChange _ fun t => baseChange_wordUnit (Polynomial.evalRingHom t) w

theorem isPolynomialCurve_pinnedX (α : Fin τ.rank → ℤ) (f : Polynomial k) :
    IsPolynomialCurve fun t => pinnedX τ k α (f.eval t) := by
  have h := isPolynomialCurve_wordUnit (τ := τ) (pinnedWord τ (Polynomial k) α f)
  simp only [mapWord_pinnedWord, wordUnit_pinnedWord, Polynomial.coe_evalRingHom] at h
  exact h

end Words

section Families

variable [IsAlgClosed k]

theorem mem_closedIdentityComponent_of_matrix {Z : Subgroup (ModGL τ k)} {D : Type} [CommRing D]
    [Algebra k D] [Algebra.FiniteType k D] [IsDomain D] (P : Matrix (Label τ) (Label τ) D)
    {c : (D →ₐ[k] k) → ModGL τ k}
    (hc : ∀ z a b, endMatrix τ (c z : Module.End k (RootModule τ k)) a b = z (P a b))
    (hcZ : ∀ z, c z ∈ Z) {z₀ : D →ₐ[k] k} (hz₀ : c z₀ = 1) (z : D →ₐ[k] k) :
    c z ∈ closedIdentityComponent Z := by
  have hmat : ∀ z : D →ₐ[k] k,
      endMatrix τ (c z : Module.End k (RootModule τ k)) = z.mapMatrix P := fun z => by
    ext a b
    rw [hc, AlgHom.mapMatrix_apply, Matrix.map_apply]
  have hdet : IsUnit P.det := by
    refine SeminaireExp3.isUnit_of_forall_algHom_ne_zero (k := k) fun z hz => ?_
    have h := det_endMatrix_mul_inv (c z)
    rw [hmat z, ← AlgHom.map_det, hz, zero_mul] at h
    exact zero_ne_one h
  obtain ⟨ψ, hψ⟩ : ∃ ψ : GLCoord k (Label τ) →ₐ[k] D,
      ψ = GLCoord.lift k (Label τ) P (↑hdet.unit⁻¹) hdet.mul_val_inv := ⟨_, rfl⟩
  have hpt : ∀ z : D →ₐ[k] k, z.comp ψ = (modGLPoint τ k (c z)).ofConv := fun z => by
    refine GLCoord.algHom_ext_of_entries fun a b => ?_
    rw [AlgHom.comp_apply, hψ, GLCoord.lift_glEntry, modGLPoint_apply_glEntry, ← endMatrix_apply,
      hc]
  refine subset_closedIdentityComponent (X := Set.range c) ?_ ⟨z₀, hz₀⟩ ?_ ⟨z, rfl⟩
  · rintro _ ⟨z, rfl⟩
    exact hcZ z
  · have h : transportPoints (modGLPoint τ k) (Set.range c) =
        Set.range fun z : D →ₐ[k] k => z.comp ψ := by
      rw [transportPoints, ← Set.range_comp]
      exact congrArg Set.range (funext fun z => (hpt z).symm)
    rw [h]
    exact isPointIrreducible_range_of_isDomain ψ

theorem mem_closedIdentityComponent_of_isPolynomialCurve {Z : Subgroup (ModGL τ k)}
    {c : k → ModGL τ k} (hc : IsPolynomialCurve c) (hcZ : ∀ t, c t ∈ Z) {t₀ : k} (h1 : c t₀ = 1)
    (t : k) : c t ∈ closedIdentityComponent Z := by
  obtain ⟨P, hP⟩ := hc
  have hz : ∀ (z : Polynomial k →ₐ[k] k) (f : Polynomial k), z f = f.eval (z Polynomial.X) := by
    intro z f
    rw [← Polynomial.coe_aeval_eq_eval, Polynomial.aeval_algHom_apply,
      Polynomial.aeval_X_left_apply]
  have h := mem_closedIdentityComponent_of_matrix (Z := Z) P
    (c := fun z => c (z Polynomial.X))
    (fun z a b => by
      show endMatrix τ (c (z Polynomial.X) : Module.End k (RootModule τ k)) a b = z (P a b)
      rw [hP]
      exact (hz z (P a b)).symm)
    (fun z => hcZ _) (z₀ := Polynomial.aeval t₀)
    (by
      show c (Polynomial.aeval t₀ Polynomial.X) = 1
      rw [Polynomial.aeval_X]
      exact h1)
    (Polynomial.aeval t)
  rwa [Polynomial.aeval_X] at h

end Families

section Lang

variable (p : ℕ) [Fact p.Prime] [CharP k p]

theorem ofConv_modGLPoint_frobTwistGL (e : ℕ) (Q g : ModGL τ k) :
    (modGLPoint τ k (frobTwistGL τ k p e Q g)).ofConv =
      (modGLPoint τ k g).ofConv.comp (frobTwistCoGL p e Q) := by
  have h := modGLPoint_symm_comp_frobTwistCoGL p e Q (modGLPoint τ k g).ofConv
  rw [toConv_ofConv, MulEquiv.symm_apply_apply] at h
  rw [← h, MulEquiv.apply_symm_apply, ofConv_toConv]

theorem frobTwistGL_mem_closedIdentityComponent (e : ℕ) (Q : ModGL τ k)
    {Z : Subgroup (ModGL τ k)} (hS : ∀ g ∈ Z, frobTwistGL τ k p e Q g ∈ Z) {g : ModGL τ k}
    (hg : g ∈ closedIdentityComponent Z) :
    frobTwistGL τ k p e Q g ∈ closedIdentityComponent Z := by
  refine subset_closedIdentityComponent
    (X := frobTwistGL τ k p e Q '' (closedIdentityComponent Z : Set (ModGL τ k))) ?_
    ⟨1, one_mem _, map_one _⟩ ?_ ⟨g, hg, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hS x (closedIdentityComponent_le Z hx)
  · have h := isPointIrreducible_closedIdentityComponent Z
    unfold IsPointIrreducible at h ⊢
    have hpts : pointSpec '' transportPoints (modGLPoint τ k)
        (frobTwistGL τ k p e Q '' (closedIdentityComponent Z : Set (ModGL τ k))) =
        PrimeSpectrum.comap (frobTwistCoGL p e Q : GLCoord k (Label τ) →+* GLCoord k (Label τ)) ''
          (pointSpec '' transportPoints (modGLPoint τ k)
            (closedIdentityComponent Z : Set (ModGL τ k))) := by
      simp only [transportPoints, Set.image_image, comap_pointSpec, ofConv_modGLPoint_frobTwistGL]
    rw [hpts]
    exact h.image _ (PrimeSpectrum.continuous_comap _).continuousOn

theorem exists_inv_mul_frobTwistGL_closedIdentityComponent [IsAlgClosed k]
    {Z : Subgroup (ModGL τ k)}
    (hZ : IsPointClosed k (transportPoints (modGLPoint τ k) (Z : Set (ModGL τ k))))
    {e : ℕ} (he : 1 ≤ e) (Q : ModGL τ k) (hS : ∀ g ∈ Z, frobTwistGL τ k p e Q g ∈ Z) :
    ∀ c ∈ closedIdentityComponent Z, ∃ ζ ∈ closedIdentityComponent Z,
      ζ⁻¹ * frobTwistGL τ k p e Q ζ = c := by
  obtain ⟨-, hconn, -⟩ := isConnectedAlgebraicSubgroup_map (modGLPoint τ k)
    (closedIdentityComponent Z)
    (isPointConstructible_of_isPointClosed (isPointClosed_closedIdentityComponent hZ))
    (isPointIrreducible_closedIdentityComponent Z)
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction p hconn he Q
    fun g hg => frobTwistGL_mem_closedIdentityComponent p e Q hS hg
  exact hlang

end Lang

theorem isPointClosed_iInf {ι : Sort*} {H : ι → Subgroup (ModGL τ k)}
    (h : ∀ i, IsPointClosed k (transportPoints (modGLPoint τ k) (H i : Set (ModGL τ k)))) :
    IsPointClosed k
      (transportPoints (modGLPoint τ k) ((⨅ i, H i : Subgroup (ModGL τ k)) : Set (ModGL τ k))) := by
  rw [Subgroup.coe_iInf, transportPoints, Set.image_iInter bijective_ofConv_modGLPoint]
  exact isPointClosed_iInter h

theorem isPointClosed_inf {H K : Subgroup (ModGL τ k)}
    (hH : IsPointClosed k (transportPoints (modGLPoint τ k) (H : Set (ModGL τ k))))
    (hK : IsPointClosed k (transportPoints (modGLPoint τ k) (K : Set (ModGL τ k)))) :
    IsPointClosed k
      (transportPoints (modGLPoint τ k) ((H ⊓ K : Subgroup (ModGL τ k)) : Set (ModGL τ k))) := by
  rw [Subgroup.coe_inf, transportPoints, Set.image_inter bijective_ofConv_modGLPoint.1]
  exact hH.inter hK

theorem comp_innerCo_modGLPoint_eq_iff {A : ModGL τ k} {y : GLCoord k (Label τ) →ₐ[k] k} :
    y.comp (innerCo (modGLPoint τ k A)) = y ↔
      (modGLPoint τ k).symm (toConv y) ∈ Subgroup.centralizer {A} := by
  have hc : ∀ g : ModGL τ k, g ∈ Subgroup.centralizer {A} ↔ A * g * A⁻¹ = g := fun g => by
    rw [Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul, eq_comm]
  rw [hc]
  have h := point_comp_innerCo (toConv y) (modGLPoint τ k A)
  rw [ofConv_toConv] at h
  constructor
  · intro hy
    apply (modGLPoint τ k).injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← h, hy]
  · intro hA
    apply WithConv.toConv_injective
    rw [h]
    have e1 := congrArg (modGLPoint τ k) hA
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at e1
    exact e1

theorem transportPoints_centralizer (T : Set (ModGL τ k)) :
    transportPoints (modGLPoint τ k) (Subgroup.centralizer T : Set (ModGL τ k)) =
      ⋂ A : T, {y | y.comp (innerCo (modGLPoint τ k A)) = y} := by
  ext y
  rw [mem_transportPoints_modGLPoint, Set.mem_iInter, SetLike.mem_coe,
    Subgroup.mem_centralizer_iff]
  refine ⟨fun h A => ?_, fun h A hA => ?_⟩
  · rw [Set.mem_setOf_eq, comp_innerCo_modGLPoint_eq_iff, Subgroup.mem_centralizer_singleton_iff]
    exact (h A A.2).symm
  · have h' := h ⟨A, hA⟩
    rw [Set.mem_setOf_eq, comp_innerCo_modGLPoint_eq_iff,
      Subgroup.mem_centralizer_singleton_iff] at h'
    exact h'.symm

theorem isPointClosed_centralizer (T : Set (ModGL τ k)) :
    IsPointClosed k
      (transportPoints (modGLPoint τ k) (Subgroup.centralizer T : Set (ModGL τ k))) := by
  rw [transportPoints_centralizer]
  exact isPointClosed_iInter fun A => isPointClosed_setOf_comp_eq _

end CFSG.LieType.AlgebraicGroups

end
