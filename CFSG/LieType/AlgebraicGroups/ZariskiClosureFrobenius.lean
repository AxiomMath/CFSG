module

public import CFSG.LieType.AlgebraicGroups.IdentityComponentLang

import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv Topology

open scoped CFSG.ConvolutionPoints

variable {τ : Tag} {k : Type} [Field k]

private theorem isClosed_setOf_pt_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : GLCoord k ι) (c : k) :
    IsClosed {g : SeminaireExp3.ZariskiGL ι k | SeminaireExp3.ZariskiGL.pt g a = c} := by
  have h : {g : SeminaireExp3.ZariskiGL ι k | SeminaireExp3.ZariskiGL.pt g a = c} =
      {g | SeminaireExp3.ZariskiGL.pt g (a - algebraMap k (GLCoord k ι) c) = 0} := by
    ext g
    simp only [Set.mem_setOf_eq, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_eq_zero]
  rw [h]
  exact (SeminaireExp3.isClosed_iff_exists (e := SeminaireExp3.ZariskiGL.pt)
    SeminaireExp3.ZariskiGL.isInducing_pt).2
    ⟨{a - algebraMap k (GLCoord k ι) c}, by ext g; simp⟩

private theorem isPointClosed_singleton {A : Type} [CommRing A] [Algebra k A]
    (y : A →ₐ[k] k) : IsPointClosed k ({y} : Set (A →ₐ[k] k)) := by
  refine ⟨{pointSpec y}, ?_, ?_⟩
  · rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    exact RingHom.ker_isMaximal_of_surjective y fun c => ⟨algebraMap k A c, y.commutes c⟩
  · ext z
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun h => h ▸ rfl, fun h => pointSpec_injective h⟩

private theorem isPointClosed_transportPoints_one :
    IsPointClosed k (transportPoints (modGLPoint τ k) ({1} : Set (ModGL τ k))) := by
  rw [transportPoints, Set.image_singleton]
  exact isPointClosed_singleton _

private theorem isPointClosed_preimage_of_continuous {f : ModGL τ k → ModGL τ k}
    {F : SeminaireExp3.ZariskiGL (Label τ) k → SeminaireExp3.ZariskiGL (Label τ) k}
    (hF : Continuous F) (hFf : ∀ g, F (modGLZariski τ k g) = modGLZariski τ k (f g))
    {S : Set (ModGL τ k)}
    (hS : IsPointClosed k (transportPoints (modGLPoint τ k) S)) :
    IsPointClosed k (transportPoints (modGLPoint τ k) (f ⁻¹' S)) := by
  rw [isPointClosed_iff_isClosed_image] at hS ⊢
  have hset : modGLZariski τ k '' (f ⁻¹' S) = F ⁻¹' (modGLZariski τ k '' S) := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [Set.mem_preimage, hFf g]
      exact ⟨f g, hg, rfl⟩
    · intro hz
      have hz' : modGLZariski τ k (f ((modGLZariski τ k).symm z)) ∈
          modGLZariski τ k '' S := by
        rw [← hFf ((modGLZariski τ k).symm z), MulEquiv.apply_symm_apply]
        exact hz
      obtain ⟨x, hx, hxz⟩ := hz'
      have hfx : f ((modGLZariski τ k).symm z) = x := (modGLZariski τ k).injective hxz.symm
      refine ⟨(modGLZariski τ k).symm z, ?_, (modGLZariski τ k).apply_symm_apply z⟩
      rw [Set.mem_preimage, hfx]
      exact hx
  rw [hset]
  exact hS.preimage hF

private theorem closure_mul_mem {G : Type} [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] (P : Subgroup G) {x y : G}
    (hx : x ∈ closure (P : Set G)) (hy : y ∈ closure (P : Set G)) :
    x * y ∈ closure (P : Set G) := by
  have hPy : (P : Set G) ⊆ (fun z => z * y) ⁻¹' closure (P : Set G) := by
    intro p hp
    have hcl : IsClosed ((fun z => p * z) ⁻¹' closure (P : Set G)) :=
      isClosed_closure.preimage (SeparatelyContinuousMul.continuous_const_mul (a := p))
    have hP : (P : Set G) ⊆ (fun z => p * z) ⁻¹' closure (P : Set G) := fun q hq =>
      subset_closure (P.mul_mem hp hq)
    exact hcl.closure_subset_iff.2 hP hy
  have hcl : IsClosed ((fun z => z * y) ⁻¹' closure (P : Set G)) :=
    isClosed_closure.preimage (SeparatelyContinuousMul.continuous_mul_const (a := y))
  exact hcl.closure_subset_iff.2 hPy hx

private theorem closure_inv_mem {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G]
    (P : Subgroup G) {x : G} (hx : x ∈ closure (P : Set G)) :
    x⁻¹ ∈ closure (P : Set G) := by
  have hcl : IsClosed ((fun z => z⁻¹) ⁻¹' closure (P : Set G)) :=
    isClosed_closure.preimage continuous_inv
  have hP : (P : Set G) ⊆ (fun z => z⁻¹) ⁻¹' closure (P : Set G) := fun p hp =>
    subset_closure (P.inv_mem hp)
  exact hcl.closure_subset_iff.2 hP hx

private theorem end_apply_eq_sum (g : Module.End k (RootModule τ k)) (v : RootModule τ k)
    (a : Label τ) :
    g v a = ∑ b : Label τ, v b * g (Finsupp.single b 1) a := by
  have hv : v = ∑ b : Label τ, v b • Finsupp.single b (1 : k) := by
    rw [← Finsupp.sum_single v, Finsupp.sum_fintype _ _ (fun _ => by simp)]
    ext b
    simp
  conv_lhs => rw [hv]
  rw [map_sum]
  simp only [map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]

private theorem linearMap_apply_eq_sum (f : RootModule τ k →ₗ[k] k) (v : RootModule τ k) :
    f v = ∑ a : Label τ, f (Finsupp.single a 1) * v a := by
  have hv : v = ∑ a : Label τ, v a • Finsupp.single a (1 : k) := by
    rw [← Finsupp.sum_single v, Finsupp.sum_fintype _ _ (fun _ => by simp)]
    ext b
    simp
  conv_lhs => rw [hv]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

private theorem linearMap_apply_eq_sum_entries (f : RootModule τ k →ₗ[k] k)
    (g : Module.End k (RootModule τ k)) (v : RootModule τ k) :
    f (g v) = ∑ a : Label τ, ∑ b : Label τ,
      f (Finsupp.single a 1) * v b * g (Finsupp.single b 1) a := by
  rw [linearMap_apply_eq_sum, Finset.sum_congr rfl]
  intro a _
  rw [end_apply_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

private theorem toConv_comp_convMul_aux {A : Type} [CommRing A] [HopfAlgebra k A]
    (h : A →ₐ[k] k) (f g : WithConv (A →ₐ[k] A)) :
    toConv (h.comp ((f * g).ofConv)) =
      toConv (h.comp f.ofConv) * toConv (h.comp g.ofConv) := by
  rw [AlgHom.comp_convMul_distrib, toConv_ofConv]

private theorem toConv_comp_convPow_aux {A : Type} [CommRing A] [HopfAlgebra k A]
    (h : A →ₐ[k] k) (f : WithConv (A →ₐ[k] A)) (m : ℕ) :
    toConv (h.comp ((f ^ m).ofConv)) = toConv (h.comp f.ofConv) ^ m := by
  induction m with
  | zero =>
    ext x
    simp [AlgHom.convOne_def]
  | succ m ih =>
    rw [pow_succ, pow_succ, toConv_comp_convMul_aux, ih]

private abbrev conjCo (c : SeminaireExp3.ZariskiGL (Label τ) k) :
    GLCoord k (Label τ) →ₐ[k] GLCoord k (Label τ) :=
  (toConv (HopfAlgebra.antipodeAlgHom k (GLCoord k (Label τ))) *
    constPoint (SeminaireExp3.ZariskiGL.point c) *
    toConv (AlgHom.id k (GLCoord k (Label τ)))).ofConv

private theorem pt_inv_mul_mul (c z : SeminaireExp3.ZariskiGL (Label τ) k) :
    SeminaireExp3.ZariskiGL.pt (z⁻¹ * c * z) =
      (SeminaireExp3.ZariskiGL.pt z).comp (conjCo c) := by
  apply toConv_injective
  have key : toConv ((SeminaireExp3.ZariskiGL.pt z).comp (conjCo c)) =
      toConv ((SeminaireExp3.ZariskiGL.pt z).comp
          (HopfAlgebra.antipodeAlgHom k (GLCoord k (Label τ)))) *
        toConv (SeminaireExp3.ZariskiGL.pt c) * toConv (SeminaireExp3.ZariskiGL.pt z) := by
    have h1 : toConv ((SeminaireExp3.ZariskiGL.pt z).comp
          ((toConv (HopfAlgebra.antipodeAlgHom k (GLCoord k (Label τ))) *
            constPoint (SeminaireExp3.ZariskiGL.point c)).ofConv)) =
        toConv ((SeminaireExp3.ZariskiGL.pt z).comp
            (toConv (HopfAlgebra.antipodeAlgHom k (GLCoord k (Label τ)))).ofConv) *
          toConv ((SeminaireExp3.ZariskiGL.pt z).comp
            (constPoint (SeminaireExp3.ZariskiGL.point c)).ofConv) :=
      toConv_comp_convMul_aux _ _ _
    have h2 : toConv ((SeminaireExp3.ZariskiGL.pt z).comp
          (toConv (HopfAlgebra.antipodeAlgHom k (GLCoord k (Label τ)))).ofConv) =
        toConv ((SeminaireExp3.ZariskiGL.pt z).comp
          (HopfAlgebra.antipodeAlgHom k (GLCoord k (Label τ)))) := by
      rw [ofConv_toConv]
    have h3 : toConv ((SeminaireExp3.ZariskiGL.pt z).comp
          (constPoint (SeminaireExp3.ZariskiGL.point c)).ofConv) =
        toConv (SeminaireExp3.ZariskiGL.pt c) := by
      rw [point_comp_constPoint]
      rfl
    have h4 : toConv ((SeminaireExp3.ZariskiGL.pt z).comp
          (toConv (AlgHom.id k (GLCoord k (Label τ)))).ofConv) =
        toConv (SeminaireExp3.ZariskiGL.pt z) := by
      rw [ofConv_toConv, AlgHom.comp_id]
    rw [conjCo, toConv_comp_convMul_aux, h1, h2, h3, h4]
  rw [key]
  calc
    toConv (SeminaireExp3.ZariskiGL.pt (z⁻¹ * c * z)) =
        toConv (SeminaireExp3.ZariskiGL.pt (z⁻¹ * c)) *
          toConv (SeminaireExp3.ZariskiGL.pt z) := by
      rw [SeminaireExp3.ZariskiGL.pt_mul, toConv_ofConv]
    _ = (toConv (SeminaireExp3.ZariskiGL.pt z⁻¹) *
          toConv (SeminaireExp3.ZariskiGL.pt c)) *
            toConv (SeminaireExp3.ZariskiGL.pt z) := by
      rw [SeminaireExp3.ZariskiGL.pt_mul, toConv_ofConv]
    _ = (toConv ((SeminaireExp3.ZariskiGL.pt z).comp
          (HopfAlgebra.antipodeAlgHom k (GLCoord k (Label τ)))) *
            toConv (SeminaireExp3.ZariskiGL.pt c)) *
              toConv (SeminaireExp3.ZariskiGL.pt z) := by
      rw [SeminaireExp3.ZariskiGL.pt_inv]

private theorem continuous_inv_mul_mul (c : SeminaireExp3.ZariskiGL (Label τ) k) :
    Continuous fun z : SeminaireExp3.ZariskiGL (Label τ) k => z⁻¹ * c * z :=
  SeminaireExp3.ZariskiGL.continuous_of_comp_eq (conjCo c) (pt_inv_mul_mul c)

private theorem pt_pow (z : SeminaireExp3.ZariskiGL (Label τ) k) (m : ℕ) :
    SeminaireExp3.ZariskiGL.pt (z ^ m) =
      (SeminaireExp3.ZariskiGL.pt z).comp
        ((toConv (AlgHom.id k (GLCoord k (Label τ)))) ^ m).ofConv := by
  apply toConv_injective
  rw [toConv_comp_convPow_aux]
  rw [show (SeminaireExp3.ZariskiGL.pt z).comp
      ((toConv (AlgHom.id k (GLCoord k (Label τ)))).ofConv) =
        SeminaireExp3.ZariskiGL.pt z from by rw [ofConv_toConv, AlgHom.comp_id]]
  rw [SeminaireExp3.ZariskiGL.toConv_pt, SeminaireExp3.ZariskiGL.toConv_pt, map_pow]

private theorem continuous_pow (m : ℕ) :
    Continuous fun z : SeminaireExp3.ZariskiGL (Label τ) k => z ^ m :=
  SeminaireExp3.ZariskiGL.continuous_of_comp_eq
    (((toConv (AlgHom.id k (GLCoord k (Label τ)))) ^ m).ofConv) (pt_pow · m)

private theorem isPointClosed_setOf_linearMap_apply_eq_aux
    (f : RootModule τ k →ₗ[k] k) (v : RootModule τ k) (c : k) :
    IsPointClosed k (transportPoints (modGLPoint τ k)
      {g : ModGL τ k | f ((g : Module.End k (RootModule τ k)) v) = c}) := by
  let P : GLCoord k (Label τ) :=
    ∑ a : Label τ, ∑ b : Label τ,
      (f (Finsupp.single a 1) * v b) • glEntry k (Label τ) a b
  have hP (g : ModGL τ k) : (modGLPoint τ k g).ofConv P =
      ∑ a : Label τ, ∑ b : Label τ,
        f (Finsupp.single a 1) * v b *
          (g : Module.End k (RootModule τ k)) (Finsupp.single b 1) a := by
    dsimp only [P]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, modGLPoint_apply_glEntry, smul_eq_mul]
  have hset : modGLZariski τ k '' {g : ModGL τ k |
        f ((g : Module.End k (RootModule τ k)) v) = c} =
      {z : SeminaireExp3.ZariskiGL (Label τ) k | SeminaireExp3.ZariskiGL.pt z P = c} := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [Set.mem_setOf_eq, pt_modGLZariski, hP, ← linearMap_apply_eq_sum_entries, hg]
    · intro hz
      set g : ModGL τ k := (modGLZariski τ k).symm z with hg
      have hze : z = modGLZariski τ k g := by
        rw [hg, MulEquiv.apply_symm_apply]
      refine ⟨g, ?_, hze.symm⟩
      have h := hz
      rw [Set.mem_setOf_eq, hze, pt_modGLZariski, hP,
        ← linearMap_apply_eq_sum_entries] at h
      exact h
  rw [isPointClosed_iff_isClosed_image, hset]
  exact isClosed_setOf_pt_eq P c

theorem isPointClosed_preimage_mul_mul (x y : ModGL τ k) {S : Set (ModGL τ k)}
    (hS : IsPointClosed k (transportPoints (modGLPoint τ k) S)) :
    IsPointClosed k (transportPoints (modGLPoint τ k) ((fun g => x * g * y) ⁻¹' S)) := by
  refine isPointClosed_preimage_of_continuous
    (f := fun g => x * g * y)
    (F := fun z => modGLZariski τ k x * (z * modGLZariski τ k y)) ?_ ?_ hS
  · exact (SeparatelyContinuousMul.continuous_const_mul
      (a := modGLZariski τ k x)).comp
      (SeparatelyContinuousMul.continuous_mul_const (a := modGLZariski τ k y))
  · intro g
    simp only [map_mul, mul_assoc]

theorem isPointClosed_preimage_inv_mul_mul (b : ModGL τ k) {S : Set (ModGL τ k)}
    (hS : IsPointClosed k (transportPoints (modGLPoint τ k) S)) :
    IsPointClosed k (transportPoints (modGLPoint τ k) ((fun g => g⁻¹ * b * g) ⁻¹' S)) := by
  refine isPointClosed_preimage_of_continuous
    (f := fun g => g⁻¹ * b * g)
    (F := fun z => z⁻¹ * modGLZariski τ k b * z)
    (continuous_inv_mul_mul (modGLZariski τ k b)) ?_ hS
  intro g
  simp only [map_mul, map_inv]

theorem isPointClosed_setOf_pow_eq_one (m : ℕ) :
    IsPointClosed k (transportPoints (modGLPoint τ k) {g : ModGL τ k | g ^ m = 1}) := by
  have h := isPointClosed_preimage_of_continuous
    (f := fun g : ModGL τ k => g ^ m) (F := fun z : SeminaireExp3.ZariskiGL (Label τ) k =>
      z ^ m) (continuous_pow m) (fun g => by simp only [map_pow]) (S := {1})
    isPointClosed_transportPoints_one
  have hset : ((fun g : ModGL τ k => g ^ m) ⁻¹' ({1} : Set (ModGL τ k))) =
      {g : ModGL τ k | g ^ m = 1} := by
    ext g
    simp
  rw [hset] at h
  exact h

theorem isPointClosed_setOf_apply_apply_eq (v : RootModule τ k) (a : Label τ) (c : k) :
    IsPointClosed k (transportPoints (modGLPoint τ k)
      {g : ModGL τ k | (g : Module.End k (RootModule τ k)) v a = c}) := by
  simpa only [Finsupp.lapply_apply] using
    (isPointClosed_setOf_linearMap_apply_eq_aux (f := Finsupp.lapply a) v c)

theorem isPointClosed_setOf_linearMap_apply_eq (f : RootModule τ k →ₗ[k] k) (v : RootModule τ k)
    (c : k) :
    IsPointClosed k (transportPoints (modGLPoint τ k)
      {g : ModGL τ k | f ((g : Module.End k (RootModule τ k)) v) = c}) :=
  isPointClosed_setOf_linearMap_apply_eq_aux f v c

theorem isPointClosed_iInter {ι : Sort*} {S : ι → Set (ModGL τ k)}
    (hS : ∀ i, IsPointClosed k (transportPoints (modGLPoint τ k) (S i))) :
    IsPointClosed k (transportPoints (modGLPoint τ k) (⋂ i, S i)) := by
  have hS' : ∀ i, IsClosed (modGLZariski τ k '' S i) := fun i => by
    rw [← isPointClosed_iff_isClosed_image]
    exact hS i
  rw [isPointClosed_iff_isClosed_image, Set.image_iInter (modGLZariski τ k).bijective]
  exact isClosed_iInter hS'

theorem isPointClosed_inter {S T : Set (ModGL τ k)}
    (hS : IsPointClosed k (transportPoints (modGLPoint τ k) S))
    (hT : IsPointClosed k (transportPoints (modGLPoint τ k) T)) :
    IsPointClosed k (transportPoints (modGLPoint τ k) (S ∩ T)) := by
  rw [isPointClosed_iff_isClosed_image] at hS hT ⊢
  rw [Set.image_inter (modGLZariski τ k).injective]
  exact hS.inter hT

theorem exists_isPointClosed_subgroup_closure (P : Subgroup (ModGL τ k)) :
    ∃ U : Subgroup (ModGL τ k), P ≤ U ∧
      IsPointClosed k (transportPoints (modGLPoint τ k) (U : Set (ModGL τ k))) ∧
      (∀ C : Set (ModGL τ k), IsPointClosed k (transportPoints (modGLPoint τ k) C) →
        (P : Set (ModGL τ k)) ⊆ C → (U : Set (ModGL τ k)) ⊆ C) ∧
      (IsPointIrreducible k (transportPoints (modGLPoint τ k) (P : Set (ModGL τ k))) →
        IsPointIrreducible k (transportPoints (modGLPoint τ k) (U : Set (ModGL τ k)))) := by
  let P' : Subgroup (SeminaireExp3.ZariskiGL (Label τ) k) :=
    P.map (modGLZariski τ k).toMonoidHom
  let C : Set (SeminaireExp3.ZariskiGL (Label τ) k) := closure (P' : Set _)
  let U : Subgroup (ModGL τ k) :=
    { carrier := modGLZariski τ k ⁻¹' C
      one_mem' := by
        show modGLZariski τ k 1 ∈ C
        rw [map_one]
        exact subset_closure (by simp)
      mul_mem' := by
        intro x y hx hy
        show modGLZariski τ k (x * y) ∈ C
        rw [map_mul]
        exact closure_mul_mem P' hx hy
      inv_mem' := by
        intro x hx
        show modGLZariski τ k x⁻¹ ∈ C
        rw [map_inv]
        exact closure_inv_mem P' hx }
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact subset_closure (Set.mem_image_of_mem _ hp)
  · rw [isPointClosed_iff_isClosed_image]
    have himg : modGLZariski τ k '' (U : Set (ModGL τ k)) = C := by
      rw [show (U : Set (ModGL τ k)) = modGLZariski τ k ⁻¹' C from rfl]
      exact Set.image_preimage_eq C (modGLZariski τ k).surjective
    rw [himg]
    exact isClosed_closure
  · intro D hD hPD
    rw [isPointClosed_iff_isClosed_image] at hD
    have hsub : (P' : Set _) ⊆ modGLZariski τ k '' D := by
      intro z hz
      change z ∈ P.map (modGLZariski τ k).toMonoidHom at hz
      rw [Subgroup.mem_map] at hz
      obtain ⟨p, hp, rfl⟩ := hz
      exact ⟨p, hPD hp, rfl⟩
    intro u hu
    have hu' : modGLZariski τ k u ∈ modGLZariski τ k '' D :=
      closure_minimal hsub hD hu
    obtain ⟨c, hc, hce⟩ := hu'
    have hcu : c = u := (modGLZariski τ k).injective hce
    rwa [hcu] at hc
  · intro hirr
    rw [isPointIrreducible_iff_isIrreducible_image] at hirr ⊢
    have himg : modGLZariski τ k '' (U : Set (ModGL τ k)) = C := by
      rw [show (U : Set (ModGL τ k)) = modGLZariski τ k ⁻¹' C from rfl]
      exact Set.image_preimage_eq C (modGLZariski τ k).surjective
    rw [himg]
    exact (show IsIrreducible (P' : Set (SeminaireExp3.ZariskiGL (Label τ) k)) from
      hirr).closure

theorem exists_antitone_isPointClosed_stabilizes {T : ℕ → Set (ModGL τ k)} (hT : Antitone T)
    (hTc : ∀ m, IsPointClosed k (transportPoints (modGLPoint τ k) (T m))) :
    ∃ M, ∀ m, M ≤ m → T m = T M := by
  have hcl : ∀ m, IsClosed (modGLZariski τ k '' T m) := fun m => by
    rw [← isPointClosed_iff_isClosed_image]
    exact hTc m
  let g : ℕ → TopologicalSpace.Closeds (SeminaireExp3.ZariskiGL (Label τ) k) :=
    fun m => ⟨modGLZariski τ k '' T m, hcl m⟩
  have hanti : Antitone g := fun m n hmn => Set.image_mono (hT hmn)
  obtain ⟨Mclosed, hM⟩ := WellFoundedLT.exists_minimal
    (inferInstance : WellFoundedLT (TopologicalSpace.Closeds
      (SeminaireExp3.ZariskiGL (Label τ) k))) (Set.range g) ⟨g 0, 0, rfl⟩
  obtain ⟨M, hMk⟩ := hM.1
  refine ⟨M, fun m hm => ?_⟩
  have hle : g m ≤ g M := hanti hm
  have hge : g M ≤ g m := by
    have h := hM.2 ⟨m, rfl⟩ (by rw [← hMk]; exact hle)
    rwa [← hMk] at h
  have heq : g m = g M := le_antisymm hle hge
  exact (modGLZariski τ k).injective.image_injective
    (congrArg (fun x : TopologicalSpace.Closeds
      (SeminaireExp3.ZariskiGL (Label τ) k) =>
        (x : Set (SeminaireExp3.ZariskiGL (Label τ) k))) heq)

theorem wellFounded_ssubset_isPointClosed :
    WellFounded fun S T : {S : Set (ModGL τ k) //
      IsPointClosed k (transportPoints (modGLPoint τ k) S)} => S.1 ⊂ T.1 := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun ⟨f, hf⟩ => ?_⟩
  have hcl : ∀ n, IsClosed (modGLZariski τ k '' (f n).1) := fun n => by
    rw [← isPointClosed_iff_isClosed_image]
    exact (f n).2
  have hanti : StrictAnti fun n => (f n).1 := strictAnti_nat_of_succ_lt fun n => hf n
  have hg : StrictAnti fun n =>
      (⟨modGLZariski τ k '' (f n).1, hcl n⟩ : TopologicalSpace.Closeds _) := by
    intro m n hmn
    exact (modGLZariski τ k).injective.image_strictMono (hanti hmn)
  exact not_strictAnti_of_wellFoundedLT _ hg

section Frobenius

variable (p : ℕ) [Fact p.Prime] [CharP k p]

private theorem entrywiseFrobGL_apply_entry (e : ℕ) (g : ModGL τ k) (a b : Label τ) :
    (((entrywiseFrobGL τ k p e g : ModGL τ k) :
        Module.End k (RootModule τ k)) (Finsupp.single b 1)) a =
      (((g : ModGL τ k) : Module.End k (RootModule τ k))
        (Finsupp.single b 1) a) ^ p ^ e := by
  rw [show ((entrywiseFrobGL τ k p e g : ModGL τ k) :
        Module.End k (RootModule τ k)) =
      entrywise (iterateFrobenius k p e) ((g : ModGL τ k) :
        Module.End k (RootModule τ k)) from rfl]
  rw [entrywise_single, Finsupp.mapRange_apply, iterateFrobenius_def]

private theorem ofConv_modGLPoint_entrywiseFrobGL (e : ℕ) (g : ModGL τ k) :
    (modGLPoint τ k (entrywiseFrobGL τ k p e g)).ofConv =
      (modGLPoint τ k g).ofConv.comp (frobCo p e) := by
  have h := congrArg WithConv.ofConv
    (toConv_comp_frobCo (τ := τ) p e (modGLPoint τ k g).ofConv)
  simpa using h.symm

private theorem continuous_entrywiseFrobGL (e : ℕ) :
    Continuous fun z : SeminaireExp3.ZariskiGL (Label τ) k =>
      modGLZariski τ k (entrywiseFrobGL τ k p e ((modGLZariski τ k).symm z)) := by
  refine SeminaireExp3.ZariskiGL.continuous_of_comp_eq (frobCo p e) fun z => ?_
  have hpt : SeminaireExp3.ZariskiGL.pt z =
      (modGLPoint τ k ((modGLZariski τ k).symm z)).ofConv := by
    conv_lhs => rw [show z = modGLZariski τ k ((modGLZariski τ k).symm z) from
      (MulEquiv.apply_symm_apply _ _).symm]
    rw [pt_modGLZariski]
  rw [pt_modGLZariski, ofConv_modGLPoint_entrywiseFrobGL, hpt]

theorem isPointClosed_preimage_entrywiseFrobGL (e : ℕ) {S : Set (ModGL τ k)}
    (hS : IsPointClosed k (transportPoints (modGLPoint τ k) S)) :
    IsPointClosed k (transportPoints (modGLPoint τ k) (entrywiseFrobGL τ k p e ⁻¹' S)) := by
  refine isPointClosed_preimage_of_continuous
    (f := entrywiseFrobGL τ k p e)
    (F := fun z => modGLZariski τ k
      (entrywiseFrobGL τ k p e ((modGLZariski τ k).symm z)))
    (continuous_entrywiseFrobGL p e) ?_ hS
  intro g
  simp only [MulEquiv.symm_apply_apply]

theorem isPointIrreducible_image_entrywiseFrobGL (e : ℕ) {S : Set (ModGL τ k)}
    (hS : IsPointIrreducible k (transportPoints (modGLPoint τ k) S)) :
    IsPointIrreducible k (transportPoints (modGLPoint τ k) (entrywiseFrobGL τ k p e '' S)) := by
  unfold IsPointIrreducible at hS ⊢
  have hpts : pointSpec '' transportPoints (modGLPoint τ k)
        (entrywiseFrobGL τ k p e '' S) =
      PrimeSpectrum.comap (frobCo (k := k) (ι := Label τ) p e :
        GLCoord k (Label τ) →+* GLCoord k (Label τ)) ''
        (pointSpec '' transportPoints (modGLPoint τ k) S) := by
    simp only [transportPoints, Set.image_image, comap_pointSpec,
      ofConv_modGLPoint_entrywiseFrobGL]
  rw [hpts]
  exact hS.image _ (PrimeSpectrum.continuous_comap _).continuousOn

theorem pow_pow_card_label_eq_one {g : ModGL τ k} {a : ℕ} (hg : g ^ p ^ a = 1) :
    g ^ p ^ Fintype.card (Label τ) = 1 := by
  have hEndChar : CharP (Module.End k (RootModule τ k)) p :=
    Module.charP_end (M := RootModule τ k) (p := p)
      ⟨Finsupp.single (Sum.inl ⟨0, by cases τ <;> decide⟩) (1 : k),
        (Ideal.torsionOf_eq_bot_iff_of_isTorsionFree (R := k) _).2 (by simp)⟩
  let N : Module.End k (RootModule τ k) := (g : Module.End k (RootModule τ k)) - 1
  have hNpow : N ^ p ^ a = 0 := by
    have hsub := sub_pow_char_pow_of_commute (p := p) (n := a)
      (x := (g : Module.End k (RootModule τ k))) (y := 1) (Commute.one_right _)
    have hg' : ((g : Module.End k (RootModule τ k))) ^ p ^ a = 1 := by
      rw [← Units.val_pow_eq_pow_val, hg, Units.val_one]
    rw [hsub, hg', one_pow, sub_self]
  have hnil : IsNilpotent N := ⟨p ^ a, hNpow⟩
  have hchar : N.charpoly = Polynomial.X ^ Module.finrank k (RootModule τ k) :=
    hnil.charpoly_eq_X_pow_finrank
  have hNn : N ^ Module.finrank k (RootModule τ k) = 0 := by
    have h := LinearMap.aeval_self_charpoly N
    rw [hchar] at h
    simpa using h
  have hNcard : N ^ Fintype.card (Label τ) = 0 := by
    rw [← Module.finrank_finsupp_self (R := k) (ι := Label τ)]
    exact hNn
  have hle : Fintype.card (Label τ) ≤ p ^ Fintype.card (Label τ) := by
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    exact (Nat.lt_two_pow_self (n := Fintype.card (Label τ))).le.trans
      (Nat.pow_le_pow_left hp2 _)
  have hNbig : N ^ p ^ Fintype.card (Label τ) = 0 :=
    pow_eq_zero_of_le hle hNcard
  have hg' : (g : Module.End k (RootModule τ k)) ^ p ^ Fintype.card (Label τ) = 1 := by
    have hsub := sub_pow_char_pow_of_commute (p := p) (n := Fintype.card (Label τ))
      (x := (g : Module.End k (RootModule τ k))) (y := 1) (Commute.one_right _)
    rw [hsub, one_pow, sub_eq_zero] at hNbig
    exact hNbig
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact hg'

private theorem exists_pow_fixed_of_isAlgebraic
    (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) (x : k) :
    ∃ d, 1 ≤ d ∧ x ^ p ^ d = x := by
  let := ZMod.algebra k p
  have halg' : Algebra.IsAlgebraic (ZMod p) k := halg
  let E : IntermediateField (ZMod p) k := IntermediateField.adjoin (ZMod p) {x}
  have hxint : IsIntegral (ZMod p) x := (halg'.isAlgebraic x).isIntegral
  have hfin : FiniteDimensional (ZMod p) E :=
    IntermediateField.finiteDimensional_adjoin (S := {x}) fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      rwa [hy]
  let : Fintype E := Fintype.ofEquiv (Fin (Module.finrank (ZMod p) E) → ZMod p)
    (Module.finBasis (ZMod p) E).equivFun.toEquiv.symm
  let d : ℕ := Module.finrank (ZMod p) E
  have hq : p ^ d = Fintype.card E := FiniteField.pow_finrank_eq_card p E
  have hdpos : 0 < d := by
    by_contra h
    have h0 : d = 0 := Nat.eq_zero_of_not_pos h
    obtain ⟨a, ha, haz⟩ := (Module.finrank_eq_zero_iff (R := ZMod p) (M := E)).mp h0 1
    have hz : algebraMap (ZMod p) E a = 0 := by simpa [Algebra.smul_def] using haz
    exact ha (FaithfulSMul.algebraMap_injective (ZMod p) E (by simpa using hz))
  refine ⟨d, hdpos, ?_⟩
  have hxE : x ∈ E := IntermediateField.mem_adjoin_simple_self (ZMod p) x
  have hcard : (⟨x, hxE⟩ : E) ^ p ^ d = ⟨x, hxE⟩ := by
    rw [hq]
    exact FiniteField.pow_card _
  have hcast := congrArg (fun y : E => (y : k)) hcard
  simpa using hcast

omit [Fact (Nat.Prime p)] [CharP k p] in
private theorem pow_fixed_of_dvd {x : k} {d j : ℕ} (_hd : 1 ≤ d) (hj : d ∣ j)
    (hx : x ^ p ^ d = x) : x ^ p ^ j = x := by
  obtain ⟨n, rfl⟩ := hj
  rw [pow_mul]
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_mul, ih, hx]

theorem exists_entrywiseFrobGL_eq_self
    (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) (g : ModGL τ k) :
    ∃ s, 1 ≤ s ∧ ∀ j, s ∣ j → entrywiseFrobGL τ k p j g = g := by
  let := ZMod.algebra k p
  have halg' : Algebra.IsAlgebraic (ZMod p) k := halg
  choose d hd1 hdx using fun (a b : Label τ) =>
    exists_pow_fixed_of_isAlgebraic (p := p) halg'
      (((g : ModGL τ k) : Module.End k (RootModule τ k)) (Finsupp.single b 1) a)
  let s : ℕ := ∏ a : Label τ, ∏ b : Label τ, d a b
  refine ⟨s, ?_, fun j hj => ?_⟩
  · exact Nat.succ_le_of_lt
      (Finset.prod_pos fun a _ => Finset.prod_pos fun b _ => hd1 a b)
  · refine Units.ext (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.end_ext_single
      fun b => Finsupp.ext fun a => ?_)
    rw [entrywiseFrobGL_apply_entry]
    have h1 : d a b ∣ ∏ c : Label τ, d a c :=
      Finset.dvd_prod_of_mem (fun c => d a c) (Finset.mem_univ b)
    have h2 : (∏ c : Label τ, d a c) ∣ s :=
      Finset.dvd_prod_of_mem (fun c => ∏ b, d c b) (Finset.mem_univ a)
    have hdvd : d a b ∣ j := dvd_trans (dvd_trans h1 h2) hj
    exact pow_fixed_of_dvd (p := p) (d := d a b) (j := j) (hd1 a b) hdvd (hdx a b)

theorem exists_iterate_frobTwistGL_eq_self
    {τ : Tag} {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]
    (e : ℕ) {Q : ModGL τ L} (hQ : entrywiseFrobGL τ L p e Q = Q)
    {r : ℕ} (hr : 0 < r) (hQr : Q ^ r = 1)
    (halg : letI := ZMod.algebra L p; Algebra.IsAlgebraic (ZMod p) L)
    (x : ModGL τ L) :
    ∃ m : ℕ, 0 < m ∧ (frobTwistGL τ L p e Q)^[m] x = x := by
  obtain ⟨s, hs, hxs⟩ := exists_entrywiseFrobGL_eq_self p halg x
  refine ⟨r * s, Nat.mul_pos hr (by omega), ?_⟩
  rw [frobTwistGL_iterate p e hQ, pow_mul, hQr, one_pow, inv_one, one_mul, mul_one]
  exact hxs _ ⟨e * r, by ring⟩

theorem map_frobTwistGL_eq_self_of_mapsTo
    {τ : Tag} {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]
    (e : ℕ) {Q : ModGL τ L} (hQ : entrywiseFrobGL τ L p e Q = Q)
    {r : ℕ} (hr : 0 < r) (hQr : Q ^ r = 1)
    (halg : letI := ZMod.algebra L p; Algebra.IsAlgebraic (ZMod p) L)
    {Z : Subgroup (ModGL τ L)} (hZ : ∀ x ∈ Z, frobTwistGL τ L p e Q x ∈ Z) :
    Z.map (frobTwistGL τ L p e Q) = Z := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hZ x hx
  · intro x hx
    obtain ⟨m, hm, hmx⟩ := exists_iterate_frobTwistGL_eq_self p e hQ hr hQr halg x
    have hmem : ∀ a : ℕ, (frobTwistGL τ L p e Q)^[a] x ∈ Z := by
      intro a
      induction a with
      | zero => exact hx
      | succ a ih =>
        rw [Function.iterate_succ_apply']
        exact hZ _ ih
    refine ⟨(frobTwistGL τ L p e Q)^[m - 1] x, hmem _, ?_⟩
    rw [← Function.iterate_succ_apply' (frobTwistGL τ L p e Q) (m - 1) x,
      show (m - 1).succ = m by omega]
    exact hmx

end Frobenius

end CFSG.LieType.AlgebraicGroups
