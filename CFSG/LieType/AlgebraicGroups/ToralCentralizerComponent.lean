module

public import CFSG.LieType.AlgebraicGroups.ConstructibleSubgroupClosed
public import CFSG.LieType.AlgebraicGroups.TwistedOrbitSurjectivity
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open WithConv Topology
open scoped CFSG.ConvolutionPoints

section PointClosed

variable {k : Type} [Field k] {A : Type} [CommRing A] [Algebra k A]

theorem IsPointClosed.inter {S T : Set (A →ₐ[k] k)} (hS : IsPointClosed k S)
    (hT : IsPointClosed k T) : IsPointClosed k (S ∩ T) := by
  obtain ⟨Z, hZ, rfl⟩ := hS
  obtain ⟨Z', hZ', rfl⟩ := hT
  exact ⟨Z ∩ Z', hZ.inter hZ', rfl⟩

theorem isPointClosed_pointsZero (I : Ideal A) : IsPointClosed k (pointsZero k I) :=
  ⟨PrimeSpectrum.zeroLocus (I : Set A), PrimeSpectrum.isClosed_zeroLocus _, by
    ext y
    exact pointSpec_mem_zeroLocus.symm⟩

theorem IsPointClosed.preimage_comp {B : Type} [CommRing B] [Algebra k B] (σ : B →ₐ[k] A)
    {S : Set (B →ₐ[k] k)} (h : IsPointClosed k S) : IsPointClosed k {y | y.comp σ ∈ S} := by
  obtain ⟨Z, hZ, rfl⟩ := h
  refine ⟨PrimeSpectrum.comap (σ : B →+* A) ⁻¹' Z, hZ.preimage (PrimeSpectrum.continuous_comap _),
    ?_⟩
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, comap_pointSpec]

theorem isPointClosed_setOf_comp_eq (σ : A →ₐ[k] A) : IsPointClosed k {y | y.comp σ = y} := by
  have h : {y : A →ₐ[k] k | y.comp σ = y} =
      pointsZero k (Ideal.span (Set.range fun a => σ a - a)) := by
    ext y
    rw [Set.mem_ofPred_eq, mem_pointsZero]
    constructor
    · intro hy b hb
      have hle : Ideal.span (Set.range fun a => σ a - a) ≤ RingHom.ker y := by
        rw [Ideal.span_le]
        rintro _ ⟨a, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, ← AlgHom.comp_apply, hy, sub_self]
      exact hle hb
    · intro hy
      ext a
      have := hy _ (Ideal.subset_span ⟨a, rfl⟩)
      rwa [map_sub, sub_eq_zero] at this
  rw [h]
  exact isPointClosed_pointsZero _

theorem preimage_closure_image_pointSpec {S : Set (A →ₐ[k] k)} (h : IsPointClosed k S) :
    pointSpec ⁻¹' closure (pointSpec '' S) = S := by
  obtain ⟨Z, hZ, rfl⟩ := h
  refine le_antisymm (fun y hy => ?_) fun y hy => subset_closure ⟨y, hy, rfl⟩
  exact (hZ.closure_subset_iff.2 (Set.image_preimage_subset _ _)) hy

theorem isPointClosed_biUnion_of_finite {ι : Type*} {s : Set ι} (hs : s.Finite)
    {S : ι → Set (A →ₐ[k] k)} (hS : ∀ i ∈ s, IsPointClosed k (S i)) :
    IsPointClosed k (⋃ i ∈ s, S i) := by
  refine ⟨⋃ i ∈ s, closure (pointSpec '' S i), hs.isClosed_biUnion fun _ _ => isClosed_closure,
    ?_⟩
  rw [Set.preimage_iUnion₂]
  exact Set.iUnion₂_congr fun i hi => (preimage_closure_image_pointSpec (hS i hi)).symm

theorem pointsZero_pointsIdeal_of_isPointClosed {S : Set (A →ₐ[k] k)} (h : IsPointClosed k S) :
    pointsZero k (pointsIdeal S) = S := by
  rw [pointsZero_pointsIdeal, preimage_closure_image_pointSpec h]

theorem zeroLocus_pointsIdeal (S : Set (A →ₐ[k] k)) :
    PrimeSpectrum.zeroLocus (pointsIdeal S : Set A) = closure (pointSpec '' S) :=
  PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure _

end PointClosed

section Cosets

variable {k : Type} [Field k] {A : Type} [CommRing A] [HopfAlgebra k A]

theorem isPointClosed_leftCoset {M : Subgroup (WithConv (A →ₐ[k] k))}
    (hM : IsPointClosed k (subgroupPoints M)) (t : WithConv (A →ₐ[k] k)) :
    IsPointClosed k {y : A →ₐ[k] k | t⁻¹ * toConv y ∈ M} := by
  have heq : {y : A →ₐ[k] k | t⁻¹ * toConv y ∈ M} =
      {y | y.comp (biTransCo t⁻¹ 1) ∈ subgroupPoints M} := by
    ext y
    have e := point_comp_biTransCo t⁻¹ 1 (toConv y)
    rw [ofConv_toConv, mul_one] at e
    change _ ↔ toConv (y.comp (biTransCo t⁻¹ 1)) ∈ M
    rw [e]
    rfl
  rw [heq]
  exact hM.preimage_comp _

theorem isPointClosed_subgroupPoints_diff {Z M : Subgroup (WithConv (A →ₐ[k] k))} (hMZ : M ≤ Z)
    (hM : IsPointClosed k (subgroupPoints M)) {T : Set (WithConv (A →ₐ[k] k))} (hT : T.Finite)
    (hTZ : T ⊆ Z) (hcov : ∀ z ∈ Z, ∃ t ∈ T, t⁻¹ * z ∈ M) :
    IsPointClosed k (subgroupPoints Z \ subgroupPoints M) := by
  have heq : subgroupPoints Z \ subgroupPoints M =
      ⋃ t ∈ {t | t ∈ T ∧ t ∉ M}, {y : A →ₐ[k] k | t⁻¹ * toConv y ∈ M} := by
    ext y
    simp only [Set.mem_sdiff, Set.mem_preimage, SetLike.mem_coe, Set.mem_iUnion, Set.mem_ofPred_eq,
      exists_prop]
    constructor
    · rintro ⟨hyZ, hyM⟩
      obtain ⟨t, htT, ht⟩ := hcov _ hyZ
      refine ⟨t, ⟨htT, fun htM => hyM ?_⟩, ht⟩
      have := M.mul_mem htM ht
      rwa [mul_inv_cancel_left] at this
    · rintro ⟨t, ⟨htT, htM⟩, ht⟩
      refine ⟨?_, fun hyM => htM ?_⟩
      · have := Z.mul_mem (hTZ htT) (hMZ ht)
        rwa [mul_inv_cancel_left] at this
      · have := M.mul_mem hyM (M.inv_mem ht)
        rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at this
  rw [heq]
  exact isPointClosed_biUnion_of_finite (hT.subset fun t ht => ht.1) fun t _ =>
    isPointClosed_leftCoset hM t

end Cosets

section Component

variable {k : Type} [Field k] [IsAlgClosed k] {A : Type} [CommRing A] [HopfAlgebra k A]
  [Algebra.FiniteType k A]

theorem connectedComponentIn_zeroLocus_eq {Z M : Subgroup (WithConv (A →ₐ[k] k))} (hMZ : M ≤ Z)
    (hM : IsConnectedAlgebraicSubgroup k M)
    (hdiff : IsPointClosed k (subgroupPoints Z \ subgroupPoints M)) :
    connectedComponentIn (PrimeSpectrum.zeroLocus (subgroupIdeal Z : Set A))
        (pointSpec (1 : WithConv (A →ₐ[k] k)).ofConv) =
      PrimeSpectrum.zeroLocus (subgroupIdeal M : Set A) := by
  set C := closure (pointSpec '' (subgroupPoints Z \ subgroupPoints M))
  have hsub : subgroupPoints M ⊆ subgroupPoints Z := Set.preimage_mono hMZ
  have hVZ : PrimeSpectrum.zeroLocus (subgroupIdeal Z : Set A) ⊆
      PrimeSpectrum.zeroLocus (subgroupIdeal M : Set A) ∪ C := by
    rw [zeroLocus_pointsIdeal, zeroLocus_pointsIdeal, ← closure_union, ← Set.image_union,
      Set.union_sdiff_cancel hsub]
  have hdisj : PrimeSpectrum.zeroLocus (subgroupIdeal M : Set A) ∩ C = ∅ := by
    by_contra hne
    obtain ⟨y, hy⟩ := exists_algHom_mem_of_isLocallyClosed k A
      ((PrimeSpectrum.isClosed_zeroLocus _).inter isClosed_closure).isLocallyClosed
      (Set.nonempty_iff_ne_empty.2 hne)
    have hyM : y ∈ subgroupPoints M := by
      rw [← hM.pointsZero_eq]
      exact pointSpec_mem_zeroLocus.1 hy.1
    have hyC : y ∈ subgroupPoints Z \ subgroupPoints M := by
      rw [← preimage_closure_image_pointSpec hdiff]
      exact hy.2
    exact hyC.2 hyM
  have hone : pointSpec (1 : WithConv (A →ₐ[k] k)).ofConv ∈
      PrimeSpectrum.zeroLocus (subgroupIdeal M : Set A) := by
    rw [pointSpec_mem_zeroLocus, hM.pointsZero_eq]
    exact M.one_mem
  have hirr : IsIrreducible (PrimeSpectrum.zeroLocus (subgroupIdeal M : Set A)) := by
    rw [PrimeSpectrum.isIrreducible_zeroLocus_iff, hM.isRadical.radical]
    exact hM.isPrime
  have hMZV : PrimeSpectrum.zeroLocus (subgroupIdeal M : Set A) ⊆
      PrimeSpectrum.zeroLocus (subgroupIdeal Z : Set A) :=
    PrimeSpectrum.zeroLocus_anti_mono fun a ha => mem_pointsIdeal.2 fun y hy =>
      mem_pointsIdeal.1 ha y (hsub hy)
  refine le_antisymm ?_ (hirr.2.isPreconnected.subset_connectedComponentIn hone hMZV)
  have hcomp := (isPreconnected_iff_subset_of_disjoint_closed.1
    (isPreconnected_connectedComponentIn (x := pointSpec (1 : WithConv (A →ₐ[k] k)).ofConv)
      (F := PrimeSpectrum.zeroLocus (subgroupIdeal Z : Set A)))) _ _
    (PrimeSpectrum.isClosed_zeroLocus _) isClosed_closure
    ((connectedComponentIn_subset _ _).trans hVZ) (by rw [hdisj, Set.inter_empty])
  rcases hcomp with h | h
  · exact h
  · exfalso
    have hx := h (mem_connectedComponentIn (hMZV hone))
    have : pointSpec (1 : WithConv (A →ₐ[k] k)).ofConv ∈
        PrimeSpectrum.zeroLocus (subgroupIdeal M : Set A) ∩ C := ⟨hone, hx⟩
    rw [hdisj] at this
    exact this

end Component

end CFSG.LieType.AlgebraicGroups
