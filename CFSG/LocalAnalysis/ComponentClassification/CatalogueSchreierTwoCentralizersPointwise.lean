module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierTwoCentralizersStabilizer

public section

namespace CFSG.ComponentClassification.CatalogueSchreierTwoCentralizers

open OuterAutomorphisms

variable {G : Type*} [Group G]

@[expose] def secondCentralizer (t : G) : Subgroup G :=
  Subgroup.centralizer ({t} : Set G)

theorem mem_secondCentralizer_iff (t x : G) :
    x ∈ secondCentralizer t ↔ t * x = x * t := by
  simp only [secondCentralizer, Subgroup.mem_centralizer_iff,
    Set.mem_singleton_iff, forall_eq]

@[expose] def centralizerIntersection (M : Subgroup G) (t : G) :
    Subgroup (secondCentralizer t) := M.subgroupOf (secondCentralizer t)

@[expose] def intersectionCentralizer (M : Subgroup G) (t : G) :
    Subgroup (secondCentralizer t) :=
  Subgroup.centralizer (centralizerIntersection M t : Set (secondCentralizer t))

theorem pointwise_preserves_secondCentralizer (M : Subgroup G) (t : G) (ht : t ∈ M)
    (automorphism : pointwiseKernel M) :
    ((automorphism : stabilizer M) : MulAut G) ∈ stabilizer (secondCentralizer t) := by
  intro member
  rw [mem_secondCentralizer_iff, mem_secondCentralizer_iff]
  let action : MulAut G := ((automorphism : stabilizer M) : MulAut G)
  have hfixed : action t = t := pointwiseKernel_fixes M automorphism t ht
  constructor
  · intro hcommute
    simpa only [map_mul, hfixed] using congrArg action hcommute
  · intro hcommute
    apply action.injective
    simpa only [map_mul, hfixed] using hcommute

@[expose] def pointwiseCentralizerStabilizer (M : Subgroup G) (t : G) (ht : t ∈ M) :
    pointwiseKernel M →* stabilizer (secondCentralizer t) :=
  ((stabilizer M).subtype.comp (pointwiseKernel M).subtype).codRestrict
    (stabilizer (secondCentralizer t)) (pointwise_preserves_secondCentralizer M t ht)

@[expose] def pointwiseCentralizerRestriction (M : Subgroup G) (t : G) (ht : t ∈ M) :
    pointwiseKernel M →* MulAut (secondCentralizer t) :=
  (restrict (secondCentralizer t)).comp (pointwiseCentralizerStabilizer M t ht)

theorem pointwiseCentralizerRestriction_apply (M : Subgroup G) (t : G) (ht : t ∈ M)
    (automorphism : pointwiseKernel M) (member : secondCentralizer t) :
    (pointwiseCentralizerRestriction M t ht automorphism member).val =
      ((automorphism : stabilizer M) : MulAut G) member := rfl

theorem pointwiseCentralizerRestriction_injective (M : Subgroup G) (t : G) (ht : t ∈ M)
    (hgenerate : M ⊔ secondCentralizer t = ⊤) :
    Function.Injective (pointwiseCentralizerRestriction M t ht) := by
  intro left right hequal
  apply Subtype.ext
  apply Subtype.ext
  apply MulEquiv.ext
  intro member
  let leftAction : MulAut G := ((left : stabilizer M) : MulAut G)
  let rightAction : MulAut G := ((right : stabilizer M) : MulAut G)
  have hM : M ≤ leftAction.toMonoidHom.eqLocus rightAction.toMonoidHom := by
    intro x hx
    exact (pointwiseKernel_fixes M left x hx).trans
      (pointwiseKernel_fixes M right x hx).symm
  have hC : secondCentralizer t ≤ leftAction.toMonoidHom.eqLocus rightAction.toMonoidHom := by
    intro x hx
    exact congrArg (fun action : MulAut (secondCentralizer t) =>
      (action (⟨x, hx⟩ : secondCentralizer t)).val) hequal
  have hjoin := sup_le hM hC
  rw [hgenerate] at hjoin
  exact hjoin (Subgroup.mem_top member)

theorem pointwiseCentralizerRestriction_fixes_intersection (M : Subgroup G) (t : G)
    (ht : t ∈ M) (automorphism : pointwiseKernel M)
    (member : centralizerIntersection M t) :
    pointwiseCentralizerRestriction M t ht automorphism member = member := by
  apply Subtype.ext
  exact pointwiseKernel_fixes M automorphism member.val.val member.property

@[expose] def intersectionInnerHom (M : Subgroup G) (t : G) :
    intersectionCentralizer M t →* MulAut (secondCentralizer t) :=
  (MulAut.conj : secondCentralizer t →* MulAut (secondCentralizer t)).comp
    (intersectionCentralizer M t).subtype

@[expose] noncomputable def pointwiseCentralizerOuter (M : Subgroup G) (t : G)
    (ht : t ∈ M) : pointwiseKernel M →* Outer (secondCentralizer t) :=
  (QuotientGroup.mk' (inner (secondCentralizer t))).comp
    (pointwiseCentralizerRestriction M t ht)

theorem pointwiseCentralizerOuter_kernel_image (M : Subgroup G) (t : G) (ht : t ∈ M)
    (automorphism : (pointwiseCentralizerOuter M t ht).ker) :
    pointwiseCentralizerRestriction M t ht automorphism.val ∈
      (intersectionInnerHom M t).range := by
  have hinner : pointwiseCentralizerRestriction M t ht automorphism.val ∈
      inner (secondCentralizer t) := (QuotientGroup.eq_one_iff _).mp automorphism.property
  obtain ⟨element, helement⟩ := hinner
  have hcentral : element ∈ intersectionCentralizer M t := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro member hmember
    have hfixed : MulAut.conj element member = member := by
      rw [helement]
      exact pointwiseCentralizerRestriction_fixes_intersection M t ht automorphism.val
        ⟨member, hmember⟩
    have hproduct := congrArg (fun x : secondCentralizer t => x * element) hfixed
    simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel, mul_one] using hproduct.symm
  exact ⟨⟨element, hcentral⟩, helement⟩

@[expose] noncomputable def pointwiseCentralizerKernelEmbedding (M : Subgroup G)
    (t : G) (ht : t ∈ M) :
    (pointwiseCentralizerOuter M t ht).ker →* (intersectionInnerHom M t).range :=
  ((pointwiseCentralizerRestriction M t ht).comp
    (pointwiseCentralizerOuter M t ht).ker.subtype).codRestrict
      (intersectionInnerHom M t).range (pointwiseCentralizerOuter_kernel_image M t ht)

theorem pointwiseCentralizerKernelEmbedding_injective (M : Subgroup G) (t : G)
    (ht : t ∈ M) (hgenerate : M ⊔ secondCentralizer t = ⊤) :
    Function.Injective (pointwiseCentralizerKernelEmbedding M t ht) := by
  intro left right hequal
  apply Subtype.ext
  apply pointwiseCentralizerRestriction_injective M t ht hgenerate
  exact congrArg Subtype.val hequal

theorem pointwiseCentralizerOuter_kernel_solvable (M : Subgroup G) (t : G)
    (ht : t ∈ M) (hgenerate : M ⊔ secondCentralizer t = ⊤)
    [Group.IsSolvable (intersectionCentralizer M t)] :
    Group.IsSolvable (pointwiseCentralizerOuter M t ht).ker := by
  let : Group.IsSolvable (intersectionInnerHom M t).range :=
    Group.isSolvable_of_surjective (intersectionInnerHom M t).rangeRestrict_surjective
  exact Group.isSolvable_of_isSolvable_injective
    (pointwiseCentralizerKernelEmbedding_injective M t ht hgenerate)

theorem pointwiseKernel_solvable (M : Subgroup G) (t : G) (ht : t ∈ M)
    (hgenerate : M ⊔ secondCentralizer t = ⊤)
    [Group.IsSolvable (Outer (secondCentralizer t))]
    [Group.IsSolvable (intersectionCentralizer M t)] :
    Group.IsSolvable (pointwiseKernel M) := by
  let : Group.IsSolvable (pointwiseCentralizerOuter M t ht).ker :=
    pointwiseCentralizerOuter_kernel_solvable M t ht hgenerate
  apply Group.isSolvable_of_ker_le_range (pointwiseCentralizerOuter M t ht).ker.subtype
    (pointwiseCentralizerOuter M t ht)
  rw [Subgroup.range_subtype]

end CFSG.ComponentClassification.CatalogueSchreierTwoCentralizers
