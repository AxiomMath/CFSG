module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierTwoCentralizersPointwise

public section

namespace CFSG.ComponentClassification.CatalogueSchreierTwoCentralizers

open OuterAutomorphisms

variable {G : Type*} [Group G]

@[expose] def ConjugacyInvariant (M : Subgroup G) : Prop :=
  ∀ automorphism : MulAut G, ∃ element : G,
    M.map automorphism.toMonoidHom = M.map (MulAut.conj element).toMonoidHom

@[expose] noncomputable def stabilizerOuterHom (M : Subgroup G) :
    stabilizer M →* Outer G :=
  (QuotientGroup.mk' (inner G)).comp (stabilizer M).subtype

theorem subgroupInner_le_stabilizerOuterHom_ker (M : Subgroup G) :
    subgroupInner M ≤ (stabilizerOuterHom M).ker := by
  rintro _ ⟨member, rfl⟩
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ⟨member.val, rfl⟩

@[expose] noncomputable def innerQuotientOuterHom (M : Subgroup G) :
    InnerQuotient M →* Outer G :=
  QuotientGroup.lift (subgroupInner M) (stabilizerOuterHom M)
    (subgroupInner_le_stabilizerOuterHom_ker M)

theorem remove_conjugation_mem_stabilizer (M : Subgroup G) (automorphism : MulAut G)
    (element : G)
    (himage : M.map automorphism.toMonoidHom = M.map (MulAut.conj element).toMonoidHom) :
    (MulAut.conj element)⁻¹ * automorphism ∈ stabilizer M := by
  apply (mem_stabilizer_iff_map M _).mpr
  have hcomp : (((MulAut.conj element)⁻¹ * automorphism).toMonoidHom) =
      ((MulAut.conj element)⁻¹).toMonoidHom.comp automorphism.toMonoidHom := by
    ext member
    rfl
  rw [hcomp, ← Subgroup.map_map, himage, Subgroup.map_map]
  have hinverse : ((MulAut.conj element)⁻¹).toMonoidHom.comp
      (MulAut.conj element).toMonoidHom = MonoidHom.id G := by
    ext member
    exact (MulAut.conj element).symm_apply_apply member
  rw [hinverse, Subgroup.map_id]

theorem innerQuotientOuterHom_surjective (M : Subgroup G) (hconjugacy : ConjugacyInvariant M) :
    Function.Surjective (innerQuotientOuterHom M) := by
  intro member
  obtain ⟨automorphism, rfl⟩ := QuotientGroup.mk'_surjective (inner G) member
  obtain ⟨element, himage⟩ := hconjugacy automorphism
  let preserving : stabilizer M :=
    ⟨(MulAut.conj element)⁻¹ * automorphism,
      remove_conjugation_mem_stabilizer M automorphism element himage⟩
  refine ⟨QuotientGroup.mk' (subgroupInner M) preserving, ?_⟩
  change QuotientGroup.mk' (inner G) ((MulAut.conj element)⁻¹ * automorphism) =
    QuotientGroup.mk' (inner G) automorphism
  have hinner : QuotientGroup.mk' (inner G) (MulAut.conj element) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨element, rfl⟩
  rw [map_mul, map_inv, hinner, inv_one, one_mul]

theorem conjugacy_invariant_two_centralizer_schreier (G : Type*) [Group G] [Finite G]
    (M : Subgroup G) (hconjugacy : ConjugacyInvariant M) (t : G) (ht : t ∈ M)
    (hgenerate : M ⊔ secondCentralizer t = ⊤)
    [Group.IsSolvable (Outer M)] [Group.IsSolvable (Outer (secondCentralizer t))]
    [Group.IsSolvable (intersectionCentralizer M t)] : Group.IsSolvable (Outer G) := by
  let : Group.IsSolvable (pointwiseKernel M) := pointwiseKernel_solvable M t ht hgenerate
  let : Group.IsSolvable (InnerQuotient M) := innerQuotient_solvable M
  exact Group.isSolvable_of_surjective (innerQuotientOuterHom_surjective M hconjugacy)

end CFSG.ComponentClassification.CatalogueSchreierTwoCentralizers
