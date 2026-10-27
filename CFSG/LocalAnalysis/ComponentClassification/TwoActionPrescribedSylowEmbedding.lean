module

public import CFSG.LocalAnalysis.ComponentClassification.TwoActionStrictEmbedding
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ComponentClassification.TwoActionPrescribedSylowEmbedding

theorem transport {G Acting : Type*} [Group G] [Finite G] [Group Acting]
    (intersection : Subgroup G) (first second : Sylow 2 intersection)
    (homomorphism : Acting →* Subgroup.center ((first : Subgroup intersection).map intersection.subtype))
    (hinjective : Function.Injective homomorphism) :
    ∃ transported : Acting →* Subgroup.center ((second : Subgroup intersection).map intersection.subtype),
      Function.Injective transported := by
  open scoped Pointwise in
    obtain ⟨actor, hactor⟩ := MulAction.exists_smul_eq intersection first second
  have hlocalMap : (first : Subgroup intersection).map (MulAut.conj actor).toMonoidHom = second := by
    exact congrArg (fun sylow : Sylow 2 intersection => (sylow : Subgroup intersection)) hactor
  let firstImage := (first : Subgroup intersection).map intersection.subtype
  let secondImage := (second : Subgroup intersection).map intersection.subtype
  have hmap : firstImage.map (MulAut.conj actor.val).toMonoidHom = secondImage := by
    rw [Subgroup.map_map]
    have hhom : (MulAut.conj actor.val).toMonoidHom.comp intersection.subtype =
        intersection.subtype.comp (MulAut.conj actor).toMonoidHom := by
      ext member
      rfl
    rw [hhom, ← Subgroup.map_map, hlocalMap]
  let equivalence := (firstImage.equivMapOfInjective (MulAut.conj actor.val).toMonoidHom
    (MulAut.conj actor.val).injective).trans (MulEquiv.subgroupCongr hmap)
  let centerEquivalence := Subgroup.centerCongr equivalence
  exact ⟨centerEquivalence.toMonoidHom.comp homomorphism, centerEquivalence.injective.comp hinjective⟩

theorem embedding {G : Type*} [Group G] [Finite G] (ambient acting intersection : Subgroup G)
    (hintersection : intersection ≤ ambient) (htwo : IsPGroup 2 acting)
    (hdisjoint : Disjoint ambient acting)
    (hnormalizesAmbient : acting ≤ Subgroup.normalizer (ambient : Set G))
    (hnormalizesIntersection : acting ≤ Subgroup.normalizer (intersection : Set G))
    (hcentralizers : ∀ member ∈ acting, member ≠ 1 →
      Subgroup.centralizer {member} ⊓ ambient ≤ intersection)
    (hcommutator : ⁅acting, intersection⁆ ≤
      (CFSG.Open.componentClassificationOddCore intersection).map intersection.subtype)
    (hstrict : ∀ first : Sylow 2 intersection, ∀ second : Sylow 2 ambient,
      Nat.card (first : Subgroup intersection) < Nat.card (second : Subgroup ambient))
    (prescribed : Sylow 2 intersection) :
    ∃ homomorphism : acting →* Subgroup.center ((prescribed : Subgroup intersection).map intersection.subtype),
      Function.Injective homomorphism := by
  obtain ⟨first, homomorphism, hinjective⟩ := TwoActionStrictEmbedding.embedding ambient acting intersection
    hintersection htwo hdisjoint hnormalizesAmbient hnormalizesIntersection hcentralizers hcommutator hstrict
  exact transport intersection first prescribed homomorphism hinjective

end CFSG.ComponentClassification.TwoActionPrescribedSylowEmbedding
