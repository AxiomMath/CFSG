module

public import CFSG.LocalAnalysis.ComponentClassification.OddIndexSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionPrescribedSylowEmbedding

public section

namespace CFSG.ComponentClassification.TwoActionOddStabilizerEmbedding

theorem embedding {G : Type*} [Group G] [Finite G]
    (ambient opposite acting intersection stabilizer : Subgroup G)
    (hintersection : intersection ≤ ambient) (hstabilizer : stabilizer ≤ intersection)
    (hoddIndex : Odd (stabilizer.subgroupOf intersection).index)
    (htwo : IsPGroup 2 acting) (hacting : acting ≤ opposite)
    (hoddIntersection : Odd (Nat.card ↥(ambient ⊓ opposite)))
    (hdisjoint : Disjoint ambient acting)
    (hnormalizesAmbient : acting ≤ Subgroup.normalizer (ambient : Set G))
    (hnormalizesStabilizer : acting ≤ Subgroup.normalizer (stabilizer : Set G))
    (hstabilizerOpposite : stabilizer ≤ Subgroup.normalizer (opposite : Set G))
    (hcentralizers : ∀ member ∈ acting, member ≠ 1 → Subgroup.centralizer {member} ⊓ ambient ≤ intersection)
    (hstrict : ∀ first : Sylow 2 intersection, ∀ second : Sylow 2 ambient,
      Nat.card (first : Subgroup intersection) < Nat.card (second : Subgroup ambient))
    (prescribed : Sylow 2 intersection) :
    ∃ homomorphism : acting →* Subgroup.center ((prescribed : Subgroup intersection).map intersection.subtype),
      Function.Injective homomorphism := by
  obtain ⟨stabilizerSylow, hnormalized⟩ := TwoActionInvariantSylow.subgroup stabilizer acting htwo hnormalizesStabilizer
  obtain ⟨intersectionSylow, hsame⟩ := OddIndexSylow.nested stabilizer intersection hstabilizer hoddIndex stabilizerSylow
  let fixed := (stabilizerSylow : Subgroup stabilizer).map stabilizer.subtype
  have hfixedEq : fixed = (intersectionSylow : Subgroup intersection).map intersection.subtype := hsame.symm
  have hfixedStabilizer : fixed ≤ stabilizer := by
    rintro member ⟨lift, hlift, rfl⟩
    exact lift.property
  have hfixedIntersection := hfixedStabilizer.trans hstabilizer
  have hfixedAmbient := hfixedIntersection.trans hintersection
  have hfixedTwo : IsPGroup 2 fixed := stabilizerSylow.isPGroup'.map stabilizer.subtype
  have hcommutatorFixed : ⁅acting, fixed⁆ ≤ fixed := by
    apply Subgroup.commutator_le.mpr
    intro actor hactor member hmember
    rw [commutatorElement_def]
    exact fixed.mul_mem ((Subgroup.mem_normalizer_iff.mp (hnormalized hactor) member).mp hmember) (fixed.inv_mem hmember)
  have hcommutatorOpposite : ⁅acting, fixed⁆ ≤ opposite := by
    apply Subgroup.commutator_le.mpr
    intro actor hactor member hmember
    rw [commutatorElement_def]
    have hconjugate := (Subgroup.mem_normalizer_iff.mp (hstabilizerOpposite (hfixedStabilizer hmember)) actor⁻¹).mp
      (opposite.inv_mem (hacting hactor))
    simpa only [mul_assoc] using opposite.mul_mem (hacting hactor) hconjugate
  have hcommutatorBot := TwoActionOddIntersection.two_in_odd_eq_bot ⁅acting, fixed⁆ (ambient ⊓ opposite)
    (hfixedTwo.to_le hcommutatorFixed) hoddIntersection
      (le_inf (hcommutatorFixed.trans hfixedAmbient) hcommutatorOpposite)
  have hcentralizes : acting ≤ Subgroup.centralizer (fixed : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutatorBot
  obtain ⟨ambientSylow, hcontained, hnormalizedAmbient⟩ := TwoActionSylowChoices.extend ambient acting htwo hnormalizesAmbient
    (fixed.subgroupOf ambient) (hfixedTwo.comap_subtype (K := ambient)) (by
      rw [Subgroup.map_subgroupOf_eq_of_le hfixedAmbient]
      exact hnormalized)
  let larger := (ambientSylow : Subgroup ambient).map ambient.subtype
  have hlargerAmbient : larger ≤ ambient := by
    rintro member ⟨lift, hlift, rfl⟩
    exact lift.property
  have hfixedLarger : fixed ≤ larger := by
    have hmap := Subgroup.map_mono (f := ambient.subtype) hcontained
    rw [Subgroup.map_subgroupOf_eq_of_le hfixedAmbient] at hmap
    exact hmap
  have hintersectionEq : intersection ⊓ larger = fixed := by
    have hlocalTwo : IsPGroup 2 (larger.subgroupOf intersection) :=
      (ambientSylow.isPGroup'.map ambient.subtype).comap_subtype
    have hlocalContained : (intersectionSylow : Subgroup intersection) ≤ larger.subgroupOf intersection := by
      intro member hmember
      apply hfixedLarger
      rw [hfixedEq]
      exact Subgroup.mem_map.mpr ⟨member, hmember, rfl⟩
    have heq := intersectionSylow.is_maximal' hlocalTwo hlocalContained
    apply le_antisymm _ (le_inf hfixedIntersection hfixedLarger)
    intro member hmember
    rw [hfixedEq]
    apply Subgroup.mem_map.mpr
    refine ⟨⟨member, hmember.1⟩, ?_, rfl⟩
    rw [← heq]
    exact hmember.2
  have hstrictImages : fixed < larger := by
    apply lt_of_le_of_ne hfixedLarger
    intro heq
    have hcard := congrArg (fun subgroup : Subgroup G => Nat.card subgroup) heq
    change Nat.card ((stabilizerSylow : Subgroup stabilizer).map stabilizer.subtype) =
      Nat.card ((ambientSylow : Subgroup ambient).map ambient.subtype) at hcard
    rw [← hsame, Subgroup.card_map_of_injective intersection.subtype_injective,
      Subgroup.card_map_of_injective ambient.subtype_injective] at hcard
    exact (ne_of_lt (hstrict intersectionSylow ambientSylow)) hcard
  obtain ⟨actor, hactor, houtside, hproductNormalizes⟩ := TwoActionStrictEmbedding.escape ambient acting intersection fixed larger
    hfixedLarger hlargerAmbient (ambientSylow.isPGroup'.map ambient.subtype) htwo hdisjoint hcentralizes hnormalizedAmbient
      hintersectionEq hstrictImages
  obtain ⟨homomorphism, hinjective⟩ := TwoActionDisplacementEmbedding.embedding ambient acting intersection fixed hfixedAmbient
    hdisjoint hnormalizesAmbient hcentralizes hcentralizers actor (hlargerAmbient hactor) houtside hproductNormalizes
  have hexists : ∃ homomorphism : acting →* Subgroup.center fixed, Function.Injective homomorphism :=
    ⟨homomorphism, hinjective⟩
  rw [hfixedEq] at hexists
  obtain ⟨transported, htransported⟩ := hexists
  exact TwoActionPrescribedSylowEmbedding.transport intersection intersectionSylow prescribed transported htransported

end CFSG.ComponentClassification.TwoActionOddStabilizerEmbedding
