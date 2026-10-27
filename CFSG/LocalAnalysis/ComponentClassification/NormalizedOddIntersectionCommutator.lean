module

public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.Assembly.Defs

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.ComponentClassification.NormalizedOddIntersectionCommutator

theorem le_core {G : Type*} [Group G] [Finite G]
    (first second overgroup acting : Subgroup G)
    (hsecond : second ≤ overgroup) (hacting : acting ≤ second)
    (hnormalizesFirst : acting ≤ Subgroup.normalizer (first : Set G))
    (hnormalizesSecond : first ⊓ overgroup ≤ Subgroup.normalizer (second : Set G))
    (hodd : Odd (Nat.card ↥(first ⊓ second))) :
    ⁅acting, first ⊓ overgroup⁆ ≤
      (componentClassificationOddCore ↥(first ⊓ overgroup)).map (first ⊓ overgroup).subtype := by
  let intersection := first ⊓ overgroup
  let overlap := first ⊓ second
  have hle : overlap ≤ intersection := inf_le_inf_left first hsecond
  have hnormal : (overlap.subgroupOf intersection).Normal := by
    apply (Subgroup.normal_subgroupOf_iff hle).mpr
    intro member actor hmember hactor
    exact ⟨first.mul_mem (first.mul_mem hactor.1 hmember.1) (first.inv_mem hactor.1),
      (Subgroup.mem_normalizer_iff.mp (hnormalizesSecond hactor) member).mp hmember.2⟩
  have hoddLocal : Odd (Nat.card (overlap.subgroupOf intersection)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact hodd
  have hcore := Subgroup.map_mono (f := intersection.subtype)
    (OddCore.maximal intersection (overlap.subgroupOf intersection) hnormal hoddLocal)
  rw [Subgroup.map_subgroupOf_eq_of_le hle] at hcore
  apply le_trans _ hcore
  apply Subgroup.commutator_le.mpr
  intro member hmember actor hactor
  have hfirstConjugate := (Subgroup.mem_normalizer_iff.mp (hnormalizesFirst hmember) actor).mp hactor.1
  have hsecondConjugate := (Subgroup.mem_normalizer_iff.mp (hnormalizesSecond hactor) member⁻¹).mp
    (second.inv_mem (hacting hmember))
  refine ⟨first.mul_mem hfirstConjugate (first.inv_mem hactor.1), ?_⟩
  change member * actor * member⁻¹ * actor⁻¹ ∈ second
  simpa only [mul_assoc] using second.mul_mem (hacting hmember) hsecondConjugate

end CFSG.ComponentClassification.NormalizedOddIntersectionCommutator
