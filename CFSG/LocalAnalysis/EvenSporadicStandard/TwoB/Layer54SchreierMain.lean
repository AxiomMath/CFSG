module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Layer54Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Layer54SchreierAbstract
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Layer54SchreierPerfect

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22
open CFSG.ComponentClassification.SemisimpleComponentStructure
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t z : G}

section Certified


theorem Level55.centPair_le_layer_of_normalizes (d : Level55 G t z)
    (hodd : CFSG.Open.standardComponentOddCore ↥(centZ z) = ⊥) (hP : Psub z = zpowers z)
    (hOut : ∀ i : ComponentIndex ↥(centZ z),
      Group.IsSolvable (ComponentClassification.OuterAutomorphisms.Outer ↥i.val))
    (hnorm : ∀ (i : ComponentIndex ↥(centZ z)) {k : G}, k ∈ centPair z t →
      ∀ {n : G}, n ∈ i.val.map (centZ z).subtype → k * n * k⁻¹ ∈ i.val.map (centZ z).subtype) :
    centPair z t ≤ (layer ↥(centZ z)).map (centZ z).subtype := by
  have hKC : centPair z t ≤ centZ z := centPair_le_centZ z t
  have hperf : ⁅(centPair z t).subgroupOf (centZ z), (centPair z t).subgroupOf (centZ z)⁆ =
      (centPair z t).subgroupOf (centZ z) := by
    apply Subgroup.map_injective (centZ z).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKC]
    exact d.commutator_centPair
  have hoddP : CFSG.pPrimeCore 2 ↥(centZ z) = ⊥ := by
    rw [← standardComponentOddCore_eq_pPrimeCore]
    exact hodd
  have hcen : ∀ c ∈ CFSG.pCore 2 ↥(centZ z), ∀ y : ↥(centZ z), c * y = y * c := by
    intro c hc y
    have h2 : (c : G) ∈ Psub z := (mem_pCore_iff_mem_O2In c).1 hc
    rw [hP] at h2
    exact Subtype.ext (commute_of_mem_zpowers_of_mem_centZ h2 y.2)
  have hn : ∀ i : ComponentIndex ↥(centZ z), ∀ k ∈ (centPair z t).subgroupOf (centZ z),
      ∀ m ∈ i.val, k * m * k⁻¹ ∈ i.val := by
    intro i k hk m hm
    obtain ⟨m', hm', hm'eq⟩ := hnorm i (mem_subgroupOf.1 hk) (n := (m : G)) ⟨m, hm, rfl⟩
    have : m' = k * m * k⁻¹ := Subtype.ext hm'eq
    rw [← this]
    exact hm'
  have hle := Layer54.le_layer_of_perfect_normalizes hperf hoddP hcen hOut hn
  intro g hg
  have hL := hle (mem_subgroupOf.2 hg : (⟨g, hKC hg⟩ : ↥(centZ z)) ∈
    (centPair z t).subgroupOf (centZ z))
  rw [← layer_eq_componentClassification] at hL
  exact ⟨⟨g, hKC hg⟩, hL, rfl⟩

end Certified

end CFSG.EvenSporadicStandard.TwoB
