module

public import CFSG.ClassicalInvolution.Q3.Q3WL65
public import CFSG.ClassicalInvolution.WeakCT.TwistedTransport
public import CFSG.ClassicalInvolution.Q3.Q3WStd
public import CFSG.ClassicalInvolution.RouteD.LocalMembers
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

@[expose] def LocalOddThreeFree3 {G : Type} [Group G] (Ω : Set (Subgroup G)) (x : G) : Prop :=
  ¬ 3 ∣ Nat.card (classicalInvolutionOddCore ↥(locLayer Ω x))

theorem card_gf3 : Nat.card (GaloisField 3 1) = 3 := by
  rw [GaloisField.card 3 1 one_ne_zero]
  norm_num

theorem odd_gf3 : Odd (Nat.card (GaloisField 3 1)) := by
  rw [card_gf3]
  decide

theorem card_sl2_gf3 : Nat.card SL(2, GaloisField 3 1) = 24 := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, card_gf3]
  norm_num

theorem two_ne_zero_gf3 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_of_odd_natCard odd_gf3

theorem linearBlockStandardPair_of_locImg3' {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {x : G} (hP1 : LocalOddCentral Ω {x})
    (hO3 : LocalOddThreeFree3 Ω x) {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (hL' : L' ∈ centralizingMembers Ω {x}) {W : Subgroup (locQuot Ω x)}
    (h : LinearBlockStandardPair (GaloisField 3 1) W (locImg Ω x L) (locImg Ω x L')) :
    ∃ W' : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W' L L' := by
  obtain ⟨e⟩ := nonempty_ringEquiv_zmod_three (card_gf3)
  obtain ⟨W', hW'⟩ := linearBlockStandardPair_of_locImg3 hΩ hex hP1 hO3 hL hL'
    (WeakCT.LinearBlockStandardPair.of_ringEquiv e h)
  exact ⟨W', WeakCT.LinearBlockStandardPair.of_ringEquiv e.symm hW'⟩

section Members

variable {G : Type} [Group G]

theorem card_locImg3 [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    {x : G} {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x}) :
    Nat.card (locImg Ω x L) = 24 := by
  obtain ⟨z, hz⟩ := hΩ.classical L hL.1
  have hLY := le_centralizingLayer hL
  let e := Subgroup.subgroupOfEquivOfLe hLY
  have hO : classicalInvolutionOddCore (L.subgroupOf (locLayer Ω x)) = ⊥ := by
    have h1 : Subgroup.map e.toMonoidHom
        (classicalInvolutionOddCore (L.subgroupOf (locLayer Ω x))) =
        classicalInvolutionOddCore ↥L :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    rw [hex L hL.1] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  have hinf := inf_oddCore_eq_bot hO
  unfold locImg
  rw [card_map_of_inf_ker_eq_bot _ _ (by rwa [QuotientGroup.ker_mk'])]
  rw [Nat.card_congr e.toEquiv]
  obtain ⟨e'⟩ := hz.nonempty_equiv_sl2 (hex L hL.1)
  rw [Nat.card_congr e'.toEquiv]
  exact natCard_sl2Three

theorem commutes_of_commutes_locImg3 [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω)
    (hex : ExactMembers3 Ω) {x : G} (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (hL' : L' ∈ centralizingMembers Ω {x}) (h : Commutes (locImg Ω x L) (locImg Ω x L')) :
    Commutes L L' := by
  obtain ⟨z, hz⟩ := hΩ.classical L hL.1
  have hLY := le_centralizingLayer hL
  obtain ⟨e⟩ := hz.nonempty_equiv_sl2 (hex L hL.1)
  have hK : Nonempty (↥(L.subgroupOf (locLayer Ω x)) ≃* SL(2, ZMod 3)) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hLY).trans e⟩
  have hbot := commutes_of_equiv_sl2Three hP1 hO3 hK (L := L'.subgroupOf (locLayer Ω x))
    (fun a ha b hb => by
      rw [← QuotientGroup.eq_one_iff (N := classicalInvolutionOddCore ↥(locLayer Ω x))]
      change QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⁅a, b⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact h _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩)
  intro a ha b hb
  have := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
  have h1 := Subgroup.mem_centralizer_iff.mp
    (this (Subgroup.mem_subgroupOf.mpr ha : (⟨a, hLY ha⟩ : ↥(locLayer Ω x)) ∈
      L.subgroupOf (locLayer Ω x))) ⟨b, le_centralizingLayer hL' hb⟩
    (Subgroup.mem_subgroupOf.mpr hb)
  exact (congrArg Subtype.val h1).symm

end Members

end CFSG.ClassicalInvolution.Q3.Q3W
