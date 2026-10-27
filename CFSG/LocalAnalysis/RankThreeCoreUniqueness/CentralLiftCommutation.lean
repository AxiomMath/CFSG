module

public import CFSG.Open.LocalVocabulary

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem perfect_subgroup_central_commutator_eq_bot
    {G : Type*} [Group G] (perfectGroup otherGroup : Subgroup G)
    (hperfect : Group.IsPerfect perfectGroup)
    (hcentral : ⁅perfectGroup, otherGroup⁆ ≤ Subgroup.center G) :
    ⁅perfectGroup, otherGroup⁆ = ⊥ := by
  let : Group.IsPerfect perfectGroup := hperfect
  have hfirst : ⁅⁅perfectGroup, otherGroup⁆, perfectGroup⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.commutator_mono hcentral le_top).trans
      (Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr le_rfl).le
  have hsecond : ⁅⁅otherGroup, perfectGroup⁆, perfectGroup⁆ = ⊥ := by
    rwa [Subgroup.commutator_comm otherGroup perfectGroup]
  have hrotated : ⁅⁅perfectGroup, perfectGroup⁆, otherGroup⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate hfirst hsecond
  rwa [Subgroup.commutator_eq_self] at hrotated

theorem perfect_lift_commutes_of_commuting_image
    {G Image : Type*} [Group G] [Group Image]
    (homomorphism : G →* Image) (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (perfectGroup otherGroup : Subgroup G) (hperfect : Group.IsPerfect perfectGroup)
    (himage : Subgroup.map homomorphism perfectGroup ≤
      Subgroup.centralizer (Subgroup.map homomorphism otherGroup : Set Image)) :
    perfectGroup ≤ Subgroup.centralizer (otherGroup : Set G) := by
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
  apply perfect_subgroup_central_commutator_eq_bot perfectGroup otherGroup hperfect
  apply le_trans _ hcentral
  have hmapped : Subgroup.map homomorphism ⁅perfectGroup, otherGroup⁆ = ⊥ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr himage
  intro element helement
  exact Subgroup.mem_bot.mp (hmapped ▸ Subgroup.mem_map_of_mem homomorphism helement)

theorem perfect_subgroup_normalized_centralizing_images_commute
    {G Image : Type*} [Group G] [Group Image]
    (homomorphism : G →* Image) (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (perfectGroup : Subgroup G) (hperfect : Group.IsPerfect perfectGroup) :
    Subgroup.comap homomorphism
      (Subgroup.centralizer (Subgroup.map homomorphism perfectGroup : Set Image)) ≤
        Subgroup.centralizer (perfectGroup : Set G) := by
  let otherGroup := Subgroup.comap homomorphism
    (Subgroup.centralizer (Subgroup.map homomorphism perfectGroup : Set Image))
  have himage : Subgroup.map homomorphism otherGroup ≤
      Subgroup.centralizer (Subgroup.map homomorphism perfectGroup : Set Image) := by
    rintro element ⟨preimage, hpreimage, rfl⟩
    exact hpreimage
  have hcommutes : Subgroup.map homomorphism perfectGroup ≤
      Subgroup.centralizer (Subgroup.map homomorphism otherGroup : Set Image) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr himage
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (perfect_lift_commutes_of_commuting_image homomorphism hcentral perfectGroup otherGroup
      hperfect hcommutes)

end CFSG.RankThreeCoreUniqueness.Helpers
