module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCoverFamilyPieces
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCoverCT

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.Quasithin (perfectCore)

local instance e6PilotCoverFamilyNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section Entrywise


variable {K : Type} [Field K]

@[expose] noncomputable def leviEntrywise (ρ : K →+* K) (J : Finset (Fin (Tag.rank .E6))) :
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J →*
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J :=
  ((adjointBaseChangeHom .E6 ρ).comp
    (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J).subtype).codRestrict _ fun y => by
    obtain ⟨y', hy'⟩ := exists_levi_adjDatumE6_baseChangeGL ρ y.2
    have h1 : adjointBaseChangeHom .E6 ρ y = y' :=
      Subtype.ext (by rw [coe_adjointBaseChangeHom]; exact hy'.symm)
    rw [MonoidHom.comp_apply, coe_subtype, h1]
    exact y'.2

theorem coe_leviEntrywise (ρ : K →+* K) (J : Finset (Fin (Tag.rank .E6)))
    (y : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J) :
    (((leviEntrywise ρ J y : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J) :
      adjointGroup .E6 K) : ModGL .E6 K) =
        baseChangeGL ρ ((y : adjointGroup .E6 K) : ModGL .E6 K) := by
  rw [leviEntrywise, MonoidHom.codRestrict_apply]
  rfl

theorem leviEntrywise_surjective (ρ : K ≃+* K) (J : Finset (Fin (Tag.rank .E6))) :
    Function.Surjective (leviEntrywise (ρ : K →+* K) J) := by
  intro z
  refine ⟨leviEntrywise (ρ.symm : K →+* K) J z, Subtype.ext (Subtype.ext ?_)⟩
  rw [coe_leviEntrywise, coe_leviEntrywise, F4Pilot.baseChangeGL_baseChangeGL,
    show (ρ : K →+* K).comp (ρ.symm : K →+* K) = RingHom.id K from
      RingHom.ext fun c => ρ.apply_symm_apply c, baseChangeGL_id]

theorem leviEntrywise_eq_self {σ : K ≃+* K} {ρ : K ≃+* K} (hρ : ∀ c : fixSubfield σ, ρ c = c)
    {J : Finset (Fin (Tag.rank .E6))} (y : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J)
    {x : adjointGroup .E6 (fixSubfield σ)}
    (hxy : ((y : adjointGroup .E6 K) : ModGL .E6 K) =
      baseChangeGL (fixSubfield σ).subtype (x : ModGL .E6 (fixSubfield σ))) :
    leviEntrywise (ρ : K →+* K) J y = y := by
  refine Subtype.ext (Subtype.ext ?_)
  have hcomp : (ρ : K →+* K).comp (fixSubfield σ).subtype = (fixSubfield σ).subtype :=
    RingHom.ext fun c => hρ c
  rw [coe_leviEntrywise, hxy, F4Pilot.baseChangeGL_baseChangeGL, hcomp]

end Entrywise

section Family


variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

theorem four_not_mem_one_E6 : (4 : Fin (Tag.rank .E6)) ∉ ({1} : Finset (Fin (Tag.rank .E6))) := by
  decide

theorem five_not_mem_one_E6 : (5 : Fin (Tag.rank .E6)) ∉ ({1} : Finset (Fin (Tag.rank .E6))) := by
  decide

theorem one_not_mem_of {j : Fin (Tag.rank .E6)} (hj : j = 4 ∨ j = 5) :
    (1 : Fin (Tag.rank .E6)) ∉ ({j} : Finset (Fin (Tag.rank .E6))) := by
  rcases hj with rfl | rfl <;> decide

variable (sH : ∀ J : Finset (Fin (Tag.rank .E6)), (1 : Fin (Tag.rank .E6)) ∉ J → J.card ≤ 2 →
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J →* neighbourCore e .high)
  (sS : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup E6Neighbour.six.nodes →*
    neighbourCore e .six) (ρ : K ≃+* K)

@[expose] noncomputable def highLiftE6 {J : Finset (Fin (Tag.rank .E6))}
    (h1 : (1 : Fin (Tag.rank .E6)) ∉ J) (hJ2 : J.card ≤ 2) :
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J →* G :=
  (neighbourCore e .high).subtype.comp (sH J h1 hJ2)

@[expose] noncomputable def sixLiftE6 {J : Finset (Fin (Tag.rank .E6))}
    (h4 : (4 : Fin (Tag.rank .E6)) ∉ J) (h5 : (5 : Fin (Tag.rank .E6)) ∉ J) :
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J →* G :=
  (neighbourCore e .six).subtype.comp (sS.comp ((leviIncl (subset_nodes_six_of_not_mem h4 h5)).comp
    (leviEntrywise (ρ : K →+* K) J)))

@[expose] noncomputable def coverPairLiftE6 {j : Fin (Tag.rank .E6)} (hj : j = 4 ∨ j = 5)
    (hc : ∀ a b, Commute (sixLiftE6 sS ρ four_not_mem_one_E6 five_not_mem_one_E6 a)
      (highLiftE6 sH (one_not_mem_of hj) (by simp) b)) :
    ↥(CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1} ⊔
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j}) →* G :=
  F4Pilot.supLift (commute_adLevi_one hj) (adLevi_one_inf_eq_bot hj) _ _ hc

theorem coverPairLiftE6_of_mem_left {j : Fin (Tag.rank .E6)} (hj : j = 4 ∨ j = 5)
    (hc : ∀ a b, Commute (sixLiftE6 sS ρ four_not_mem_one_E6 five_not_mem_one_E6 a)
      (highLiftE6 sH (one_not_mem_of hj) (by simp) b))
    (z : ↥(CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1} ⊔
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j}))
    (hz : (z : adjointGroup .E6 K) ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1}) :
    coverPairLiftE6 sH sS ρ hj hc z =
      sixLiftE6 sS ρ four_not_mem_one_E6 five_not_mem_one_E6 ⟨z, hz⟩ := by
  obtain ⟨z, -⟩ := z
  exact F4Pilot.supLift_apply_left (commute_adLevi_one hj) (adLevi_one_inf_eq_bot hj) hc ⟨z, hz⟩

theorem coverPairLiftE6_of_mem_right {j : Fin (Tag.rank .E6)} (hj : j = 4 ∨ j = 5)
    (hc : ∀ a b, Commute (sixLiftE6 sS ρ four_not_mem_one_E6 five_not_mem_one_E6 a)
      (highLiftE6 sH (one_not_mem_of hj) (by simp) b))
    (z : ↥(CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1} ⊔
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j}))
    (hz : (z : adjointGroup .E6 K) ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j}) :
    coverPairLiftE6 sH sS ρ hj hc z = highLiftE6 sH (one_not_mem_of hj) (by simp) ⟨z, hz⟩ := by
  obtain ⟨z, -⟩ := z
  exact F4Pilot.supLift_apply_right (commute_adLevi_one hj) (adLevi_one_inf_eq_bot hj) hc ⟨z, hz⟩

theorem card_singleton_le_two_E6 (j : Fin (Tag.rank .E6)) :
    ({j} : Finset (Fin (Tag.rank .E6))).card ≤ 2 := by
  rw [Finset.card_singleton]; omega

variable (hc4 : ∀ a b, Commute (sixLiftE6 sS ρ four_not_mem_one_E6 five_not_mem_one_E6 a)
    (highLiftE6 sH (one_not_mem_of four_cases) (card_singleton_le_two_E6 4) b))
  (hc5 : ∀ a b, Commute (sixLiftE6 sS ρ four_not_mem_one_E6 five_not_mem_one_E6 a)
    (highLiftE6 sH (one_not_mem_of five_cases) (card_singleton_le_two_E6 5) b))

@[expose] noncomputable def coverFamilyE6
    (J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2}) :
    (adjDatumE6 K).leviAmalgam J →* G :=
  if h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1 then
    if h4 : (4 : Fin (Tag.rank .E6)) ∈ J.1 then
      (coverPairLiftE6 sH sS ρ four_cases hc4).comp
        (Subgroup.inclusion (adLevi_le_pair J.2 four_cases h1 h4))
    else if h5 : (5 : Fin (Tag.rank .E6)) ∈ J.1 then
      (coverPairLiftE6 sH sS ρ five_cases hc5).comp
        (Subgroup.inclusion (adLevi_le_pair J.2 five_cases h1 h5))
    else sixLiftE6 sS ρ h4 h5
  else highLiftE6 sH h1 J.2

variable {sH sS ρ hc4 hc5}

theorem coverFamilyE6_of_one_not_mem
    {J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2}}
    (h1 : (1 : Fin (Tag.rank .E6)) ∉ J.1) (x : (adjDatumE6 K).leviAmalgam J) :
    coverFamilyE6 sH sS ρ hc4 hc5 J x = highLiftE6 sH h1 J.2 x := by
  rw [coverFamilyE6, dite_eq_right h1]

theorem coverFamilyE6_of_six {J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2}}
    (h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1) (h4 : (4 : Fin (Tag.rank .E6)) ∉ J.1)
    (h5 : (5 : Fin (Tag.rank .E6)) ∉ J.1) (x : (adjDatumE6 K).leviAmalgam J) :
    coverFamilyE6 sH sS ρ hc4 hc5 J x = sixLiftE6 sS ρ h4 h5 x := by
  rw [coverFamilyE6, dite_eq_left h1, dite_eq_right h4, dite_eq_right h5]

theorem coverFamilyE6_of_four {J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2}}
    (h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1) (h4 : (4 : Fin (Tag.rank .E6)) ∈ J.1)
    (x : (adjDatumE6 K).leviAmalgam J) :
    coverFamilyE6 sH sS ρ hc4 hc5 J x =
      coverPairLiftE6 sH sS ρ four_cases hc4 ⟨x, adLevi_le_pair J.2 four_cases h1 h4 x.2⟩ := by
  rw [coverFamilyE6, dite_eq_left h1, dite_eq_left h4]
  rfl

theorem coverFamilyE6_of_five {J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2}}
    (h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1) (h4 : (4 : Fin (Tag.rank .E6)) ∉ J.1)
    (h5 : (5 : Fin (Tag.rank .E6)) ∈ J.1) (x : (adjDatumE6 K).leviAmalgam J) :
    coverFamilyE6 sH sS ρ hc4 hc5 J x =
      coverPairLiftE6 sH sS ρ five_cases hc5 ⟨x, adLevi_le_pair J.2 five_cases h1 h5 x.2⟩ := by
  rw [coverFamilyE6, dite_eq_left h1, dite_eq_right h4, dite_eq_left h5]
  rfl

end Family

section Compat


variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}
  {h : FieldNeighbourCover σ e .high}
  {sH : ∀ J : Finset (Fin (Tag.rank .E6)), (1 : Fin (Tag.rank .E6)) ∉ J → J.card ≤ 2 →
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J →* neighbourCore e .high}
  {sS : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup E6Neighbour.six.nodes →*
    neighbourCore e .six} {ρ : K ≃+* K}
  {hc4 : ∀ a b, Commute (sixLiftE6 sS ρ four_not_mem_one_E6 five_not_mem_one_E6 a)
    (highLiftE6 sH (one_not_mem_of four_cases) (card_singleton_le_two_E6 4) b)}
  {hc5 : ∀ a b, Commute (sixLiftE6 sS ρ four_not_mem_one_E6 five_not_mem_one_E6 a)
    (highLiftE6 sH (one_not_mem_of five_cases) (card_singleton_le_two_E6 5) b)}

theorem highLiftE6_eq (hH : ∀ J h1 hJ2, IsCoverPiece h (subset_nodes_high_of_one_not_mem h1)
      (sH J h1 hJ2)) (hq : 4 ≤ Nat.card (fixSubfield σ)) {I J : Finset (Fin (Tag.rank .E6))}
    (hIJ : I ⊆ J) (hI1 : (1 : Fin (Tag.rank .E6)) ∉ I) (hJ1 : (1 : Fin (Tag.rank .E6)) ∉ J)
    (hI2 : I.card ≤ 2) (hJ2 : J.card ≤ 2)
    (x : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup I)
    (y : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J)
    (hxy : (x : adjointGroup .E6 K) = y) :
    highLiftE6 sH hI1 hI2 x = highLiftE6 sH hJ1 hJ2 y := by
  have h1 := (hH I hI1 hI2).eq_of_subset (hH J hJ1 hJ2) hq (subset_refl I) hIJ hI2 x
  have hx : leviIncl (subset_refl I) x = x := Subtype.ext (coe_leviIncl _ x)
  have hy : leviIncl hIJ x = y := Subtype.ext ((coe_leviIncl _ x).trans hxy)
  rw [hx, hy] at h1
  change ((sH I hI1 hI2 x : neighbourCore e .high) : G) =
    ((sH J hJ1 hJ2 y : neighbourCore e .high) : G)
  rw [h1]

theorem sixLiftE6_eq {I J : Finset (Fin (Tag.rank .E6))}
    (hI4 : (4 : Fin (Tag.rank .E6)) ∉ I) (hI5 : (5 : Fin (Tag.rank .E6)) ∉ I)
    (hJ4 : (4 : Fin (Tag.rank .E6)) ∉ J) (hJ5 : (5 : Fin (Tag.rank .E6)) ∉ J)
    (x : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup I)
    (y : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J)
    (hxy : (x : adjointGroup .E6 K) = y) :
    sixLiftE6 sS ρ hI4 hI5 x = sixLiftE6 sS ρ hJ4 hJ5 y := by
  change ((sS _ : neighbourCore e .six) : G) = ((sS _ : neighbourCore e .six) : G)
  congr 2
  refine Subtype.ext (Subtype.ext ?_)
  simp only [MonoidHom.comp_apply]
  rw [coe_leviIncl, coe_leviIncl, coe_leviEntrywise, coe_leviEntrywise, hxy]

theorem isCompatible_coverFamilyE6
    (hH : ∀ J h1 hJ2, IsCoverPiece h (subset_nodes_high_of_one_not_mem h1) (sH J h1 hJ2))
    (hq : 4 ≤ Nat.card (fixSubfield σ))
    (hagree : ∀ {I : Finset (Fin (Tag.rank .E6))} (hI1 : (1 : Fin (Tag.rank .E6)) ∉ I)
      (hI2 : I.card ≤ 2), I ⊆ {0, 2, 3} →
      ∀ (x : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup I)
        (z : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup E6Neighbour.six.nodes),
        ((z : adjointGroup .E6 K) : ModGL .E6 K) =
          baseChangeGL (ρ : K →+* K) ((x : adjointGroup .E6 K) : ModGL .E6 K) →
        highLiftE6 sH hI1 hI2 x = ((sS z : neighbourCore e .six) : G)) :
    IsCompatible (adjDatumE6 K).leviAmalgam (coverFamilyE6 sH sS ρ hc4 hc5) := by
  intro i j hij x y hxy
  have hsub : (i.1 : Finset (Fin (Tag.rank .E6))) ⊆ j.1 := hij
  have hmono : ∀ {I : Finset (Fin (Tag.rank .E6))}, (i.1 : Finset (Fin (Tag.rank .E6))) ⊆ I →
      (y : adjointGroup .E6 K) ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup I :=
    fun h => hxy ▸ CFSG.LieType.CurtisTits.levi_mono (adjDatumE6 K).rootGroup h x.2
  by_cases h1j : (1 : Fin (Tag.rank .E6)) ∈ j.1
  · by_cases h4j : (4 : Fin (Tag.rank .E6)) ∈ j.1
    ·
      have hj : (j.1 : Finset (Fin (Tag.rank .E6))) = {1, 4} :=
        eq_pair_of_card_le_two j.2 (one_ne_of four_cases) h1j h4j
      have hij' : ∀ a ∈ i.1, a = 1 ∨ a = 4 := fun a ha => by
        have := hsub ha
        rw [hj, Finset.mem_insert, Finset.mem_singleton] at this
        exact this
      rw [coverFamilyE6_of_four h1j h4j]
      by_cases h1i : (1 : Fin (Tag.rank .E6)) ∈ i.1
      · by_cases h4i : (4 : Fin (Tag.rank .E6)) ∈ i.1
        · rw [coverFamilyE6_of_four h1i h4i]
          exact congrArg _ (Subtype.ext hxy)
        · have h5i : (5 : Fin (Tag.rank .E6)) ∉ i.1 := fun h => by
            rcases hij' 5 h with h' | h'
            exacts [five_ne_one_E6 h', five_ne_four_E6 h']
          have hi1 : (i.1 : Finset (Fin (Tag.rank .E6))) ⊆ {1} := fun a ha => by
            rcases hij' a ha with rfl | rfl
            · exact Finset.mem_singleton_self _
            · exact absurd ha h4i
          rw [coverFamilyE6_of_six h1i h4i h5i,
            coverPairLiftE6_of_mem_left _ _ _ _ hc4 _ (hmono hi1)]
          exact sixLiftE6_eq _ _ _ _ x _ hxy
      · have hi4 : (i.1 : Finset (Fin (Tag.rank .E6))) ⊆ {4} := fun a ha => by
          rcases hij' a ha with rfl | rfl
          · exact absurd ha h1i
          · exact Finset.mem_singleton_self _
        rw [coverFamilyE6_of_one_not_mem h1i,
          coverPairLiftE6_of_mem_right _ _ _ _ hc4 _ (hmono hi4)]
        exact highLiftE6_eq hH hq hi4 h1i _ i.2 _ x _ hxy
    · have h4i : (4 : Fin (Tag.rank .E6)) ∉ i.1 := fun h => h4j (hsub h)
      by_cases h5j : (5 : Fin (Tag.rank .E6)) ∈ j.1
      ·
        have hj : (j.1 : Finset (Fin (Tag.rank .E6))) = {1, 5} :=
          eq_pair_of_card_le_two j.2 (one_ne_of five_cases) h1j h5j
        have hij' : ∀ a ∈ i.1, a = 1 ∨ a = 5 := fun a ha => by
          have := hsub ha
          rw [hj, Finset.mem_insert, Finset.mem_singleton] at this
          exact this
        rw [coverFamilyE6_of_five h1j h4j h5j]
        by_cases h1i : (1 : Fin (Tag.rank .E6)) ∈ i.1
        · by_cases h5i : (5 : Fin (Tag.rank .E6)) ∈ i.1
          · rw [coverFamilyE6_of_five h1i h4i h5i]
            exact congrArg _ (Subtype.ext hxy)
          · have hi1 : (i.1 : Finset (Fin (Tag.rank .E6))) ⊆ {1} := fun a ha => by
              rcases hij' a ha with rfl | rfl
              · exact Finset.mem_singleton_self _
              · exact absurd ha h5i
            rw [coverFamilyE6_of_six h1i h4i h5i,
              coverPairLiftE6_of_mem_left _ _ _ _ hc5 _ (hmono hi1)]
            exact sixLiftE6_eq _ _ _ _ x _ hxy
        · have hi5 : (i.1 : Finset (Fin (Tag.rank .E6))) ⊆ {5} := fun a ha => by
            rcases hij' a ha with rfl | rfl
            · exact absurd ha h1i
            · exact Finset.mem_singleton_self _
          rw [coverFamilyE6_of_one_not_mem h1i,
            coverPairLiftE6_of_mem_right _ _ _ _ hc5 _ (hmono hi5)]
          exact highLiftE6_eq hH hq hi5 h1i _ i.2 _ x _ hxy
      ·
        have h5i : (5 : Fin (Tag.rank .E6)) ∉ i.1 := fun h => h5j (hsub h)
        rw [coverFamilyE6_of_six h1j h4j h5j]
        by_cases h1i : (1 : Fin (Tag.rank .E6)) ∈ i.1
        · rw [coverFamilyE6_of_six h1i h4i h5i]
          exact sixLiftE6_eq _ _ _ _ x y hxy
        · rw [coverFamilyE6_of_one_not_mem h1i]
          refine hagree h1i i.2 (subset_a3Nodes_of_not_mem h1i h4i h5i) x _ ?_
          simp only [MonoidHom.comp_apply]
          rw [coe_leviIncl, coe_leviEntrywise, hxy]
  · have h1i : (1 : Fin (Tag.rank .E6)) ∉ i.1 := fun h => h1j (hsub h)
    rw [coverFamilyE6_of_one_not_mem h1i, coverFamilyE6_of_one_not_mem h1j]
    exact highLiftE6_eq hH hq hsub h1i h1j i.2 j.2 x y hxy

theorem highLiftE6_fix
    (hH : ∀ J h1 hJ2, IsCoverPiece h (subset_nodes_high_of_one_not_mem h1) (sH J h1 hJ2))
    (hq : 4 ≤ Nat.card (fixSubfield σ)) {J : Finset (Fin (Tag.rank .E6))}
    (h1 : (1 : Fin (Tag.rank .E6)) ∉ J) (hJ2 : J.card ≤ 2) {x : adjointGroup .E6 (fixSubfield σ)}
    (hx : x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 (fixSubfield σ)).rootGroup J)
    (y : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J)
    (hxy : ((y : adjointGroup .E6 K) : ModGL .E6 K) =
      baseChangeGL (fixSubfield σ).subtype (x : ModGL .E6 (fixSubfield σ))) :
    highLiftE6 sH h1 hJ2 y = ((e.symm x : L) : G) :=
  (hH J h1 hJ2).fix hq hx y hxy

theorem sixLiftE6_fix
    (hS : IsCoverPiece (h.toNeighbour .six) (subset_refl E6Neighbour.six.nodes) sS)
    (hρ : ∀ c : fixSubfield σ, ρ c = c) (hq : 4 ≤ Nat.card (fixSubfield σ))
    {J : Finset (Fin (Tag.rank .E6))} (h4 : (4 : Fin (Tag.rank .E6)) ∉ J)
    (h5 : (5 : Fin (Tag.rank .E6)) ∉ J) {x : adjointGroup .E6 (fixSubfield σ)}
    (hx : x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 (fixSubfield σ)).rootGroup J)
    (y : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J)
    (hxy : ((y : adjointGroup .E6 K) : ModGL .E6 K) =
      baseChangeGL (fixSubfield σ).subtype (x : ModGL .E6 (fixSubfield σ))) :
    sixLiftE6 sS ρ h4 h5 y = ((e.symm x : L) : G) := by
  change ((sS (leviIncl (subset_nodes_six_of_not_mem h4 h5)
    (leviEntrywise (ρ : K →+* K) J y)) : neighbourCore e .six) : G) = _
  rw [leviEntrywise_eq_self hρ y hxy]
  refine hS.fix hq (CFSG.LieType.CurtisTits.levi_mono (adjDatumE6 (fixSubfield σ)).rootGroup
    (subset_nodes_six_of_not_mem h4 h5) hx) _ ?_
  rw [coe_leviIncl, hxy]

theorem range_coverFamilyE6
    (hH : ∀ J h1 hJ2, IsCoverPiece h (subset_nodes_high_of_one_not_mem h1) (sH J h1 hJ2))
    (hS : IsCoverPiece (h.toNeighbour .six) (subset_refl E6Neighbour.six.nodes) sS)
    (hq : 4 ≤ Nat.card (fixSubfield σ))
    (hpair : ∀ {j : Fin (Tag.rank .E6)}, j = 4 ∨ j = 5 →
      pieceCore e {1, j} = pieceCore e {1} ⊔ pieceCore e {j})
    (J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2}) :
    (coverFamilyE6 sH sS ρ hc4 hc5 J).range = pieceCore e J.1 := by
  have hsix : ∀ {I : Finset (Fin (Tag.rank .E6))} (h4 : (4 : Fin (Tag.rank .E6)) ∉ I)
      (h5 : (5 : Fin (Tag.rank .E6)) ∉ I), I.card ≤ 2 →
      (sixLiftE6 sS ρ h4 h5).range = pieceCore e I := by
    intro I h4 h5 hI2
    have hr : (sixLiftE6 sS ρ h4 h5).range =
        ((neighbourCore e .six).subtype.comp (sS.comp (leviIncl
          (subset_nodes_six_of_not_mem h4 h5)))).range := by
      change (((neighbourCore e .six).subtype.comp (sS.comp (leviIncl
        (subset_nodes_six_of_not_mem h4 h5)))).comp (leviEntrywise (ρ : K →+* K) I)).range = _
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (leviEntrywise_surjective ρ I),
        ← MonoidHom.range_eq_map]
    rw [hr]
    exact (hS.restrict (subset_nodes_six_of_not_mem h4 h5)).range_eq_pieceCore hq hI2
  have hhigh : ∀ {I : Finset (Fin (Tag.rank .E6))} (h1 : (1 : Fin (Tag.rank .E6)) ∉ I)
      (hI2 : I.card ≤ 2), (highLiftE6 sH h1 hI2).range = pieceCore e I :=
    fun h1 hI2 => (hH _ h1 hI2).range_eq_pieceCore hq hI2
  have hpairr : ∀ {j : Fin (Tag.rank .E6)} (hj : j = 4 ∨ j = 5)
      (hc : ∀ a b, Commute (sixLiftE6 sS ρ four_not_mem_one_E6 five_not_mem_one_E6 a)
        (highLiftE6 sH (one_not_mem_of hj) (by simp) b))
      (h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1) (hjJ : j ∈ J.1),
      (coverFamilyE6 sH sS ρ hc4 hc5 J).range = (coverPairLiftE6 sH sS ρ hj hc).range →
      (coverFamilyE6 sH sS ρ hc4 hc5 J).range = pieceCore e J.1 := by
    intro j hj hc h1 hjJ hrange
    rw [hrange, coverPairLiftE6, F4Pilot.range_supLift, hsix _ _ (by simp),
      hhigh _ (by simp), ← hpair hj, eq_pair_of_card_le_two J.2 (one_ne_of hj) h1 hjJ]
  by_cases h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1
  · by_cases h4 : (4 : Fin (Tag.rank .E6)) ∈ J.1
    · refine hpairr four_cases hc4 h1 h4 (le_antisymm ?_ ?_)
      · rintro _ ⟨x, rfl⟩
        rw [coverFamilyE6_of_four h1 h4]
        exact ⟨_, rfl⟩
      · rintro _ ⟨z, rfl⟩
        have hz : (z : adjointGroup .E6 K) ∈
            CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J.1 := by
          rw [eq_pair_of_card_le_two J.2 (one_ne_of four_cases) h1 h4, F4Pilot.levi_pair]
          exact z.2
        exact ⟨⟨z, hz⟩, by rw [coverFamilyE6_of_four h1 h4]⟩
    · by_cases h5 : (5 : Fin (Tag.rank .E6)) ∈ J.1
      · refine hpairr five_cases hc5 h1 h5 (le_antisymm ?_ ?_)
        · rintro _ ⟨x, rfl⟩
          rw [coverFamilyE6_of_five h1 h4 h5]
          exact ⟨_, rfl⟩
        · rintro _ ⟨z, rfl⟩
          have hz : (z : adjointGroup .E6 K) ∈
              CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J.1 := by
            rw [eq_pair_of_card_le_two J.2 (one_ne_of five_cases) h1 h5, F4Pilot.levi_pair]
            exact z.2
          exact ⟨⟨z, hz⟩, by rw [coverFamilyE6_of_five h1 h4 h5]⟩
      · have hφ : coverFamilyE6 sH sS ρ hc4 hc5 J = sixLiftE6 sS ρ h4 h5 :=
          MonoidHom.ext fun x => coverFamilyE6_of_six h1 h4 h5 x
        rw [hφ, hsix h4 h5 J.2]
  · have hφ : coverFamilyE6 sH sS ρ hc4 hc5 J = highLiftE6 sH h1 J.2 :=
      MonoidHom.ext fun x => coverFamilyE6_of_one_not_mem h1 x
    rw [hφ, hhigh h1 J.2]

theorem fix_coverFamilyE6
    (hH : ∀ J h1 hJ2, IsCoverPiece h (subset_nodes_high_of_one_not_mem h1) (sH J h1 hJ2))
    (hS : IsCoverPiece (h.toNeighbour .six) (subset_refl E6Neighbour.six.nodes) sS)
    (hρ : ∀ c : fixSubfield σ, ρ c = c) (hq : 4 ≤ Nat.card (fixSubfield σ))
    (J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2})
    (x : adjointGroup .E6 (fixSubfield σ))
    (hx : x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 (fixSubfield σ)).rootGroup J.1)
    (y : (adjDatumE6 K).leviAmalgam J)
    (hxy : ((y : adjointGroup .E6 K) : ModGL .E6 K) =
      baseChangeGL (fixSubfield σ).subtype (x : ModGL .E6 (fixSubfield σ))) :
    coverFamilyE6 sH sS ρ hc4 hc5 J y = ((e.symm x : L) : G) := by
  have hpair : ∀ {j : Fin (Tag.rank .E6)} (hj : j = 4 ∨ j = 5)
      (hc : ∀ a b, Commute (sixLiftE6 sS ρ four_not_mem_one_E6 five_not_mem_one_E6 a)
        (highLiftE6 sH (one_not_mem_of hj) (by simp) b))
      (h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1) (hjJ : j ∈ J.1)
      (hy : (y : adjointGroup .E6 K) ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1} ⊔
        CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j}),
      coverPairLiftE6 sH sS ρ hj hc ⟨y, hy⟩ = ((e.symm x : L) : G) := by
    intro j hj hc h1 hjJ hy
    have hJ : (J.1 : Finset (Fin (Tag.rank .E6))) = {1, j} :=
      eq_pair_of_card_le_two J.2 (one_ne_of hj) h1 hjJ
    have hx' : x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 (fixSubfield σ)).rootGroup {1} ⊔
        CFSG.LieType.CurtisTits.levi (adjDatumE6 (fixSubfield σ)).rootGroup {j} := by
      rw [← F4Pilot.levi_pair, ← hJ]
      exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      exists_mul_eq_of_mem_sup_of_commute_E6 (commute_adLevi_one (K := fixSubfield σ) hj) hx'
    obtain ⟨a', ha'⟩ := exists_levi_adjDatumE6_baseChangeGL (K := K) (fixSubfield σ).subtype ha
    obtain ⟨b', hb'⟩ := exists_levi_adjDatumE6_baseChangeGL (K := K) (fixSubfield σ).subtype hb
    have hyab : (⟨y, hy⟩ : ↥(CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1} ⊔
        CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j})) =
        ⟨a', mem_sup_left a'.2⟩ * ⟨b', mem_sup_right b'.2⟩ := by
      refine Subtype.ext (Subtype.ext ?_)
      change ((y : adjointGroup .E6 K) : ModGL .E6 K) =
        ((a' : adjointGroup .E6 K) : ModGL .E6 K) * ((b' : adjointGroup .E6 K) : ModGL .E6 K)
      rw [hxy, ha', hb', ← map_mul]
      rfl
    rw [hyab, map_mul, coverPairLiftE6_of_mem_left _ _ _ hj hc _ a'.2,
      coverPairLiftE6_of_mem_right _ _ _ hj hc _ b'.2,
      sixLiftE6_fix hS hρ hq four_not_mem_one_E6 five_not_mem_one_E6 ha _ ha',
      highLiftE6_fix hH hq (one_not_mem_of hj) (by simp) hb _ hb', map_mul, L.coe_mul]
  by_cases h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1
  · by_cases h4 : (4 : Fin (Tag.rank .E6)) ∈ J.1
    · rw [coverFamilyE6_of_four h1 h4]
      exact hpair four_cases hc4 h1 h4 _
    · by_cases h5 : (5 : Fin (Tag.rank .E6)) ∈ J.1
      · rw [coverFamilyE6_of_five h1 h4 h5]
        exact hpair five_cases hc5 h1 h5 _
      · rw [coverFamilyE6_of_six h1 h4 h5]
        exact sixLiftE6_fix hS hρ hq h4 h5 hx y hxy
  · rw [coverFamilyE6_of_one_not_mem h1]
    exact highLiftE6_fix hH hq h1 J.2 hx y hxy

end Compat

section Main


variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

theorem commutator_levi_adjDatumE6 (hK : 4 ≤ Nat.card K) {J : Finset (Fin (Tag.rank .E6))}
    (hJ2 : J.card ≤ 2) :
    ⁅CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J,
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J⁆ =
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J := by
  apply map_injective (adjointGroup .E6 K).subtype_injective
  rw [map_commutator, map_subtype_levi_adjDatumE6,
    ← perfectCore_inf_centralizer_leviTorus_inf hK hJ2]
  exact CFSG.Quasithin.perfectCore_perfect _

theorem exists_isFieldRowFamily_of_cover (h : FieldNeighbourCover σ e .high)
    (hσ : orderOf σ = 2) (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ∃ φ : ∀ J, (adjDatumE6 K).leviAmalgam J →* G, IsFieldRowFamily e φ := by
  have hσ1 : σ ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  obtain ⟨c, hc⟩ : ∃ c : K, σ c ≠ c := by
    by_contra hne
    exact hσ1 (RingEquiv.ext fun x => not_not.1 fun hx => hne ⟨x, hx⟩)
  have hlt : Nat.card (fixSubfield σ) < Nat.card K :=
    Finite.card_subtype_lt (p := fun x => x ∈ fixSubfield σ) (x := c)
      fun hmem => hc ((mem_fixSubfield σ).1 hmem)
  have hK : 5 ≤ Nat.card K := by omega
  have hK4 : 4 ≤ Nat.card K := by omega
  choose sH hH using fun (J : Finset (Fin (Tag.rank .E6))) (h1 : (1 : Fin (Tag.rank .E6)) ∉ J)
    (hJ2 : J.card ≤ 2) => exists_isCoverPiece_high h hK (subset_nodes_high_of_one_not_mem h1) hJ2
  obtain ⟨sS, hS⟩ :=
    exists_isCoverPiece_toNeighbour h hK (Or.inl rfl) (subset_refl E6Neighbour.six.nodes)
  obtain ⟨sT, hT⟩ :=
    exists_isCoverPiece_toNeighbour h hK (Or.inr rfl) (subset_refl E6Neighbour.three.nodes)
  obtain ⟨sA, hA⟩ := exists_isCoverPiece_a3 h hK
  obtain ⟨ρ, hρ, htw⟩ :=
    exists_twist_eq_on_a3_cover h (h.toNeighbour .six) hq hA (hS.restrict a3Nodes_subset_six)
  have hagree : ∀ {I : Finset (Fin (Tag.rank .E6))} (hI1 : (1 : Fin (Tag.rank .E6)) ∉ I)
      (hI2 : I.card ≤ 2), I ⊆ {0, 2, 3} →
      ∀ (x : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup I)
        (z : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup E6Neighbour.six.nodes),
        ((z : adjointGroup .E6 K) : ModGL .E6 K) =
          baseChangeGL (ρ : K →+* K) ((x : adjointGroup .E6 K) : ModGL .E6 K) →
        highLiftE6 sH hI1 hI2 x = ((sS z : neighbourCore e .six) : G) := by
    intro I hI1 hI2 hIA x z hzx
    have e1 := (hH I hI1 hI2).eq_of_subset hA hq (subset_refl I) hIA hI2 x
    have hx1 : leviIncl (subset_refl I) x = x := Subtype.ext (coe_leviIncl _ x)
    rw [hx1] at e1
    obtain ⟨w, hw⟩ := exists_levi_adjDatumE6_baseChangeGL (ρ : K →+* K)
      (leviIncl hIA x).2
    have e2 := htw (leviIncl hIA x) w (by rw [hw])
    have hwz : leviIncl a3Nodes_subset_six w = z := by
      apply Subtype.ext
      apply Subtype.ext
      rw [coe_leviIncl, hw, hzx, coe_leviIncl]
    change ((sH I hI1 hI2 x : neighbourCore e .high) : G) = _
    rw [e1, e2, MonoidHom.comp_apply, hwz]
  have h1T : ({1} : Finset (Fin (Tag.rank .E6))) ⊆ E6Neighbour.three.nodes := one_subset_three
  have hrangeS :
      (sixLiftE6 sS ρ four_not_mem_one_E6 five_not_mem_one_E6).range = pieceCore e {1} := by
    have hr : (sixLiftE6 sS ρ four_not_mem_one_E6 five_not_mem_one_E6).range =
        ((neighbourCore e .six).subtype.comp (sS.comp (leviIncl
          (subset_nodes_six_of_not_mem four_not_mem_one_E6 five_not_mem_one_E6)))).range := by
      change (((neighbourCore e .six).subtype.comp (sS.comp (leviIncl
        (subset_nodes_six_of_not_mem four_not_mem_one_E6 five_not_mem_one_E6)))).comp
          (leviEntrywise (ρ : K →+* K) {1})).range = _
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (leviEntrywise_surjective ρ {1}),
        ← MonoidHom.range_eq_map]
    rw [hr]
    exact (hS.restrict _).range_eq_pieceCore hq (by simp)
  have hc : ∀ {j : Fin (Tag.rank .E6)} (hj : j = 4 ∨ j = 5), ∀ a b,
      Commute (sixLiftE6 sS ρ four_not_mem_one_E6 five_not_mem_one_E6 a)
        (highLiftE6 sH (one_not_mem_of hj) (by simp) b) := by
    intro j hj a b
    have hjT : ({j} : Finset (Fin (Tag.rank .E6))) ⊆ E6Neighbour.three.nodes :=
      singleton_subset_three_of hj
    have hM1 := (hT.restrict h1T).range_eq_pieceCore hq (by simp)
    have hMj := (hT.restrict hjT).range_eq_pieceCore hq (by simp)
    have hrangeH := (hH {j} (one_not_mem_of hj) (by simp)).range_eq_pieceCore hq (by simp)
    obtain ⟨a', ha'⟩ : sixLiftE6 sS ρ four_not_mem_one_E6 five_not_mem_one_E6 a ∈
        ((neighbourCore e .three).subtype.comp (sT.comp (leviIncl h1T))).range := by
      rw [hM1, ← hrangeS]
      exact ⟨a, rfl⟩
    obtain ⟨b', hb'⟩ : highLiftE6 sH (one_not_mem_of hj) (by simp) b ∈
        ((neighbourCore e .three).subtype.comp (sT.comp (leviIncl hjT))).range := by
      rw [hMj, ← hrangeH]
      exact ⟨b, rfl⟩
    rw [← ha', ← hb']
    have : Group.IsPerfect (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1}) :=
      Subgroup.isPerfect_iff.2 (commutator_levi_adjDatumE6 hK4 (by simp))
    have hcomm := commute_of_comp_commute_of_ker_le_center (h.toNeighbour .three).ker_le_center
      (sT.comp (leviIncl h1T)) (sT.comp (leviIncl hjT)) (fun a b => by
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hT, hT]
        have hab := (commute_adLevi_one hj _ a.2 _ b.2).eq
        show _ * _ = _ * _
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        change ((leviIncl h1T a : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup
            E6Neighbour.three.nodes) : adjointGroup .E6 K) *
          ((leviIncl hjT b : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup
            E6Neighbour.three.nodes) : adjointGroup .E6 K) =
          ((leviIncl hjT b : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup
            E6Neighbour.three.nodes) : adjointGroup .E6 K) *
          ((leviIncl h1T a : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup
            E6Neighbour.three.nodes) : adjointGroup .E6 K)
        rw [coe_leviIncl, coe_leviIncl]
        exact hab) a' b'
    exact hcomm.map (neighbourCore e .three).subtype
  have hpair : ∀ {j : Fin (Tag.rank .E6)}, j = 4 ∨ j = 5 →
      pieceCore e {1, j} = pieceCore e {1} ⊔ pieceCore e {j} := by
    intro j hj
    have hJT : ({1, j} : Finset (Fin (Tag.rank .E6))) ⊆ E6Neighbour.three.nodes :=
      Finset.insert_subset_iff.2 ⟨h1T (Finset.mem_singleton_self _), singleton_subset_three_of hj⟩
    have h1 := (hT.restrict hJT).range_eq_pieceCore hq Finset.card_le_two
    have h2 := (hT.restrict hJT).range_eq hq
    rw [← h1, h2, Finset.iSup_insert, Finset.iSup_singleton]
  exact ⟨coverFamilyE6 sH sS ρ (hc four_cases) (hc five_cases),
    ⟨isCompatible_coverFamilyE6 hH hq hagree, range_coverFamilyE6 hH hS hq hpair,
      fix_coverFamilyE6 hH hS hρ hq⟩⟩

theorem fieldCoverFamilyInput_holds : FieldCoverFamilyInput := by
  intro K _ _ _ σ G _ _ L e h hσ hq _
  exact exists_isFieldRowFamily_of_cover h hσ hq

end Main

end CFSG.SeitzReduction.E6Pilot
