module

public import CFSG.ClassicalInvolution.Asc77.AscT8W1
public import CFSG.ClassicalInvolution.Asc77.AscMuTabProved
public import CFSG.ClassicalInvolution.Asc77.AscT8ROutF
public import CFSG.ClassicalInvolution.Asc77.AscT8S2Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.Assembly.LowTwoRank

namespace T8W

section Sec

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem s26XMuZ2_E4_of_data (hs : Std8 p f Ω K J S R T W z t) (hE : MuIsoE4 Ω W)
    (hX : omegaNbrGen Ω K ≠ ⊤) :
    ∃ W' ∈ WSet (oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K))),
      MuIsoZ2 (oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K))) W' := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  obtain ⟨S₂, hRS₂, hS₂X⟩ := exists_sylow_meeting_X hs
  obtain ⟨J₂, hJ₂, hK1⟩ :=
    exists_unique_member_E4 hs hE hRS₂ (T8S2.not_le_omegaNbrGen hs hX)
  have hGen := s26_genSection_omegaNbrGen (K := K) hp hq hΩ hs.stand.aEmpty
  have hJ₂X : J₂ ≤ X := le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J₂ hJ₂
  refine T8S2.exists_muIsoZ2_of_sylow hp hq (Λ := restrictFamily Ω X) (hΩ.restrict X)
    hGen.hyp hGen.aEmpty (AscP1Nine3.sylowOfIsSylow2In₉ hS₂X) (J₀ := J₂.subgroupOf X)
    ⟨J₂, hJ₂.1, hJ₂X, rfl⟩ ?_
  rintro _ ⟨L, hL, hLX, rfl⟩ hcard
  have hSH : ((AscP1Nine3.sylowOfIsSylow2In₉ hS₂X : Sylow 2 ↥X) : Subgroup ↥X) =
      ((S₂ : Subgroup G) ⊓ X).subgroupOf X := rfl
  have hLS : L ⊓ (S₂ : Subgroup G) ≤ X := inf_le_left.trans hLX
  have hinf : L.subgroupOf X ⊓ ((S₂ : Subgroup G) ⊓ X).subgroupOf X =
      (L ⊓ (S₂ : Subgroup G)).subgroupOf X := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  rw [hSH, hinf] at hcard
  have hc2 : Nat.card ↥((L ⊓ (S₂ : Subgroup G)).subgroupOf X) =
      Nat.card ↥(L ⊓ (S₂ : Subgroup G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLS).toEquiv
  rw [hc2] at hcard
  rw [hK1 L hL hLX hcard]

theorem s26XProper_E4 [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) : omegaNbrGen Ω K ≠ ⊤ := fun htop => by
  have hle := s26_omegaNbrGen_le_sigmaNorm hs.stand.hyp.conjInvariant hs.stand.mem
  rw [htop, top_le_iff] at hle
  exact hdisc (dConnected_of_sigmaNorm_eq_top hs.stand.mem hs.stand.trans hle)

theorem s26XEdgeless_E4 [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hE : MuIsoE4 Ω W) :
    DEdgeless (oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K))) := by
  obtain ⟨W', hW', hZ2⟩ := s26XMuZ2_E4_of_data hs hE (s26XProper_E4 hs hdisc)
  have hGen := s26_genSection_omegaNbrGen (K := K) hs.stand.odd hs.stand.five hs.stand.hyp
    hs.stand.aEmpty
  exact s26_dEdgeless_of_muIsoZ2 (l7_5_2_proved p f) hs.stand.odd hs.stand.five hGen.hyp
    hGen.aEmpty hW' hZ2

theorem c26_3_E4 [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t) (hdisc : ¬ DConnected Ω)
    (hE : MuIsoE4 Ω W) :
    (SectionLieType p f Ω (omegaNbrGen Ω K) .PSL 3 ∧ p ^ f % 4 = 3) ∨
    (SectionLieType p f Ω (omegaNbrGen Ω K) .PSU 3 ∧ p ^ f % 4 = 1) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hA : ∀ L ∈ Ω, AEmpty Ω L := hs.stand.aEmpty
  have hn : CITBelowU p f (Nat.card G) := hs.stand.below f hq
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  have hXp : X ≠ ⊤ := s26XProper_E4 hs hdisc
  have hDE : DEdgeless (oddQuotientFamily (restrictFamily Ω X)) := s26XEdgeless_E4 hs hdisc hE
  have htop : (⊤ : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X)) ∉
      oddQuotientFamily (restrictFamily Ω X) := s26_top_notMem_of_c26_1 (T8R.c26_1 p f) hs hdisc
  obtain ⟨W', hW', hZ2⟩ := s26XMuZ2_E4_of_data hs hE hXp
  have hlt : Nat.card (↥X ⧸ classicalInvolutionOddCore ↥X) < Nat.card G := by
    have h1 : Nat.card ↥X < Nat.card G :=
      lt_of_le_of_ne (Subgroup.card_le_card_group X)
        (fun h => hXp (Subgroup.eq_top_of_card_eq X h))
    exact lt_of_le_of_lt (Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective) h1
  have hL : layerHull Ω X = X := s26_layerHull_omegaNbrGen Ω K
  have hGen : GenSection p f (oddQuotientFamily (restrictFamily Ω X)) := by
    have := genSection_layerHull hp hq hΩ hA X
    rwa [hL] at this
  have hJX : J ≤ X := le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J hs.hJ
  have hne : (oddQuotientFamily (restrictFamily Ω X)).Nonempty :=
    ⟨_, ⟨J.subgroupOf X, ⟨J, hs.hJ.1, hJX, rfl⟩, rfl⟩⟩
  have hTrans : TransSection p f (oddQuotientFamily (restrictFamily Ω X)) := by
    rcases transSection_or_dConnected hp hq (thm4Below_of_citBelow hn) hlt hGen with hc | ht
    · exfalso
      obtain ⟨K₀, hK₀⟩ := hne
      apply htop
      have hall : omegaGen (oddQuotientFamily (restrictFamily Ω X)) = K₀ := by
        refine le_antisymm (iSup₂_le fun L hL => ?_) (le_omegaGen hK₀)
        rw [eq_of_dConnected_of_dEdgeless hc hDE hL hK₀]
      rw [← hGen.gen, hall]
      exact hK₀
    · exact ht
  have hrows := ih8MuTableSect_proved (p := p) (f := f) (Nat.card G) hn hp hq
    (↥X ⧸ classicalInvolutionOddCore ↥X) hlt _ hTrans hne htop W' hW'
  have hlie := hrows.1.mp hZ2
  by_cases hpi : p ^ f % 4 = 1
  · right
    refine ⟨?_, hpi⟩
    have hpi' : piSign p f = true := by simp [piSign, hpi]
    rw [hpi'] at hlie
    exact sectionLieType_of_hasLieType hGen.gen (by simpa using hlie)
  · left
    have hp2 : p ^ f % 2 = 1 := Nat.odd_iff.mp (((Fact.out : p.Prime).odd_of_ne_two hp).pow)
    refine ⟨?_, by omega⟩
    have hpi' : piSign p f = false := by simp [piSign, hpi]
    rw [hpi'] at hlie
    exact sectionLieType_of_hasLieType hGen.gen (by simpa using hlie)

end Sec

end T8W

end CFSG.ClassicalInvolution.Asc77
