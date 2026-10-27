module

public import CFSG.ClassicalInvolution.Asc77.AscT8S26UTop
public import CFSG.ClassicalInvolution.Asc77.AscT8S26UFinal
public import CFSG.ClassicalInvolution.Asc77.AscIHSectG

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.Assembly.LowTwoRank

section Claims

variable (p f : ℕ) [Fact p.Prime]

@[expose] def S26XProper : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoS4 Ω W → omegaNbrGen Ω K ≠ ⊤

@[expose] def S26XEdgeless : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoS4 Ω W →
        DEdgeless (oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K)))

@[expose] def S26XTop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoS4 Ω W →
        (⊤ : Subgroup (↥(omegaNbrGen Ω K) ⧸ classicalInvolutionOddCore ↥(omegaNbrGen Ω K))) ∉
          oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K))

@[expose] def S26XMuZ2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoS4 Ω W →
        ∃ W' ∈ WSet (oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K))),
          MuIsoZ2 (oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K))) W'

end Claims

variable {p f : ℕ} [Fact p.Prime]

theorem s26XTop_of_c26_1 (h1 : C26_1 p f) : S26XTop p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc _
  exact s26_top_notMem_of_c26_1 h1 hs hdisc

theorem c26_3_S4_of_x (hMu : Ih8MuTableSect p f) (hB : S26XProper p f) (hE : S26XEdgeless p f)
    (hT : S26XTop p f) (hZ : S26XMuZ2 p f) : C26_3_S4 p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hS4
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hA : ∀ L ∈ Ω, AEmpty Ω L := hs.stand.aEmpty
  have hn : CITBelowU p f (Nat.card G) := hs.stand.below f hq
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  have hXp : X ≠ ⊤ := hB G Ω K J S R T W z t hs hdisc hS4
  have hDE : DEdgeless (oddQuotientFamily (restrictFamily Ω X)) :=
    hE G Ω K J S R T W z t hs hdisc hS4
  have htop : (⊤ : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X)) ∉
      oddQuotientFamily (restrictFamily Ω X) := hT G Ω K J S R T W z t hs hdisc hS4
  obtain ⟨W', hW', hZ2⟩ := hZ G Ω K J S R T W z t hs hdisc hS4
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
  have hrows := hMu (Nat.card G) hn hp hq (↥X ⧸ classicalInvolutionOddCore ↥X) hlt _ hTrans hne
    htop W' hW'
  have hlie := hrows.1.mp hZ2
  have hp2 : p ^ f % 2 = 1 := Nat.odd_iff.mp (((Fact.out : p.Prime).odd_of_ne_two hp).pow)
  by_cases hpi : p ^ f % 4 = 1
  · right
    refine ⟨?_, hpi⟩
    have hpi' : piSign p f = true := by simp [piSign, hpi]
    rw [hpi'] at hlie
    exact sectionLieType_of_hasLieType hGen.gen (by simpa using hlie)
  · left
    refine ⟨?_, by omega⟩
    have hpi' : piSign p f = false := by simp [piSign, hpi]
    rw [hpi'] at hlie
    exact sectionLieType_of_hasLieType hGen.gen (by simpa using hlie)

theorem c26_2_u_of_x (hMu : Ih8MuTableSect p f) (hB : S26XProper p f) (hE : S26XEdgeless p f)
    (hT : S26XTop p f) (hZ : S26XMuZ2 p f) : C26_2_u p f :=
  c26_2_u_of_c26_3 (c26_3_S4_of_x hMu hB hE hT hZ)

theorem c26_2_of_x (hMu : Ih8MuTableSect p f) (hB : S26XProper p f) (hE : S26XEdgeless p f)
    (hT : S26XTop p f) (hZ : S26XMuZ2 p f) : C26_2 p f :=
  c26_2_of_c26_3 (c26_3_S4_of_x hMu hB hE hT hZ)

theorem thm8A_of_s26_x (hMu : Ih8MuTableSect p f) (hB : S26XProper p f) (hE : S26XEdgeless p f)
    (h1 : C26_1 p f) (hZ : S26XMuZ2 p f) (h13 : C26_13_sc p f) (h274a : C27_4a p f)
    (h8E4 : C27_8E4 p f) (h8nE4 : C27_8nE4 p f) : Thm8A p f :=
  thm8A_of_s26_c26_3 (c26_3_S4_of_x hMu hB hE (s26XTop_of_c26_1 h1) hZ) h13 h274a h8E4 h8nE4

end CFSG.ClassicalInvolution.Asc77
