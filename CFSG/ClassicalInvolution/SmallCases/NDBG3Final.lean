module

public import CFSG.ClassicalInvolution.SmallCases.NDBG3AEmpty
public import CFSG.ClassicalInvolution.SmallCases.NDBG6Main
public import CFSG.ClassicalInvolution.SmallCases.NDBD4Frame
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.AS76b (Asc75Theorem4)

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable (p f : ℕ) [Fact p.Prime]


@[expose] def G2TwinPred : Asc77.ShapePred := fun G _ _ K z =>
  p = 3 ∧ (∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) ∧
    ∃ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z, ∃ i : Fin D.card,
      D.tag i = .G2 ∧ D.card = 3

variable {p f}

theorem NDBG3.false_of_g2_three_of_frame (hfr : Asc77.FrameExistsOnE p f (G2TwinPred p f))
    (h4 : Asc75Theorem4) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hz : IsClassicalMember p f K z) (hBelow : CITBelowU p f (Nat.card G))
    (hD : Disconnected.DConnected (𝒞 K)) (hp3 : p = 3)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A)
    (D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z) {b : Fin D.card} (hG2 : D.tag b = .G2)
    (h3 : D.card = 3) : False := by
  obtain ⟨L₀, z₀, A, S, a, hfrm, hA⟩ :=
    hfr G hnab hp2 hq K z hz hBelow hD ⟨hp3, hnoF, D, b, hG2, h3⟩
  have hΩ : InClass p f (𝒞 K) := inClass_conjugates hz
  obtain ⟨hex, -⟩ := Asc77.exactMembers_and_localOddCentral_of_fuzzyFrameStarE hnab hp2 hq hΩ
    (exists_single_class K) (localLieSystems_of_citBelowU hΩ hBelow) hD hfrm
    (Asc77.lemma52 G A hA)
  exact NDBG3.false_of_g2_of_exact h4 hnab hp2 hq hz hBelow hex hnoF D hG2 (by omega)

theorem NDBG3.false_of_g2_of_frame (hfr : Asc77.FrameExistsOnE p f (G2TwinPred p f))
    (h4 : Asc75Theorem4) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hz : IsClassicalMember p f K z) (hBelow : CITBelowU p f (Nat.card G))
    (hD : Disconnected.DConnected (𝒞 K))
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A)
    (D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z) {b : Fin D.card} (hG2 : D.tag b = .G2)
    (hcard : 3 ≤ D.card) : False := by
  let C := Cover.toXCtx hnab hp2 hq hz hBelow D
  by_cases hp3 : p = 3
  · rcases (show D.card = 3 ∨ 3 < D.card by omega) with h | h
    · exact NDBG3.false_of_g2_three_of_frame hfr h4 hnab hp2 hq hz hBelow hD hp3 hnoF D hG2 h
    · exact BSC.BSE.false_of_g2_of_card (C := C) hnoF (b := b) hG2 h
  · exact NDBG.false_of_g2_of_card_ne_three hp3 C hnoF (b := b) hG2 hcard

theorem noG2D4Twin_of_frame (hfr : Asc77.FrameExistsOnE p f (G2TwinPred p f))
    (h4 : Asc75Theorem4) : NoG2D4Twin p f := by
  intro G _ _ _ K z hS hT D i hi
  have hno := fuzzyFrameExcluded G K z hS
  let C := Cover.toXCtx hS.nonabelian hS.odd hS.five hS.member hS.below D
  have hb : ¬ (C.D.tag i = .PSL ∧ C.D.rank i = 2) := fun h => by
    rcases hi with hi | hi <;>
    · rw [show C.D.tag i = _ from hi] at h
      exact absurd h.1 (by decide)
  obtain ⟨T, hTΩ, hTK, hTz⟩ := hT
  have hcard : 3 ≤ C.D.card := NDBG.three_le_card_of_twin C hb hTΩ hTK hTz
  rcases hi with hG2 | hD4
  · exact NDBG3.false_of_g2_of_frame hfr h4 hS.nonabelian hS.odd hS.five hS.member hS.below
      hS.dconn hno D hG2 hcard
  · exact NDBG.false_of_trialityD4_of_card (C := C) hno (b := i) hD4 hcard

theorem bootNoG2Twin_of_frame (hfr : Asc77.FrameExistsOnE p f (G2TwinPred p f))
    (h4 : Asc75Theorem4) : BSC.BootNoG2Twin p f := by
  intro G _ _ _ K z hS D i hG2 hcard
  exact NDBG3.false_of_g2_of_frame hfr h4 hS.nonabelian hS.odd hS.five hS.member hS.below
    hS.dconn (BSC.noFuzzyFrame hS) D hG2 hcard

end CFSG.ClassicalInvolution.NDB
