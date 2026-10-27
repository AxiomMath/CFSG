module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoStageFFar
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoStageFPartner
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoDefs

public section

namespace CFSG.OddStandard.AltStdCycTwo

open Subgroup Equiv AltStdBal AltStdSec CFSG.ComponentClassification.RestrictedStd.Spor

namespace StageF

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ} {z : G}

theorem Inner.nearGivesRoot (hlookup : AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hOut : CFSG.RankThree.PartOne.SporadicOuterOrderLeTwoSimple) (hFour : FourExactOuterInput)
    (c : Inner G L Q n z) (hodd : Odd n) (e : L ≃* alternatingGroup (Fin n))
    (hnear : ∃ y ∈ FusionSet L z, IsNear e y) :
    ∃ S : Finset (Fin n), S.card = 4 ∧ ∀ b ∈ L, b ∈ centralizer (rootGroup e S : Set G) →
      orderOf b = 2 → ∃ h' ∈ centralizer (rootGroup e S : Set G), h' * z * h'⁻¹ = z * b := by
  obtain ⟨y, hy, hyL, hnear⟩ := hnear
  have hf4 : 4 ≤ (fixFin ((e ⟨y, hyL⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card := by
    rw [← card_fixedPoints_eq]
    exact hnear
  exact c.nearGives hlookup hHN hOut hFour hodd e (by norm_num) le_rfl hy hf4

theorem Inner.fusionAll (hlookup : AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hOut : CFSG.RankThree.PartOne.SporadicOuterOrderLeTwoSimple) (hFour : FourExactOuterInput)
    (c : Inner G L Q n z) (hodd : Odd n) : FusionAll L z := by
  obtain ⟨e⟩ := c.iso
  by_cases hnear : ∃ y ∈ FusionSet L z, IsNear e y
  · obtain ⟨S, hS, hsec⟩ := c.nearGivesRoot hlookup hHN hOut hFour hodd e hnear
    obtain ⟨e₀, he₀R, he₀2, he₀L, he₀cov, hcov⟩ := rootCover G L n c.hn e S hS
    exact c.fusionAll_of_section_fusion he₀R he₀2 he₀L hsec hcov he₀cov
  · push Not at hnear
    exact (c.farOnlyFalse e hnear).elim

end StageF

theorem cycTwoInnerFusionAll_of_inputs (hlookup : AltComponentLookup)
    (hHN : HNLocalComponentsInput)
    (hOut : CFSG.RankThree.PartOne.SporadicOuterOrderLeTwoSimple)
    (hFour : FourExactOuterInput) : CycTwoInnerFusionAll := by
  intro G _ _ L Q n θ z h hn hE
  exact StageF.Inner.fusionAll hlookup hHN hOut hFour ⟨h.std, hn, ⟨θ⟩, h.cyc, h.card, hE⟩ h.odd

end CFSG.OddStandard.AltStdCycTwo
