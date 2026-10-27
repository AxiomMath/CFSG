module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RSporHS
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RSporCompsB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RSporBaby
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSporTwoPart
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace L34R

theorem false_of_sporadic
    (hCT : EvenSporadicStandard.CentralTwoBound) (hR2 : SuzDoubleCoverL34Input)
    {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q) (hZ : IsPGroup 2 (center Q))
    (hZ1 : center Q ≠ ⊥) (hspor : NativeSporadic.SporadicRep (Q ⧸ center Q))
    {σ : MulAut Q} (hσ : ∀ y, σ (σ y) = y) {P : Subgroup Q} (hPF : P ≤ fixedSubgroup σ)
    (hP : IsPComponent 2 (P.subgroupOf (fixedSubgroup σ))) (hPne : P ≠ ⊤)
    (htype : IsL34Type (P ⧸ Open.fusionZStar P)) (hrank : 2 ≤ pRank 2 ↥(Open.fusionZStar P))
    {σ' : MulAut (Q ⧸ center Q)} {P' : Subgroup (Q ⧸ center Q)}
    (h' : CatLeaf.ProperFixedComponent σ' P') (htype' : IsL34Type (P' ⧸ Open.fusionZStar P')) :
    False := by
  have : IsSimpleGroup (Q ⧸ center Q) := hQ.2.1
  have hna : ∃ a b : Q ⧸ center Q, a * b ≠ b * a := hQ.2.2
  have h2Z : 2 ∣ Nat.card (center Q) := RankThree.PartTwo.Sec4.Census.two_dvd_card_center hZ
    ((Subgroup.nontrivial_iff_ne_bot _).mpr hZ1)
  have hodd : ∀ {m : ℕ}, Odd m → Nat.card (center Q) ∣ m → False := fun hm hdm =>
    (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr (h2Z.trans hdm))
  obtain ⟨s, ⟨e⟩⟩ := hspor
  have hd := SolMax.SporTwo.card_center_dvd_twoPartBound hCT hQ hZ e
  cases s
  all_goals try exact hodd (by decide) hd
  case M12 => exact not_isL34Type_M12 e P' htype'
  case M22 => exact not_isL34Type_M22 hna e h' htype'
  case J2 => exact not_isL34Type_J2 e h' htype'
  case HS => exact false_of_hs (Nat.le_of_dvd (by norm_num) hd) e htype hrank
  case Ru => exact not_isL34Type_Ru hna e h' htype'
  case Suz =>
    have := hR2 Q hQ hZ hZ1 ⟨e⟩ σ hσ P hPF hP hPne htype
    omega
  case Co1 => exact not_isL34Type_Co1 hna e h' htype'
  case Fi22 => exact not_isL34Type_Fi22 hna e h' htype'
  case B => exact not_isL34Type_B hna e h' htype'

end L34R

end CFSG.ComponentClassification.GrSLit
