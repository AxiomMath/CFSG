module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivNorm
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivHyp
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivJ2
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.S10.Defs
public import CFSG.RankThree.PartOne.S8.Statements

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoStandard

theorem step22iv_of
    (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (h310 : RankTwoClassical.Asc08Lemma310NF) : Step22iv := by
  intro G _ _ A R g E F hS
  have hF := hS.frame
  have hL := hS.type
  have hodd := hS.odd
  by_cases hT : E ⊓ A ≤ conjClosure (F ⊓ A) (sec2P E)
  · exact four_pow_four_le_card_conjClosure_of_le h11 hE16 hF hL hodd hT
  · exfalso
    obtain ⟨y, hyA, hyE, hyU, hy3, hW, hW256, -, -, hW₁, -, -, -⟩ :=
      sec2W_structure_of_not_le h11 hE16 hF hL hodd hT
    by_cases hn : (Sec2Quot.nbar (sec2W A E y) (sec2L A E)).Normal
    · exact false_of_nbar_normal h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hn
    · exact false_of_nbar_not_normal h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hT hW₁ h310
        (Sec2.not_isSporadic_M12_J2_of_elem256 hW hW256 fun x hx hx2 =>
          mem_sec2W_of_mem_centralizer h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hx hx2) hn

end CFSG.ComponentClassification.AS81
