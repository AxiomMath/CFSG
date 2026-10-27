module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12EndOverlap
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Thm3Four
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundation

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M12

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.ABGLocalTools
open CFSG.ComponentClassification.Asc76 CFSG.ComponentClassification.AschbacherTheorem3

theorem sporadicCaseOdd_M12_of_check
    {S : Array (Array ℕ)} {Wd : Array (List ℤ)} {sG roots : Array ℕ}
    {nodes : Array CFSG.KC.Census.NodeP} {cS : CFSG.KC.Census.ArrCertP}
    {wcs : Array (Array CFSG.KC.Census.ArrCertP)} {excs : List CFSG.KC.Census.ExcRefP}
    (hc : m12CheckW S Wd m12E0 sG roots nodes cS wcs excs = true)
    (hE : m12EndCheck S m12E0 m12EndA0 m12EndLeaves m12EndL m12EndSigma m12EndC0 m12EndZ = true)
    (hO : m12OverFacts S)
    (h3L : Asc76Theorem3Large) (h22 : Asc76Lemma22) (h4' : Asc76Theorem4) :
    SporadicCaseOdd .M12 := by
  intro G _ _ A hH hodd ⟨e⟩
  have hA := hH.standard
  have hm : 1 < Open.pRank 2 (centralizer (A : Set G)) := by
    have := hH.rank
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := exists_isSylowOf 2 (centralizer (A : Set G))
  by_cases hRd : IsDihedralTwoGroup R
  · obtain ⟨g, hg, -⟩ := AS76b.exists_even_overlap hA hodd hm hH.not_normal
    obtain ⟨hR4, hRe, g', hg', T', hT'1, hT'2⟩ := Sec5.dihedral_conclusion h3L
      Asc76X.Thm3Four.asc76Theorem3Four hodd hA hg hR hRd (Sec5.one_lt_pRank_of_isSylowOf hR hm)
    exact false_of_config hc hE hA e hg' hT'2 (hT'1.le.trans inf_le_right) hR hRe.2 hR4.ge
  · exact m12_false_of_not_dihedral hc hE hO h22 RankTwoFoundation.asc75Theorem4 h4' hA hodd hm
      hH.not_normal e hR hRd

end CFSG.ComponentClassification.RankTwoSporadic.M12
