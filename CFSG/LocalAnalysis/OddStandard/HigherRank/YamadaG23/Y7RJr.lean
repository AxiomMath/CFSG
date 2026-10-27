module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RPs
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RPr

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {t : G} {P U : Subgroup G}

private theorem openPRank_le_six_of_le_P (h : Wr7 t P U) (hU : RankFacts U) {V : Subgroup G}
    (hVP : V ≤ P) : CFSG.Open.pRank 2 V ≤ 6 := by
  refine CFSG.SectionRank.pRank_le (p := 2) (H := V) (k := 6) (by norm_num) ?_
  intro E hEV hE
  have := Wr7.rank_bound h hU E (hEV.trans hVP) hE
  simpa using this

private theorem le_thompsonRank_of {T E : Subgroup G} (hET : E ≤ T)
    (hEc : IsMulCommutative E)
    (hmax : ∀ V : Subgroup G, V ≤ T → IsMulCommutative V → pRank 2 V ≤ pRank 2 E) :
    E ≤ thompsonRank T := by
  unfold thompsonRank
  refine le_iSup_of_le E ?_
  refine le_iSup_of_le hET ?_
  refine le_iSup_of_le hEc ?_
  refine le_iSup_of_le hmax ?_
  exact le_rfl

theorem Wr7.pRank_abelian_le (h : Wr7 t P U) (hU : RankFacts U) {V : Subgroup G}
    (hV : V ≤ wrStar t P) (hVc : IsMulCommutative V) :
    pRank 2 V ≤ 6 ∧ (¬ V ≤ P → pRank 2 V ≤ 4) := by
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank 2 V]
  by_cases hVP : V ≤ P
  · exact ⟨openPRank_le_six_of_le_P h hU hVP, fun hnp => absurd hVP hnp⟩
  · have h4 : CFSG.Open.pRank 2 V ≤ 4 := by
      refine CFSG.SectionRank.pRank_le (p := 2) (H := V) (k := 4) (by norm_num) ?_
      intro E hEV hE
      have := Wr7.abelian_out h hU hV hVc hVP E hEV hE
      simpa using this
    exact ⟨h4.trans (by norm_num), fun _ => h4⟩

theorem Wr7.thompsonRank_star (h : Wr7 t P U) (hU : RankFacts U) :
    thompsonRank (wrStar t P) = P := by
  apply le_antisymm
  ·
    unfold thompsonRank
    refine iSup_le fun W => iSup_le fun hW => iSup_le fun hWc => iSup_le fun hmax => ?_
    by_contra hWP
    obtain ⟨E, hEP, hE, hEcard, -⟩ := Wr7.rank_cover h hU (x := 1) P.one_mem (by simp)
    have hEstar : E ≤ wrStar t P := by rw [wrStar]; exact hEP.trans le_sup_left
    have hle4 : pRank 2 W ≤ 4 := (Wr7.pRank_abelian_le h hU hW hWc).2 hWP
    have h6E : 6 ≤ pRank 2 E := by
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank 2 E]
      have := CFSG.SectionRank.le_pRank (p := 2) (H := E) (E := E) (by norm_num) le_rfl hE
        (k := 6) (by rw [hEcard]; norm_num)
      simpa using this
    have h6le : 6 ≤ pRank 2 W := h6E.trans (hmax E hEstar hE.1)
    omega
  ·
    refine (Wr7.rank_gen h hU (thompsonRank (wrStar t P))) ?_
    intro E hEP hE hEcard
    have hEstar : E ≤ wrStar t P := by rw [wrStar]; exact hEP.trans le_sup_left
    refine le_thompsonRank_of (T := wrStar t P) (E := E) hEstar hE.1 ?_
    intro V hVT hVc
    have h6E : pRank 2 E = 6 := by
      apply le_antisymm
      · exact (Wr7.pRank_abelian_le h hU hEstar hE.1).1
      · rw [CFSG.SectionRank.pRank_coe_eq_openPRank 2 E]
        have := CFSG.SectionRank.le_pRank (p := 2) (H := E) (E := E) (by norm_num) le_rfl hE
          (k := 6) (by rw [hEcard]; norm_num)
        simpa using this
    rw [h6E]
    exact (Wr7.pRank_abelian_le h hU hVT hVc).1

end CFSG.OddStandard.HigherRank.YamadaG23
