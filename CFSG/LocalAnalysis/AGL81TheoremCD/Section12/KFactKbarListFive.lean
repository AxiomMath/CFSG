module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactKbarListFiveAlternating
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactKbarListFiveClassical
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactKbarListFiveExceptional
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactKbarListFiveSporadicRank
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactKbarListFiveSporadicSmall
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactKbarListFiveMonster

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic Subgroup
open CFSG.LocalAnalysis.AGL81I.Section3
open KbarListFive


theorem kFactKbarListFive_holds : KFactKbarListFive := by
  intro p hp hp5 K _ _ hKcat hpr S _ _ he Y V W₁ W₂ W₃ t₁ t₂ t₃ hY hr hcfg hV ht₁ ht₂ ht₃
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := he
  obtain ⟨-, -, hq, -, hK⟩ := hKcat
  rcases hK with hK | ⟨-, hK⟩ | ⟨hp3, -⟩ | ⟨hp5', hK⟩ | ⟨hp7, hK⟩ | ⟨hp11, hK⟩
  · rcases hK with hK | hK | hK | hK | hK | hK | hK | hK | hK
    · obtain ⟨a⟩ := hK
      exact alternating_two_mul hp5 hq e a hY hr
    · obtain ⟨a⟩ := hK
      exact (false_of_alternating_three_mul hp5 hq e a hY hr).elim
    · exact (false_of_psl_two hp hp5 hq e hK hcfg.elem hcfg.card).elim
    · exact (false_of_psl_two hp hp5 hq e hK hcfg.elem hcfg.card).elim
    · exact (false_of_psl_three_prime hp hp5 hq e hK hcfg.elem hcfg.card).elim
    · exact (false_of_psu_three_prime hp hp5 hq e hK hcfg.elem hcfg.card).elim
    · obtain ⟨a⟩ := hK
      have hm : StatedClassicalModel K .PSL 4 p 1 :=
        ⟨⟨hp, le_rfl, by norm_num, by simp, by simp⟩, ZMod p, inferInstance, inferInstance,
          by simp, ⟨a.trans
            (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 (ZMod p))⟩⟩
      obtain ⟨-, -, hcases⟩ := CFSG.SectionRank.classical_model_rank (by omega) hm
      rcases hcases with ⟨-, ⟨h, -⟩ | ⟨h, -⟩ | h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
      all_goals first | omega | cases h
    · obtain ⟨-, -, hcases⟩ := CFSG.SectionRank.classical_model_rank (by omega) hK
      rcases hcases with ⟨h, -⟩ | ⟨-, ⟨h, -⟩ | h⟩ | ⟨h, -⟩ | h
      all_goals first | omega | cases h
    · exact (false_of_psp_four_prime hp hp5 hq e hK hcfg.elem hcfg.card).elim
  · exact (false_of_g2_prime hp hp5 hq e hK hcfg.elem hcfg.card).elim
  · omega
  · rcases hK with hK | hK | hK | hK | hK | hK | hK | hK | hK | hK | hK | hK
    · exact (false_of_suzuki hq e hK hcfg hV ht₁ ht₂ ht₃).elim
    · exact (false_of_tits hq e hK hcfg.elem hcfg.card).elim
    · exact (false_of_sporadic_rank_four hq e (s := .McL) (by simp) hK hY hr).elim
    · exact (false_of_hs hq e hK hcfg.elem hcfg.card).elim
    · exact (false_of_sporadic_rank_four hq e (s := .Fi22) (by simp) hK hY hr).elim
    · exact (false_of_sporadic_rank_four hq e (s := .Co1) (by simp) hK hY hr).elim
    · exact (false_of_sporadic_rank_four hq e (s := .Co2) (by simp) hK hY hr).elim
    · exact (false_of_sporadic_rank_four hq e (s := .Co3) (by simp) hK hY hr).elim
    · exact (false_of_sporadic_rank_four hq e (s := .Ly) (by simp) hK hY hr).elim
    · exact (false_of_ru hq e hK hcfg.elem hcfg.card).elim
    · exact (false_of_sporadic_rank_four hq e (s := .B) (by simp) hK hY hr).elim
    · exact (false_of_sporadic_rank_four hq e (s := .HN) (by simp) hK hY hr).elim
  · rcases hK with hK | hK | hK | hK
    · exact (false_of_he hq e hK hcfg.elem hcfg.card).elim
    · exact (false_of_sporadic_rank_four hq e (s := .ONan) (by simp) hK hY hr).elim
    · exact (false_of_sporadic_rank_four hq e (s := .Fi24Prime) (by simp) hK hY hr).elim
    · exact (false_of_monster hq e hK hY hr).elim
  · exact (false_of_j4 hq e hK hcfg.elem hcfg.card).elim

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
