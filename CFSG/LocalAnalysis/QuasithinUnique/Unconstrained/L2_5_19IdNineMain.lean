module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNineLin
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNineSporadic

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

theorem tabThreeRankNine : TabThreeRankNine := by
  intro G _ _ X hXq hZ2 hcase
  have key : HasElemAb 3 9 ↥X := by
    rcases hcase with hL3 | hJ2 | hHS | hA8 | hL5 | hSp | hA6
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL3
      have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
      exact HasElemAb.of_quotient_two _ hZ2
        (HasElemAb.of_mulEquiv e.symm (hasElemAb_nine_psl_three_four hK4))
    · obtain ⟨e⟩ := hJ2
      exact HasElemAb.of_quotient_two _ hZ2 (HasElemAb.of_mulEquiv e.symm hasElemAb_nine_J2)
    · obtain ⟨e⟩ := hHS
      exact HasElemAb.of_quotient_two _ hZ2 (HasElemAb.of_mulEquiv e.symm hasElemAb_nine_HS)
    · obtain ⟨e⟩ := hA8
      exact HasElemAb.of_mulEquiv e.symm hasElemAb_nine_alt_eight
    · obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := hL5
      exact HasElemAb.of_mulEquiv e.symm (hasElemAb_nine_psl_five K)
    · obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := hSp
      exact HasElemAb.of_mulEquiv e.symm (hasElemAb_nine_psp_four K)
    · obtain ⟨e⟩ := hA6
      exact HasElemAb.of_mulEquiv e.symm hasElemAb_nine_alt_six
  exact key.exists_subgroup

end CFSG.QuasithinUnique.Id2519
