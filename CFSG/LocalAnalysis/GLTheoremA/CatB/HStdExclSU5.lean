module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCenter

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HStdExcl

open Subgroup CFSG.Open CFSG.Fischer

theorem sU5Mult_holds :
    SU5Mult := by
  intro M _ _ hM hquot
  obtain ⟨e⟩ := hquot
  let projM5 : StatedProj (StatedSU 5 (2 ^ 1) F4) ≃* StatedSU 5 (2 ^ 1) F4 :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.statedScalars_subgroupOf_eq_bot
        (by rw [Nat.card_eq_fintype_card, F4.card]; norm_num))).trans
      QuotientGroup.quotientBot
  have hL : CFSG.Blueprint.LieModel (M ⧸ center M) .PSU 5 2 1 :=
    Or.inl ⟨by decide,
      ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩, F4, inferInstance,
        inferInstance, by rw [Nat.card_eq_fintype_card, F4.card]; norm_num,
        ⟨e.trans projM5.symm⟩⟩⟩
  exact CFSG.OddStandard.SmallF3.HypA2Leaves.a2l_center_eq_bot_psu52 hM hL

end CFSG.LocalAnalysis.GLTheoremA.HStdExcl

end
