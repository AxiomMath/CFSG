module

public import CFSG.CGT.PushingUpLit.SolKNA.Adapters
public import CFSG.CGT.PushingUpLit.SolKNA.BranchC2
public import CFSG.CGT.PushingUpLit.SolKNA.BranchC4
public import CFSG.CGT.PushingUpLit.SolKNA.PairLemma
public import CFSG.CGT.PushingUpLit.SolKNA.Residue

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.CGT.PushingUpLit.SolKAb (STSetting)

section Top

set_option linter.unusedSectionVars false


theorem rankGe2_of_analysis (han : ∀ (G : Type) [Group G] [Finite G] (K R T : Subgroup G) (g : G),
    NAConfig G K R T g → False) : SolomonTimmesfeldMainRankGe2 := by
  intro G _ _ hKP hs hna K hK hM hFs R hnc hrk
  have S : STSetting G K := ⟨hs, hna, hK, hM, hFs⟩
  rcases mtOutcome_or_exists_config S R hnc hrk with h | ⟨R₁, T, g, cfg⟩
  · exact h
  · exact (han G _ R₁ T g cfg).elim

theorem rankGe2_of_szAbelian (hSz : Lemma18SzAbelian) : SolomonTimmesfeldMainRankGe2 :=
  rankGe2_of_analysis fun G _ _ _ _ _ _ cfg =>
    analysis (G := G)
      ⟨fun cfg h4 => caseII4_false hSz cfg h4,
        fun cfg h5 h => II5.false_of_normal cfg h5 h,
        fun cfg h5 h => caseII5_not_normal_false cfg h5 h⟩ cfg

end Top

end CFSG.CGT.PushingUpLit.SolKNA
