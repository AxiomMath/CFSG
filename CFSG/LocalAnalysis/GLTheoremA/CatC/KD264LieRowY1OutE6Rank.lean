module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutLinCat
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open

theorem y1out_five_le_pRank_top_of_card_ge {G : Type} [Group G] [Finite G] {E : Subgroup G}
    (hE : IsElemAbelian 3 E) (h : 243 ≤ Nat.card E) : 5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPG : IsPGroup 3 E := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hE.2 g g.2)⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (G := E)).1 hPG
  have hm5 : 5 ≤ m := by
    by_contra hlt
    have h4 : m ≤ 4 := by omega
    have : 3 ^ m ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) h4
    omega
  exact hm5.trans (le_pRank_of_elemAbelian_card (p := 3) (by norm_num) le_top hE hm)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie
