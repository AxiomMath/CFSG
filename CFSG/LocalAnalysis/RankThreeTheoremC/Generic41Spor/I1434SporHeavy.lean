module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434SporCase
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434SporS2
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434SporS1B
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434SporS1HN
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434SporS1Ly
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434SporS1M

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Blueprint

theorem i1434SporCase_holds
    : I1434SporCase := by
  have hord : I1434.SporCarrierOrders := fun s =>
    CFSG.AGLEmbedding.card_carrier_eq_sporOrd CFSG.Open.Open.monster_y443_derived_card s
  refine I1434.i1434SporCase_of_tables hord ?_
  intro s h5
  rcases (I1434.five_pow_three_dvd_sporOrd_iff s).1 h5 with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact I1434.hs_hasNonabelianFiveSubgroup
  · exact I1434.mcl_hasNonabelianFiveSubgroup
  · exact I1434.ru_hasNonabelianFiveSubgroup
  · exact I1434.co3_hasNonabelianFiveSubgroup
  · exact I1434.co2_hasNonabelianFiveSubgroup
  · exact I1434.th_hasNonabelianFiveSubgroup
  · exact I1434.co1_hasNonabelianFiveSubgroup
  · exact I1434.hn_hasNonabelianFiveSubgroup
  · exact I1434.ly_hasNonabelianFiveSubgroup
  · exact I1434.b_hasNonabelianFiveSubgroup
  · haveI : Finite NativeSporadic.M :=
      Nat.finite_of_card_ne_zero (by
        have := hord .M
        rw [show NativeSporadic.Carrier .M = NativeSporadic.M from rfl] at this
        rw [this]
        decide)
    exact I1434.m_hasNonabelianFiveSubgroup_of_finite

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
