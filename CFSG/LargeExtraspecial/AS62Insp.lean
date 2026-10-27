module

public import CFSG.LargeExtraspecial.AS35WSp4
public import CFSG.LargeExtraspecial.AS35WL43
public import CFSG.LieType.Multipliers.U42

public section

namespace CFSG.LargeExtraspecial

open CFSG.LocalAnalysis.ComponentInitial

namespace AS62

theorem w2Good_of_lieModel
    {X : Type} [Group X] [Finite X]
    (h : Blueprint.LieModel X .PSU 4 2 1 ∨ Blueprint.LieModel X .PSL 4 3 1) :
    AS35W.W2Good X := by
  rcases h with h | h
  · obtain ⟨e⟩ := CFSG.LieType.Multipliers.U42.nonempty_mulEquiv_PSp43 h
    exact AS35W.W2Good.of_mulEquiv
      (e.trans CFSG.ComponentClassification.CatFactsSmall.PSp43.psp43EquivP) AS35W.w2Good_QP45
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
    exact AS35W.W2Good.of_mulEquiv e (AS35W.l43W2Input K (by rw [hK]; norm_num))

end AS62

end CFSG.LargeExtraspecial
