module

public import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
import CFSG.RankThree.PartTwo.KFacts.KS14Sz
import CFSG.LieType.Ree.SuzukiOrder
import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Arith

public section

namespace CFSG.AGLEmbedding


theorem kFactThreeOrFiveDvd : KFactThreeOrFiveDvd := by
  intro Y _ _ _ hnab hcat
  by_cases h3 : 3 ∣ Nat.card Y
  · exact Or.inl h3
  right
  obtain ⟨f, -, a, -, K, _, _, rfl, hK, ⟨e⟩⟩ :=
    RankThree.PartTwo.KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd Y hnab hcat h3
  rw [Nat.card_congr e.toEquiv, LieType.Ree.suzuki_order hK]
  exact (SignalizerFunctorTheorem.McBride.SzModel.five_dvd_sq_add_one a).mul_left _

end CFSG.AGLEmbedding
