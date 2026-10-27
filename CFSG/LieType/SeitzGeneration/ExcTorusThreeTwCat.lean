module

public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw
public import CFSG.LieType.SeitzGeneration.ExcTorusThreeTwRank

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti


theorem not_rankLE2_cat_twistedE6_three (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid)
    (hpq : 3 ≠ q.p) : ¬ RankLE2 3 (Cat ⟨.twistedE6 q, hv⟩) := by
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have hpK : ¬ 3 ∣ q.p ^ q.exponent := by
    rw [← TauCeti.PrimePower.card_def]
    exact not_dvd_card_of_ne Nat.prime_three hpq
  exact fun h => not_rankLE2_twistedE6_three q.prime_p q.exponent_pos K hK σ hσ hpK
    (RankLE2.of_mulEquiv e h)

end CFSG.LieType.SeitzGeneration
