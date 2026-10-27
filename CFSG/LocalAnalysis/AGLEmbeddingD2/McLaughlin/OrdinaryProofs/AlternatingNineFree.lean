module

public import CFSG.Alternating.Multipliers.Main
public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

open CFSG.RankThree.PerfectCover

theorem not_nine_dvd_card_hopfMultiplier_alternating {m : ℕ}
    (hm : 5 ≤ m) : ¬ 9 ∣ Nat.card (hopfMultiplier (alternatingGroup (Fin m))) := by
  rw [(CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput m hm).2]
  split_ifs <;> decide

theorem not_nine_dvd_card_griessHopfMultiplier_of_mulEquiv_alternating
    {S : Type} [Group S] {m : ℕ} (hm : 5 ≤ m)
    (e : S ≃* alternatingGroup (Fin m)) :
    ¬ 9 ∣ Nat.card (CFSG.Open.griessHopfMultiplier S) := by
  rw [Nat.card_congr (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv,
    Nat.card_congr (hopfMultiplierEquivGriess (alternatingGroup (Fin m))).toEquiv]
  exact not_nine_dvd_card_hopfMultiplier_alternating hm

end CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
