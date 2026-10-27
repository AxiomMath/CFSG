module

public import CFSG.LieType.SeitzGeneration.ExcTorusThreeRank
public import CFSG.LieType.SeitzGeneration.ExcPlaneModel

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge TauCeti


theorem not_rankLE2_cat_F4_three (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid)
    (hpq : 3 ≠ q.p) : ¬ RankLE2 3 (Cat ⟨.F4 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have hpK : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne Nat.prime_three hpq
  exact fun h => not_rankLE2_F4_three K hpK (RankLE2.of_mulEquiv e h)

theorem not_rankLE2_cat_E6_three (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid)
    (hpq : 3 ≠ q.p) : ¬ RankLE2 3 (Cat ⟨.E6 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have hpK : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne Nat.prime_three hpq
  exact fun h => not_rankLE2_E6_three K hpK (RankLE2.of_mulEquiv e h)

theorem not_rankLE2_cat_E7_three (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid)
    (hpq : 3 ≠ q.p) : ¬ RankLE2 3 (Cat ⟨.E7 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have hpK : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne Nat.prime_three hpq
  exact fun h => not_rankLE2_E7_three K hpK (RankLE2.of_mulEquiv e h)

theorem not_rankLE2_cat_E8_three (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid)
    (hpq : 3 ≠ q.p) : ¬ RankLE2 3 (Cat ⟨.E8 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have hpK : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne Nat.prime_three hpq
  exact fun h => not_rankLE2_E8_three K hpK (RankLE2.of_mulEquiv e h)

end CFSG.LieType.SeitzGeneration
