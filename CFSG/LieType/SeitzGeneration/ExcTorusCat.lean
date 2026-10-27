module

public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.LieType.SeitzGeneration.ExcTorusRankE6
public import CFSG.LieType.SeitzGeneration.ExcTorusRankE7
public import CFSG.LieType.SeitzGeneration.ExcTorusRankE8

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge TauCeti


theorem rankLE1_cat_E6 (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid) {p : ℕ}
    (hp : p.Prime) (hpq : p ≠ q.p)
    (hcnt : degCount Tag.E6 (orderOf ((q.card : ℕ) : ZMod p)) ≤ 1) :
    RankLE1 p (Cat ⟨.E6 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at hcnt
  exact RankLE1.of_mulEquiv e.symm (rankLE1_E6 K hp hpK hcnt)

theorem not_rankLE2_cat_E6 (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ≠ q.p)
    (hcnt : 3 ≤ degCount Tag.E6 (orderOf ((q.card : ℕ) : ZMod p))) :
    ¬ RankLE2 p (Cat ⟨.E6 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at hcnt
  exact fun h => not_rankLE2_E6 K hp hp3 hpK hcnt (RankLE2.of_mulEquiv e h)

theorem rankLE1_cat_E7 (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid) {p : ℕ}
    (hp : p.Prime) (hpq : p ≠ q.p)
    (hcnt : degCount Tag.E7 (orderOf ((q.card : ℕ) : ZMod p)) ≤ 1) :
    RankLE1 p (Cat ⟨.E7 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at hcnt
  exact RankLE1.of_mulEquiv e.symm (rankLE1_E7 K hp hpK hcnt)

theorem not_rankLE2_cat_E7 (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ≠ q.p)
    (hcnt : 3 ≤ degCount Tag.E7 (orderOf ((q.card : ℕ) : ZMod p))) :
    ¬ RankLE2 p (Cat ⟨.E7 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at hcnt
  exact fun h => not_rankLE2_E7 K hp hp3 hpK hcnt (RankLE2.of_mulEquiv e h)

theorem rankLE1_cat_E8 (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid) {p : ℕ}
    (hp : p.Prime) (hpq : p ≠ q.p)
    (hcnt : degCount Tag.E8 (orderOf ((q.card : ℕ) : ZMod p)) ≤ 1) :
    RankLE1 p (Cat ⟨.E8 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at hcnt
  exact RankLE1.of_mulEquiv e.symm (rankLE1_E8 K hp hpK hcnt)

theorem not_rankLE2_cat_E8 (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ≠ q.p)
    (hcnt : 3 ≤ degCount Tag.E8 (orderOf ((q.card : ℕ) : ZMod p))) :
    ¬ RankLE2 p (Cat ⟨.E8 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at hcnt
  exact fun h => not_rankLE2_E8 K hp hp3 hpK hcnt (RankLE2.of_mulEquiv e h)

end CFSG.LieType.SeitzGeneration
