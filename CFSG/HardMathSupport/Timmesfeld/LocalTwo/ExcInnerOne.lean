module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSplit
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerBase

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.TauCetiBridge

set_option linter.unusedSectionVars false

section Classes

theorem innerPlaneBalanceAt_G2_one : InnerPlaneBalanceAt .G2 1 := by
  intro q hv p hp hp7 _ hpq he
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
  have h1 : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact dvd_sub_one_of_orderOf_eq_one (hK ▸ Nat.card_pos) he
  exact InnerPlaneBalance.of_mulEquiv e (innerPlanes_adjointG2_of_dvd_sub_one hp (by omega) h1)

theorem innerPlaneBalanceAt_F4_one : InnerPlaneBalanceAt .F4 1 := by
  intro q hv p hp hp7 _ hpq he
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have h1 : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact dvd_sub_one_of_orderOf_eq_one (hK ▸ Nat.card_pos) he
  exact InnerPlaneBalance.of_mulEquiv e (innerPlanes_adjointF4_of_dvd_sub_one' hp (by omega) h1)

theorem innerPlaneBalanceAt_E6_one : InnerPlaneBalanceAt .E6 1 := by
  intro q hv p hp hp7 _ hpq he
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have h1 : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact dvd_sub_one_of_orderOf_eq_one (hK ▸ Nat.card_pos) he
  exact InnerPlaneBalance.of_mulEquiv e (innerPlanes_adjointE6_of_dvd_sub_one hp hp7 h1)

theorem innerPlaneBalanceAtP_E7_one : InnerPlaneBalanceAtP .E7 1 fun p => 11 ≤ p := by
  intro q hv p hp hp7 hp11 hpq he
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have h1 : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact dvd_sub_one_of_orderOf_eq_one (hK ▸ Nat.card_pos) he
  exact InnerPlaneBalance.of_mulEquiv e (innerPlanes_adjointE7_of_dvd_sub_one hp hp11 h1)

theorem innerPlaneBalanceAtP_E8_one : InnerPlaneBalanceAtP .E8 1 fun p => 11 ≤ p := by
  intro q hv p hp hp7 hp11 hpq he
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have h1 : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact dvd_sub_one_of_orderOf_eq_one (hK ▸ Nat.card_pos) he
  exact InnerPlaneBalance.of_mulEquiv e (innerPlanes_adjointE8_of_dvd_sub_one hp hp11 h1)

theorem crossCharInnerAt_E6_dvd_sub_one :
    CrossCharInnerAt .E6 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .E6 q ∧ 7 ≤ p ∧
      p ∣ q.card - 1 := by
  rintro ⟨d, hv⟩ hk p hp hp2 hc ⟨q, hd, hp7, hpq⟩
  change d = _ at hd
  subst hd
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  rw [← hK] at hpq
  exact (isInnerLocallyBalanced_of_innerPlanes hp
    (innerPlanes_adjointE6_of_dvd_sub_one hp hp7 hpq)).of_mulEquiv e

theorem crossCharInnerAt_E7_dvd_sub_one :
    CrossCharInnerAt .E7 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .E7 q ∧ 11 ≤ p ∧
      p ∣ q.card - 1 := by
  rintro ⟨d, hv⟩ hk p hp hp2 hc ⟨q, hd, hp11, hpq⟩
  change d = _ at hd
  subst hd
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  rw [← hK] at hpq
  exact (isInnerLocallyBalanced_of_innerPlanes hp
    (innerPlanes_adjointE7_of_dvd_sub_one hp hp11 hpq)).of_mulEquiv e

theorem crossCharInnerAt_E8_dvd_sub_one :
    CrossCharInnerAt .E8 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .E8 q ∧ 11 ≤ p ∧
      p ∣ q.card - 1 := by
  rintro ⟨d, hv⟩ hk p hp hp2 hc ⟨q, hd, hp11, hpq⟩
  change d = _ at hd
  subst hd
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  rw [← hK] at hpq
  exact (isInnerLocallyBalanced_of_innerPlanes hp
    (innerPlanes_adjointE8_of_dvd_sub_one hp hp11 hpq)).of_mulEquiv e

end Classes

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
