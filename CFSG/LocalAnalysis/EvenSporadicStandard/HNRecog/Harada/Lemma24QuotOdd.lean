module

public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

private theorem oddCore_eq_pPrimeCore_two (H : Type*) [Group H] :
    CFSG.oddCore H = CFSG.pPrimeCore 2 H := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp

theorem oddCore_normal_eq_bot {Q : Type} [Group Q] [Finite Q]
    (hO : ∀ N : Subgroup Q, N.Normal → Odd (Nat.card N) → N = ⊥) (X : Subgroup Q) [X.Normal] :
    CFSG.oddCore ↥X = ⊥ := by
  let O : Subgroup ↥X := CFSG.oddCore ↥X
  have hOeq : O = CFSG.pPrimeCore 2 ↥X := oddCore_eq_pPrimeCore_two ↥X
  have hOodd : Odd (Nat.card O) := by
    rw [hOeq]
    exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥X))
  have hnormal : (O.map X.subtype).Normal := by
    rw [hOeq]
    exact ConjAct.normal_of_characteristic_of_normal
  have hodd : Odd (Nat.card (O.map X.subtype)) := by
    rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact hOodd
  have hbot : O.map X.subtype = ⊥ := hO (O.map X.subtype) hnormal hodd
  exact (Subgroup.map_eq_bot_iff_of_injective O X.subtype_injective).mp hbot

end CFSG.EvenSporadicStandard.HNRecog.Harada
