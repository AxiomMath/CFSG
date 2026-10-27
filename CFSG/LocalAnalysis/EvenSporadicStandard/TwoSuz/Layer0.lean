module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Suz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Center

public section

namespace CFSG.EvenSporadicStandard.TwoSuz

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.SuzOddCore
open CFSG.EvenSporadicStandard.Finkelstein77 (innAut Asc76Lemma25)

section Out

theorem index_dvd_two_of_isSporadic_suz {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .Suz) :
    (innAut Y).index ∣ 2 := by
  obtain ⟨e₀⟩ := h
  have e : Y ≃* suzM := e₀.trans suzEquivM
  have hZ : center Y = ⊥ := HypOne.center_eq_bot_of_mulEquiv e.symm HypOne.Suz.center_suzM
  have hcard : Nat.card (MulAut Y) ≤ 2 * Nat.card Y := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv, Nat.card_congr e.toEquiv,
      ← Nat.card_congr HypOne.Suz.autEquiv.toEquiv]
    exact HypOne.Suz.card_suzT_le
  exact HypOne.index_dvd_two_of_card_le (HypOne.conj_injective_of_center_eq_bot hZ) hcard

end Out

end CFSG.EvenSporadicStandard.TwoSuz
