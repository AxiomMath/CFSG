module

public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicScalar
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LargeEvenClassification.Helpers


theorem binary_addSubgroup_card_two_finrank {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (L : AddSubgroup V)
    (hcard : Nat.card L = 2) :
    Module.finrank (ZMod 2) ((AddSubgroup.toZModSubmodule 2) L) = 1 := by
  have hcard' : Nat.card ((AddSubgroup.toZModSubmodule 2) L) = 2 := hcard
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := (AddSubgroup.toZModSubmodule 2) L)
  have h : 2 ^ Module.finrank (ZMod 2) ((AddSubgroup.toZModSubmodule 2) L) = 2 ^ 1 := by
    rw [hcard', Nat.card_eq_fintype_card, ZMod.card] at hpow
    exact hpow.symm
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) h

theorem binary_addSubgroup_distinct_lines {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (L M : AddSubgroup V)
    (hL : Nat.card L = 2) (hM : Nat.card M = 2) (hne : L ≠ M) :
    Module.finrank (ZMod 2) ((AddSubgroup.toZModSubmodule 2) L) = 1 ∧
    Module.finrank (ZMod 2) ((AddSubgroup.toZModSubmodule 2) M) = 1 ∧
    (AddSubgroup.toZModSubmodule 2) L ≠ (AddSubgroup.toZModSubmodule 2) M := by
  refine ⟨binary_addSubgroup_card_two_finrank L hL,
    binary_addSubgroup_card_two_finrank M hM, ?_⟩
  exact fun h => hne ((AddSubgroup.toZModSubmodule 2).injective h)

end CFSG.LargeEvenClassification.Helpers
