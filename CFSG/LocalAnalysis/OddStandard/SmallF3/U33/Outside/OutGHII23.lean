module

public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import CFSG.GH74.GLS.Bg.TwoGroups.Vocab
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open CFSG.GH74.GLS.Bg.TwoGroups

@[expose] def GHII23List : Prop :=
  ∀ (P : Type) [Group P] (ι : P →* MulAut (E2 4)), Function.Injective ι → ¬ IsSolvable P →
    O2 (⊤ : Subgroup P) = ⊥ →
      Nonempty (P ≃* alternatingGroup (Fin 8)) ∨ Nonempty (P ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (P ≃* Equiv.Perm (Fin 6)) ∨ Nonempty (P ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (P ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty (P ≃* Equiv.Perm (Fin 5)) ∨ Nonempty (P ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (P ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 5)) ∨
      ∃ L : Subgroup P, L.index = 2 ∧
        Nonempty (L ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 5))

private lemma card_alt8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
