module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycNodes
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSpinMinus

public section

namespace CFSG.AGLEmbedding.BlockCyc

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

theorem hasE9_of_model_pomegaPlus {Y : Type} [Group Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaPlus n 2 f) : HasE9 Y := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hn3 : 3 ≤ n := by omega
  refine (borelQuotient_spinPlus hn3 e).hasE9_of_nodes
    (i := (⟨2, by show 2 < n; omega⟩ : Fin n)) (j := (⟨0, by show 0 < n; omega⟩ : Fin n)) ?_ ?_
    (hasSL2Node_spinPlus hn3 _).hasOrderThree (hasSL2Node_spinPlus hn3 _).hasOrderThreeNC
  · simp [plusDatum, cartanD, Fin.ext_iff]
    omega
  · intro hij
    have := congrArg Fin.val hij
    simp at this

theorem hasE9_of_model_pomegaMinus {Y : Type} [Group Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaMinus n 2 f) : HasE9 Y := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hn4 : 4 ≤ n := by omega
  have h0 : 0 + 1 < n - 1 := by omega
  refine (borelQuotient_spinMinus hirr hn4 e).hasE9_of_nodes
    (i := (⟨2, by show 2 < n - 1; omega⟩ : Fin (n - 1)))
    (j := (⟨0, by show 0 < n - 1; omega⟩ : Fin (n - 1))) ?_ ?_
    (hasOrderThree_spinMinus hirr _) (hasSL2Node_spinMinus_long hirr h0).hasOrderThreeNC
  · simp [minusDatum, cartanB, Fin.ext_iff]
  · intro hij
    have := congrArg Fin.val hij
    simp at this

end CFSG.AGLEmbedding.BlockCyc
