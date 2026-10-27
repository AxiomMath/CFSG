module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Kind
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SecPerm

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.GH74.GLS.Stage12

theorem not_kindFactorAll_mclly_of_index {k : Kind} (hk : k = Kind.mcl ∨ k = Kind.ly) {Y : Type} [Group Y]
    [Nontrivial Y] (hmin : ∀ H : Subgroup Y, H ≠ ⊤ → 11 < H.index) : ¬ KindFactorAll k Y := by
  rcases hk with rfl | rfl
  · rintro ⟨n, -, hn, hs⟩
    exact not_isSection_alt_of_index (n := n) (fun H hH => lt_of_le_of_lt (by omega) (hmin H hH)) hs
  · rintro ⟨n, -, hn, hs⟩
    exact not_isSection_alt_of_index (n := n) (fun H hH => lt_of_le_of_lt (by omega) (hmin H hH)) hs

theorem not_isSection_alt_seven_of_index {Y : Type} [Group Y] [Nontrivial Y]
    (hmin : ∀ H : Subgroup Y, H ≠ ⊤ → 7 < H.index) : ¬ IsSection Y (alternatingGroup (Fin 7)) :=
  not_isSection_alt_of_index hmin

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
