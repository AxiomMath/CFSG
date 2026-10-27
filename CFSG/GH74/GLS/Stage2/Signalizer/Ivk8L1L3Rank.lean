module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Rank3

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1

open CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem fl3_elemAbelian_le_four {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime)
    (_hf : 1 ≤ f) (hp2 : p ≠ 2) (hLie : LieModel Y .PSL 3 p f)
    (E : Subgroup Y) (hE : CFSG.IsElementaryAbelian 2 ↥E) : Nat.card ↥E ≤ 4 := by
  have := hE
  exact card_elemAbelian_two_le_four_of_PSL3 hp hp2 hLie E
    ⟨hE.toIsMulCommutative, fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1
