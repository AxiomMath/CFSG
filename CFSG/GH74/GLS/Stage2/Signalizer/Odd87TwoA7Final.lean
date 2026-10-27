module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7Main
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7OddLie

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG CFSG.GH74 CFSG.GH74.GLS

theorem pumpupTwoA7_of_ghList {H : Type} [Group H] [Finite H] (L I : Subgroup H) (s : H)
    {K₀ : Type} [Group K₀] (hGH : GHList (↥L ⧸ Subgroup.center ↥L)) (hL : IsComponent L)
    (hs : orderOf s = 2) (hsI : s ∈ I) (hIL : I ≤ L)
    (hIc : IsPCompIn 2 (Subgroup.centralizer ({s} : Set H)) I) (hK₀ : IsDoubleCoverOfAlt K₀ 7)
    (hφ : ∃ φ : ↥I →* K₀, Function.Surjective φ ∧ Odd (Nat.card φ.ker)) : I = L :=
  pumpupTwoA7_of_ghList_of_oddLie twoA7OddLie L I s hGH hL hs hsI hIL hIc hK₀ hφ

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
