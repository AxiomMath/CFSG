module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24ThreeClasses
public import CFSG.Sporadic.Fi24.OctadAction

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three

open CFSG.Sporadic.Fi24 (R cls lvl)

attribute [local instance] CFSG.Sporadic.Fi24.rAction

@[expose] def poH : List ℕ :=
  [19, 21, 19, 14, 13, 14, 18, 23, 15, 23, 8, 10, 18, 11, 8, 22, 6, 6, 20, 7, 25, 0, 9, 17, 20]

@[expose] def poW0 : List ℕ := [21, 16, 8, 1]

@[expose] def poW1 : List ℕ := [20, 13, 1]

@[expose] def poP0 : Fin 306936 := ⟨0, by norm_num⟩

@[expose] def poP1 : Fin 306936 := ⟨305530, by norm_num⟩


@[expose] noncomputable def poC0 : Fin 306936 := wordElt poW0 • poP0

@[expose] noncomputable def poC1 : Fin 306936 := wordElt poW1 • poP0

@[expose] noncomputable def poX : R := cls poP0 * cls poP1 * (cls poC0 * cls poC1)

@[expose] def PoLam (a : Fin 306936) : Prop :=
  a = poP0 ∨ a = poP1 ∨ a = cls poP0 • poP1 ∨ a = poC0 ∨ a = poC1 ∨ a = cls poC0 • poC1

structure Fi24PairOrbitFacts : Prop where
  h_c0 : wordElt poH • poC0 = poP0
  h_c1 : wordElt poH • poC1 = poP1
  orbit_card_ge :
    3499200 ≤ Nat.card (MulAction.orbit (lvl 2) ((poC0, poC1) : Fin 306936 × Fin 306936))
  chirality : ∀ a : Fin 306936, PoLam a → ∀ k ∈ lvl 2,
    ¬(k • poC0 = wordElt poH • a ∧ k • poC1 = wordElt poH • (poX • a))

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three

end
