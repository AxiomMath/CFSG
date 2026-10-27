module

public import CFSG.Sporadic.Fi24.Simple

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three

open CFSG.Perm

@[expose] def repWords : Fin 5 → List ℕ :=
  ![[18], [16, 19], [14, 16, 16, 14, 16, 16], [16], [2]]

@[expose] noncomputable def wordElt (w : List ℕ) :
    CFSG.Sporadic.Fi24.J :=
  (w.map (pairG CFSG.Sporadic.Fi24.gs)).prod

@[expose] noncomputable def fi24Rep3 (i : Fin 5) :
    CFSG.Sporadic.Fi24.J :=
  wordElt (repWords i)

@[expose] def Fi24ThreeClasses : Prop :=
  ∀ s : CFSG.Sporadic.Fi24.J, orderOf s = 3 → ∃ i : Fin 5, IsConj s (fi24Rep3 i)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
