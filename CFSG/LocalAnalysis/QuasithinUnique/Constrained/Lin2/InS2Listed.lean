module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedW

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def ListedLin2OddRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S K L : Subgroup G) (z : G) (n : ℕ),
    1 < n → IsShort2 L → IsLin2Type L n → blockZ L = ⊥ → L ≤ K → CFSG.IsQuasisimple ↥K →
      IsListedComponentW M S K z →
        ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ n - 1 ∧ 2 ≤ CFSG.Open.pRank p K

end CFSG.QuasithinUnique.Lin2
