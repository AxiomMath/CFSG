module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIIStruct
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Cor47

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC KFactWeakClosureHeis
  GenericComponentClass u3_endgame)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G} {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
  {Shape : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Subgroup X → Prop}

theorem typeII_cor47 (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hX : ExtraFacts Typ p Shape)
    (hiso : ∀ (A B : Type) [Group A] [Group B], A ≃* B → Typ p A → Typ p B)
    (hc : PointConfig Typ G p P M x J) :
    ∀ X : Subgroup G, IsPGroup 2 X → X ≤ rankThreePrimeCore p M →
      X ≤ Subgroup.centralizer ({x} : Set G) → X = ⊥ := by
  have _hU0 := hU0
  exact CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.u3_cor47_gen hS hD1
    (CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.typeSigTrivOn_of_X hc.prime hiso
      (fun X _ _ K h => hX.sigTriv X K h))
    (typeII_S_decomp hX hc) hc

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
