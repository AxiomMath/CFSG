module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PlaneStruct
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupTits
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Cor47

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC GenericComponentClass)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem tits_cor47 (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hX : TitsFacts)
    (hc : PointConfig IsTitsType G 5 P M x J) :
    ∀ X : Subgroup G, IsPGroup 2 X → X ≤ rankThreePrimeCore 5 M →
      X ≤ Subgroup.centralizer ({x} : Set G) → X = ⊥ := by
  have _hU0 := hU0
  have hiso : ∀ (A B : Type) [Group A] [Group B], A ≃* B → IsTitsType 5 A → IsTitsType 5 B :=
    fun A B _ _ e h => ⟨h.1, h.2.imp fun _ hn => hn.map fun f => e.symm.trans f⟩
  exact CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.u3_cor47_gen hS hD1
    (CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.typeSigTrivOn_of_X hc.prime hiso
      (fun X _ _ K h => hX.sigTriv X K h))
    (plane_S_decomp (fun K _ _ hK => hX.sylow K hK) (fun K _ _ hK => hX.noOuter K hK) hc) hc

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
