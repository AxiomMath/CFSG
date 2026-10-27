module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32SharedProp31
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Cor47
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Aut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem sz32_lemma44 (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hSz : Sz32Facts)
    (hSz' : Sz32OpenFacts) (hc : PointConfig IsSz32Type G 5 P M x J) :
    ∀ X : Subgroup G, IsPGroup 2 X → X ≤ rankThreePrimeCore 5 M →
      X ≤ Subgroup.centralizer ({x} : Set G) → X = ⊥ := by
  have hiso : ∀ (A B : Type) [Group A] [Group B], A ≃* B → IsSz32Type 5 A → IsSz32Type 5 B :=
    fun A B _ _ e h => ⟨h.1, h.2.imp fun _ hn => hn.map fun f => e.symm.trans f⟩
  exact CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.u3_cor47_gen_cyc hS hD1
    (CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.typeSigTrivOn_of_X hc.prime hiso
      (fun X _ _ K h => hSz.sigTriv X K h))
    (point_prop31_ii hS hD1 hU0 hc).1 hc

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
