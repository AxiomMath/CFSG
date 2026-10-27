module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenDefs
public import CFSG.Quasithin.Background.C118WeakPair
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenExtract
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenLift10
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenCore

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem concl1Gen_of_symCase_of_radFree_weak {C₁ C₂ H T M V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hP : IsC118WeakPair T C₁ C₂) (hmin : MinParabolic H T M) (hF : CharTwo H)
    (hred : IsTwoReducedIn H V) (hVZ : V = VZ T H)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) (hSym : SymCaseGen H T V hV)
    (hR : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H ∨ C₁ ≤ centerOf H ∨
      H ≤ Subgroup.normalizer (C₂ : Set G)) :
    Concl1Gen C₁ C₂ H T := by
  rcases hR with hRad | h1 | h2
  · obtain ⟨N, Y, s, ⟨d⟩⟩ := exists_genSetting_data hV hmin hF hred hVZ hJ hRad hSym
    rcases s.dichotomy_weak hP with h | h | ⟨hY, hA3⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · obtain ⟨x, hxY, hx3, hxL, hxth⟩ := SymLift.exists_x (s := s) (d := d)
      exact Or.inr (Or.inr
        (SymLift.XData.oneBlock (s := s) (d := d) ⟨hxY, hx3, hxL, hxth⟩ hY.1 hA3 hRad))
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)

end CFSG.AGLEmbeddingD2.GN
