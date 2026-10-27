module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenDefs
public import CFSG.Quasithin.Background.C118WeakPair
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenNatCase
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenSolvC126
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenType

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem cases_weak (hE : E23NonsolvGen) {C₁ C₂ H T M : Subgroup G} {Q : Prop}
    (hP : IsC118WeakPair T C₁ C₂) (hmin : MinParabolic H T M) (hF : CharTwo H)
    (hQ : Concl1Gen C₁ C₂ H T → Q)
    (hnat : ∀ hV : IsElemAbelian 2 (VZ T H), IsTwoReducedIn H (VZ T H) →
      ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G) → NatCaseGen H T (VZ T H) hV → Q)
    (hsym : ∀ hV : IsElemAbelian 2 (VZ T H), IsTwoReducedIn H (VZ T H) →
      ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G) → SymCaseGen H T (VZ T H) hV → Q) :
    Q := by
  obtain ⟨-, hVel, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo hmin.isSylow hF (le_refl _)
  obtain ⟨-, h1Z, -, h2B, h2char, -⟩ := id hP
  by_cases hJ : thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G)
  · rcases C1Pack.c126_case_B h1Z h2B h2char hmin hF hJ with h | h
    · exact hQ (Or.inl h)
    · exact hQ (Or.inr (Or.inl h))
  · have hc := e23ConclGen_of_inputs hE hVel hmin hF hred hJ
    rcases case_split_gen hVel T hred.2.1 hc with hsolv | hnat' | hsym'
    · exact hQ (concl1Gen_of_perfectCore_le_weak hP hmin hF hsolv)
    · exact hnat hVel hred hJ hnat'
    · exact hsym hVel hred hJ hsym'

end CFSG.AGLEmbeddingD2.GN
