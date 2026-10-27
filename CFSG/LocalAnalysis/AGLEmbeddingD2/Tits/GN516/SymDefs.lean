module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.Reduction
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.EngineOver

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def AGL81I516SymOver : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ C₁ C₂ : Subgroup X, IsC118Pair T C₁ C₂ →
    ∀ L : Subgroup (X ⧸ gnC T), Open.IsComponentOf L ⊤ →
    IsChevTwo (↥L ⧸ Subgroup.center ↥L) →
    ∀ P : Subgroup (X ⧸ gnC T), IsMinOverBorel L (gnImg T T ⊓ L) P →
    ∀ S : Subgroup X, baum T ≤ S → S ≤ T → pCoreOf 2 (⊤ : Subgroup X) ≤ S → T ⊓ gnC T ≤ S →
    ∀ K M : Subgroup X, S ≤ K →
      gnImg T K = conjClosure (pElementSubgroup 2 (conjClosure P
        (gnImg T S ⊓ Subgroup.normalizer (L : Set (X ⧸ gnC T))))) (gnImg T S) ⊔ gnImg T S →
      MinParabolic K S M → CharTwo K →
      ¬ thompsonJ S ≤ Subgroup.centralizer (VZ S K : Set X) →
      ∀ hV : IsElemAbelian 2 (VZ S K), SymCaseGen K S (VZ S K) hV →
        pElementSubgroup 2 P ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
          pElementSubgroup 2 P ≤ gnImg T (Subgroup.normalizer (C₂ : Set X))

theorem agl81I516Sym_of_over (h : AGL81I516SymOver) : AGL81I516Sym := by
  intro X _ _ T hX C₁ C₂ hP L hL hch P hPb H₁ M₁ hTH hmap hmin hF hJ hV hsym
  exact h X T hX C₁ C₂ hP L hL hch P hPb T (C1GN.baum_le T) le_rfl
    (B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow) inf_le_left H₁ M₁ hTH hmap hmin hF hJ hV hsym

theorem concl1Gen_over_weak_or_sym {G : Type} [Group G] [Finite G] (hE : E23NonsolvGen)
    {C₁ C₂ K S T M : Subgroup G}
    (hP : IsC118Pair T C₁ C₂) (hT : IsPGroup 2 T) (hbS : baum T ≤ S) (hST : S ≤ T)
    (hmin : MinParabolic K S M) (hF : CharTwo K)
    (hcard : ∀ (V : Subgroup G) (hV : IsElemAbelian 2 V), V = VZ S K →
      ∀ I, E23FamGen K S V hV I →
        (∀ L ∈ I, ∃ n : ℕ, 2 ≤ n ∧
          CFSG.Quasithin.E2.IsL2Natural L (fixV (autI hV (twoResidual K))) n) →
          twoResidual K ≤ thompsonJ K → I.card < 2) :
    Concl1Gen C₁ C₂ K S ∨
      (¬ thompsonJ S ≤ Subgroup.centralizer (VZ S K : Set G) ∧
        ∃ hV : IsElemAbelian 2 (VZ S K), SymCaseGen K S (VZ S K) hV) :=
  cases_over_weak hE hP hT hbS hST hmin hF hcard Or.inl fun hV hJ hsym => Or.inr ⟨hJ, hV, hsym⟩

end CFSG.AGLEmbeddingD2.Tits.GN516
