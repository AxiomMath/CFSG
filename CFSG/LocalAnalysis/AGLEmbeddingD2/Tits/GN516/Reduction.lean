module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.OverT
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Print516

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def AGL81I516Hard : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ C₁ C₂ : Subgroup X, IsC118Pair T C₁ C₂ →
    ∀ L : Subgroup (X ⧸ gnC T), Open.IsComponentOf L ⊤ →
    IsChevTwo (↥L ⧸ Subgroup.center ↥L) →
    ∀ P : Subgroup (X ⧸ gnC T), IsMinOverBorel L (gnImg T T ⊓ L) P →
    ∀ H₁ M₁ : Subgroup X, T ≤ H₁ →
      gnImg T H₁ = conjClosure (pElementSubgroup 2 (conjClosure P
        (gnImg T T ⊓ Subgroup.normalizer (L : Set (X ⧸ gnC T))))) (gnImg T T) ⊔ gnImg T T →
      MinParabolic H₁ T M₁ → CharTwo H₁ → GNHardCase H₁ T →
        pElementSubgroup 2 P ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
          pElementSubgroup 2 P ≤ gnImg T (Subgroup.normalizer (C₂ : Set X))

theorem agl81I516_of_hard (hE : E23NonsolvGen) (hK : KFactChevMinParabolic)
    (hH : AGL81I516Hard) : GN.AGL81I516 := by
  intro X _ _ T hX C₁ C₂ hP L hL hch P hPb
  rcases parabolic_or_hardCase hE hK hX hP hL hch hPb with h | ⟨H₁, M₁, hTH, hmap, hmin, hF, hhard⟩
  · exact h
  · exact hH X T hX C₁ C₂ hP L hL hch P hPb H₁ M₁ hTH hmap hmin hF hhard

@[expose] def AGL81I516NatMulti : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ C₁ C₂ : Subgroup X, IsC118Pair T C₁ C₂ →
    ∀ L : Subgroup (X ⧸ gnC T), Open.IsComponentOf L ⊤ →
    IsChevTwo (↥L ⧸ Subgroup.center ↥L) →
    ∀ P : Subgroup (X ⧸ gnC T), IsMinOverBorel L (gnImg T T ⊓ L) P →
    ∀ H₁ M₁ : Subgroup X, T ≤ H₁ →
      gnImg T H₁ = conjClosure (pElementSubgroup 2 (conjClosure P
        (gnImg T T ⊓ Subgroup.normalizer (L : Set (X ⧸ gnC T))))) (gnImg T T) ⊔ gnImg T T →
      MinParabolic H₁ T M₁ → CharTwo H₁ →
      ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H₁ : Set X) →
      ∀ hV : IsElemAbelian 2 (VZ T H₁), NatCaseGen H₁ T (VZ T H₁) hV →
      (∀ I, E23FamGen H₁ T (VZ T H₁) hV I →
          (∀ L ∈ I, ∃ n : ℕ, 2 ≤ n ∧ CFSG.Quasithin.E2.IsL2Natural L
            (fixV (autI hV (twoResidual H₁))) n) → 2 ≤ I.card) →
        pElementSubgroup 2 P ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
          pElementSubgroup 2 P ≤ gnImg T (Subgroup.normalizer (C₂ : Set X))

@[expose] def AGL81I516Sym : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ C₁ C₂ : Subgroup X, IsC118Pair T C₁ C₂ →
    ∀ L : Subgroup (X ⧸ gnC T), Open.IsComponentOf L ⊤ →
    IsChevTwo (↥L ⧸ Subgroup.center ↥L) →
    ∀ P : Subgroup (X ⧸ gnC T), IsMinOverBorel L (gnImg T T ⊓ L) P →
    ∀ H₁ M₁ : Subgroup X, T ≤ H₁ →
      gnImg T H₁ = conjClosure (pElementSubgroup 2 (conjClosure P
        (gnImg T T ⊓ Subgroup.normalizer (L : Set (X ⧸ gnC T))))) (gnImg T T) ⊔ gnImg T T →
      MinParabolic H₁ T M₁ → CharTwo H₁ →
      ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H₁ : Set X) →
      ∀ hV : IsElemAbelian 2 (VZ T H₁), SymCaseGen H₁ T (VZ T H₁) hV →
        pElementSubgroup 2 P ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
          pElementSubgroup 2 P ≤ gnImg T (Subgroup.normalizer (C₂ : Set X))

theorem agl81I516Hard_of_branches (hN : AGL81I516NatMulti) (hS : AGL81I516Sym) :
    AGL81I516Hard := by
  intro X _ _ T hX C₁ C₂ hP L hL hch P hPb H₁ M₁ hTH hmap hmin hF ⟨hJ, hV, hc⟩
  rcases hc with ⟨hnat, hall⟩ | hsym
  · exact hN X T hX C₁ C₂ hP L hL hch P hPb H₁ M₁ hTH hmap hmin hF hJ hV hnat hall
  · exact hS X T hX C₁ C₂ hP L hL hch P hPb H₁ M₁ hTH hmap hmin hF hJ hV hsym

end CFSG.AGLEmbeddingD2.Tits.GN516
