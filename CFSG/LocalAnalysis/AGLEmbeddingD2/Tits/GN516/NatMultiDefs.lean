module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.CardGN
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BlockLiftQ
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def NatMultiBaumStab : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
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
        baum T ≤ gnStab T (Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓
          Subgroup.normalizer (P : Set (X ⧸ gnC T)))

@[expose] def KPCardOne : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ L : Subgroup (X ⧸ gnC T), Open.IsComponentOf L ⊤ →
    IsChevTwo (↥L ⧸ Subgroup.center ↥L) →
    ∀ P : Subgroup (X ⧸ gnC T), IsMinOverBorel L (gnImg T T ⊓ L) P →
    ∀ K M : Subgroup X,
      K.map (QuotientGroup.mk' (gnC T)) = pElementSubgroup 2 P ⊔ (gnImg T T ⊓
        (Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓ Subgroup.normalizer (P : Set (X ⧸ gnC T)))) →
      MinParabolic K (gnStab T (Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓
        Subgroup.normalizer (P : Set (X ⧸ gnC T)))) M → CharTwo K →
      ∀ (V : Subgroup X) (hV : IsElemAbelian 2 V),
        V = VZ (gnStab T (Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓
          Subgroup.normalizer (P : Set (X ⧸ gnC T)))) K →
        ∀ I, E23FamGen K (gnStab T (Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓
            Subgroup.normalizer (P : Set (X ⧸ gnC T)))) V hV I →
          (∀ L' ∈ I, ∃ n : ℕ, 2 ≤ n ∧
            CFSG.Quasithin.E2.IsL2Natural L' (fixV (autI hV (twoResidual K))) n) →
            twoResidual K ≤ thompsonJ K → I.card < 2

theorem kPCardOne_of_levi (hK : KFactChevMinParabolic) (hLP : KFactChevMinParabolicLevi) :
    KPCardOne := by
  intro X _ _ T hX L hL hch P hPb
  exact hcard_of_gn hK hX hL hch hPb fun _ => hLP _ L (gnImg T T ⊓ L) P hL.2.2 hch
    (Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf hX.sylow hL.2.1) hPb

end CFSG.AGLEmbeddingD2.Tits.GN516
