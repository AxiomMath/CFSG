module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Extremal
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

@[expose] def KFactBlocksInSylowCentralizerQS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (N S : Subgroup G) (z : G), p.Prime → 5 ≤ p →
    CFSG.Open.IsKGroup ↥N → CFSG.QuasithinUnique.CharTwo N →
    CFSG.QuasithinUnique.IsSylowTwoOf S N → ¬ p ∣ Nat.card N → z ∈ normalizer (N : Set G) →
    z ∈ normalizer (S : Set G) → z ^ p = 1 →
    ∀ Y : Subgroup G, CFSG.CGT.PushingUp.IsBlockOfInX N Y →
      (CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) ∨ z ∈ normalizer (Y : Set G)) →
      Y ≤ S ⊔ (N ⊓ centralizer ({z} : Set G))

@[expose] def StepL617PrimeTop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G),
    Situation G p P M → Point P M x → Central P z → ∀ H S : Subgroup G, Optimal p M x z H S →
      pCoreOf 2 (GLBPrimeCore p H ⊔ S) = pCoreOf 2 H →
      ∀ Y : Subgroup G, CFSG.CGT.PushingUp.IsBlockOfInX (GLBPrimeCore p H ⊔ S) Y →
        ¬ CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) → z ∉ normalizer (Y : Set G) → Y ≤ M

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
