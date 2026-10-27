module

public import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport
public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4Defs

public section

namespace CFSG.HardMathSupport.Malle.OvergroupTransport

open CFSG.AGLEmbedding CFSG.Open

@[expose] def ReeF4SocleNormalizerMaximal : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex),
    IsReeFFourFiveIndex d → Nonempty (K ≃* CatGroup d) →
    ∀ P : Sylow 5 K, NormalizerMaximal (P : Subgroup K)

@[expose] def ReeF4SocleAutOrder : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex),
    IsReeFFourFiveIndex d → Nonempty (K ≃* CatGroup d) →
    Nat.card (MulAut K) ∣ 5 * Nat.card K

@[expose] def ReeF4SocleFiveRank : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex),
    IsReeFFourFiveIndex d → Nonempty (K ≃* CatGroup d) →
    ∀ P : Subgroup K, IsPGroup 5 ↥P → Open.pRank 5 P ≤ 2

@[expose] def ReeF4SocleSylowNormal : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y) (d : TauCeti.ValidLieTypeIndex),
    IsReeFFourFiveIndex d → K.Normal → Nonempty (K ≃* CatGroup d) →
    Subgroup.centralizer (K : Set Y) = ⊥ → ∀ T : Sylow 5 Y,
      3 ≤ Open.pRank 5 (T : Subgroup Y) →
      Subgroup.normalizer (((T : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) ≤
        Subgroup.normalizer ((T : Subgroup Y) : Set Y)

end CFSG.HardMathSupport.Malle.OvergroupTransport
