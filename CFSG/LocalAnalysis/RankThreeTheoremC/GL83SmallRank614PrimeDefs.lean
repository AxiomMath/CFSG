module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614ExtDefs
public import CFSG.Foundations.Catalog

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

@[expose] def KFactBlockFactorThreePrime : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsKGroup X → ¬ 3 ∣ Nat.card X →
    Subgroup.centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X →
    ∀ T : Subgroup X, IsPGroup 2 T → ¬ 2 ∣ T.index →
      (⨆ (T₀ : Subgroup X) (_ : T₀ ≤ T) (_ : T₀ ≠ ⊥) (_ : (T₀.subgroupOf T).Characteristic),
        normalizer (T₀ : Set X)) = ⊤

@[expose] def GL83SmallRankProp614Core (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M : Subgroup G), SmallRankSituation G 3 P M → Group.IsSolvable M →
    Nonempty ((P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) →
    ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
      ∀ H S : Subgroup G, Prop614Extremal M (zpowers x ⊔ zpowers z) H S →
        ¬ 3 ∣ (zpowers x ⊔ zpowers z).relIndex H →
        H = normalizer (pCoreOf 2 H : Set G) →
        IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) H S →
        pCoreOf 2 H ≤ S →
        (∀ S₀ : Subgroup G, pCoreOf 2 H < S₀ → S₀ ≤ S →
          S ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (S₀ : Set G) →
          normalizer (S₀ : Set G) ≤ M) →
        (∀ S₀ : Subgroup G, S₀ ≤ S → S₀ ≠ ⊥ → (S₀.subgroupOf S).Characteristic →
          normalizer (S₀ : Set G) ≤ M) →
        rankThreePrimeCore 3 H ≤ M → False

end CFSG.LocalAnalysis.RankThreeTheoremC
