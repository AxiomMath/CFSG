module

public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CZDefs
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.Open

structure O98Red (X : Type) [Group X] [Finite X] (E Y S : Subgroup X) (z : X) : Prop where
  catalog : CFSG.AGLEmbedding.CatalogSimpleSections X
  core : CFSG.pPrimeCore 3 X = ⊥
  elem_E : IsElemAbelian 3 E
  card_E : Nat.card E = 9
  E_le : E ≤ Y
  gamma_le : rankThreeGamma 1 3 E ≤ Y
  rank_Y : pRank 3 Y ≤ 3
  rank23 : ∀ T : Subgroup X, T ≠ ⊥ → IsPGroup 2 T →
    pRank 3 (Subgroup.normalizer (T : Set X)) ≤ 3
  two_S : IsPGroup 2 S
  S_le : S ≤ Y
  normal_S : ∀ y ∈ Y, ∀ s ∈ S, y * s * y⁻¹ ∈ S
  center_z : z ∈ Subgroup.center X
  order_z : orderOf z = 3

@[expose] def KFactThreeFiveInner : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.AGLEmbedding.CatalogSimpleSections X →
    ∀ K E : Subgroup X, K.Normal → CFSG.IsQuasisimple ↥K → CFSG.pPrimeCore 3 ↥K = ⊥ →
      IsElemAbelian 3 E → Nat.card E = 9 →
      (∀ T : Subgroup X, T ≠ ⊥ → IsPGroup 2 T →
        pRank 3 (Subgroup.normalizer (T : Set X)) ≤ 3) →
      pRank 3 (rankThreeGamma 1 3 E) ≤ 3 → ¬ K ≤ rankThreeGamma 1 3 E →
      ∃ e ∈ E, e ≠ 1 ∧ ∃ k ∈ K, ∀ y ∈ K, e * y * e⁻¹ = k * y * k⁻¹

@[expose] def KFactThreeSevenTwoThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.AGLEmbedding.CatalogSimpleSections X →
    ∀ K E S : Subgroup X, K.Normal → CFSG.IsQuasisimple ↥K → CFSG.pPrimeCore 3 ↥K = ⊥ →
      IsElemAbelian 3 E → Nat.card E = 9 →
      (∀ T : Subgroup X, T ≠ ⊥ → IsPGroup 2 T →
        pRank 3 (Subgroup.normalizer (T : Set X)) ≤ 3) →
      pRank 3 (rankThreeGamma 1 3 E) ≤ 3 → ¬ K ≤ rankThreeGamma 1 3 E →
      IsPGroup 2 S → rankThreeGamma 1 3 E ≤ Subgroup.normalizer (S : Set X) →
      ¬ S ≤ Subgroup.centralizer (K : Set X) →
      (CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsL34Type ↥K ∧ ∀ r : ℕ, r.Prime →
          r ∣ Nat.card ↥(K ⊓ Subgroup.normalizer (S : Set X)) → r = 2 ∨ r = 3) ∨
        CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsA11Type ↥K

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
