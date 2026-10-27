module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

structure A7ModuleData (D H V J₁ U : Subgroup G) : Prop where
  U_le : U ≤ pCoreOf 2 H
  U_central : U ≤ centralizer (pCoreOf 2 H : Set G)
  U_exp : ∀ u ∈ U, u ^ 2 = 1
  card_U : Nat.card U = 16
  U_normal : H ≤ normalizer (U : Set G)
  J₁_le : J₁ ≤ H
  D_le : D ≤ J₁
  V_le : V ≤ J₁ ⊔ pCoreOf 2 H
  comm : ∀ s ∈ pCoreOf 2 H, ∀ j ∈ J₁, s * j * s⁻¹ * j⁻¹ ∈ U
  split : ∀ w ∈ pCoreOf 2 H, w ∈ centralizer (pCoreOf 2 H : Set G) → w ^ 2 = 1 →
    w ∈ U ⊔ (pCoreOf 2 H ⊓ centralizer (J₁ : Set G))
  inter : U ⊓ centralizer (J₁ : Set G) = ⊥
  cent : V ⊓ centralizer (U : Set G) = pCoreOf 2 H
  quad : ∀ x ∈ V, x ∉ pCoreOf 2 H →
    U ⊓ centralizer ({x} : Set G) = U ⊓ centralizer (V : Set G)
  idx : Nat.card U = 4 * Nat.card (U ⊓ centralizer (V : Set G) : Subgroup G)
  three : 3 ∣ Nat.card (invariantTwoJoinIn D J₁)

end CFSG.LocalAnalysis.RankThreeTheoremC
