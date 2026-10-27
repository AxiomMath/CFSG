module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGCfg

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

structure KGData3Pre {G : Type} [Group G] [Finite G] (p : ℕ) (H D S B L M : Subgroup G) (z : G) :
    Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  D_le_H : D ≤ H
  H_le_D : H ≤ normalizer (D : Set G)
  D_two : IsPGroup 2 D
  D_le_M : D ≤ M
  D_lt_S : D < S
  S_le_H : S ≤ H
  S_le_M : S ≤ M
  S_two : IsPGroup 2 S
  B_le_H : B ≤ H
  B_le_M : B ≤ M
  B_elem : IsElemAbelian p B
  B_card : Nat.card B = p ^ 2
  z_mem_B : z ∈ B
  z_order : orderOf z = p
  B_le_S : B ≤ normalizer (S : Set G)
  max_S : ∀ S' : Subgroup G, S' ≤ H → IsPGroup 2 S' → B ≤ normalizer (S' : Set G) → S ≤ S' →
    S' = S
  cover : ∀ S₀ : Subgroup G, D < S₀ → S₀ ≤ S → S ⊔ B ≤ normalizer (S₀ : Set G) →
    normalizer (S₀ : Set G) ≤ M
  cover_Z : normalizer (zpowers z : Set G) ≤ M
  L_sec : S622IsSimpleSection L D
  L_le_H : L ≤ H
  z_mem_L : z ∈ L
  L_rank : CFSG.Open.pRank p L ≤ 1
  L_not_le : ¬ L ≤ M
  M_le_L : M ⊓ H ≤ normalizer (L : Set G)
  charTwo : H ⊓ centralizer (D : Set G) ≤ D
  rank_H : CFSG.Open.pRank p H ≤ 2
  catalog : ∀ X : Subgroup G, X ≤ H → CFSG.AGLEmbedding.CatalogSimpleSections ↥X
  char_le : ∀ S₀ : Subgroup G, S₀ ≤ S → S₀ ≠ ⊥ → (S₀.subgroupOf S).Characteristic →
    normalizer (S₀ : Set G) ≤ M

variable {G : Type} [Group G] [Finite G] {p : ℕ} {H D S B L M : Subgroup G} {z : G}

theorem KGData3Pre.toKGData3 (d : KGData3Pre p H D S B L M z) : KGC.KGData3 p H D S B L M z :=
  ⟨⟨d.prime, d.five_le, d.D_le_H, d.H_le_D, d.D_two, d.D_le_M, d.D_lt_S, d.S_le_H, d.S_le_M,
    d.S_two, d.B_le_H, d.B_le_M, d.B_elem, d.B_card, d.z_mem_B, d.z_order, d.B_le_S, d.max_S,
    d.cover, d.cover_Z, d.L_sec, d.L_le_H, d.z_mem_L, d.L_rank, d.L_not_le, d.M_le_L⟩,
    d.charTwo, d.rank_H, d.catalog, d.char_le⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
