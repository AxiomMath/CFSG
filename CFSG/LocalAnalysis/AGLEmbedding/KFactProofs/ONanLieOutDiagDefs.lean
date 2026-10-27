module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutModels

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

@[expose] def LieOutDich : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), IsComponentOf L ⊤ →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ x ∈ Subgroup.normalizer (L : Set Y), x ^ p = 1 →
      x ∉ L ⊔ Subgroup.centralizer (L : Set Y) →
      DiagType (↥L ⧸ Subgroup.center ↥L) p ∨ LieOutConcl L x

end CFSG.AGLEmbedding.LieOut
