module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def KFactChevMinParabolic : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L R P : Subgroup Y), Open.IsQuasisimple ↥L →
    IsChevTwo (↥L ⧸ Subgroup.center ↥L) → R ≤ Subgroup.normalizer (L : Set Y) →
    IsPGroup 2 R → IsSylowTwoOf (R ⊓ L) L → IsMinOverBorel L (R ⊓ L) P →
      (∃ M : Subgroup Y, MinParabolic (pElementSubgroup 2 (conjClosure P R) ⊔ R) R M) ∧
      (conjClosure P R ≠ L →
        ⁅pCoreOf 2 (twoResidual (pElementSubgroup 2 (conjClosure P R))),
          twoResidual (pElementSubgroup 2 (conjClosure P R))⁆ ≠ ⊥)

@[expose] def KFactChevGenThree : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L S₀ : Subgroup Y), Open.IsQuasisimple ↥L →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → IsSylowTwoOf S₀ L →
      ∃ Ps : Set (Subgroup Y), (∀ P ∈ Ps, IsMinOverBorel L S₀ P) ∧
        L = (⨆ P ∈ Ps, pElementSubgroup 2 P) ∧
        ∀ P ∈ Ps, ∃ x ∈ pElementSubgroup 2 P, orderOf x = 3 ∧
          x ∉ (Subgroup.center ↥L).map L.subtype

@[expose] def KFactChevGenCentre : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L S₀ : Subgroup Y), Open.IsQuasisimple ↥L →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → IsSylowTwoOf S₀ L →
      ∃ Ps : Set (Subgroup Y), (∀ P ∈ Ps, IsMinOverBorel L S₀ P) ∧
        L = (⨆ P ∈ Ps, pElementSubgroup 2 P) ∧
        ∀ P ∈ Ps, ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card (Subgroup.center ↥L) →
          ∃ x ∈ pElementSubgroup 2 P, orderOf x = p ∧ x ∉ (Subgroup.center ↥L).map L.subtype

end CFSG.AGLEmbeddingD2.GN
