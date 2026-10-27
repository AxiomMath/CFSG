module

public import CFSG.Open.LocalVocabulary
public import CFSG.Open.PGLModelDefs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

@[expose] def KFactL34FixedPointsGen : Prop :=
  ∀ (L : Type) [Group L] [Finite L],
    Nonempty (L ≃* CFSG.PGLModel.projSL 3 (GaloisField 2 2)) →
    ∀ F : Subgroup (MulAut L), CFSG.Open.IsElemAbelian 3 F → Nat.card F = 9 →
      ¬ F ≤ (MulAut.conj : L →* MulAut L).range →
      ∀ Y : Subgroup L, (∀ f ∈ F, f ≠ 1 → ∀ x : L, f x = x → x ∈ Y) → Y = ⊤

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
