module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

@[expose] def FiveCentralizesTwo (q : ℕ) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W],
    Module.finrank (ZMod q) W ≤ 3 → ∀ R : Subgroup (Module.End (ZMod q) W)ˣ, IsPGroup 2 R →
    ∀ y : (Module.End (ZMod q) W)ˣ, (∃ k : ℕ, y ^ (5 ^ k) = 1) →
    y ∈ Subgroup.normalizer (R : Set (Module.End (ZMod q) W)ˣ) → ∀ x ∈ R, y * x = x * y

@[expose] def SimilitudeThreeAbelian (q : ℕ) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W],
    Module.finrank (ZMod q) W = 4 → ∀ B : LinearMap.BilinForm (ZMod q) W,
    (∀ u : W, (∀ v : W, B u v = 0) → u = 0) → (∀ w : W, B w w = 0) →
    ∀ T : Subgroup (Module.End (ZMod q) W)ˣ, IsPGroup 3 T →
    (∀ t ∈ T, ∃ c : ZMod q, ∀ u v : W,
      B ((t : Module.End (ZMod q) W) u) ((t : Module.End (ZMod q) W) v) = c * B u v) →
    IsMulCommutative T

@[expose] def LThreeFourTwoLocal (K : Type) [Group K] : Prop :=
  ∃ E : Subgroup K, IsPGroup 2 E ∧ ∃ y ∈ Subgroup.normalizer (E : Set K), orderOf y = 5 ∧
    ∃ x ∈ E, y * x ≠ x * y

@[expose] def LThreeFourThreeLocal (K : Type) [Group K] : Prop :=
  ∃ E : Subgroup K, IsPGroup 3 E ∧ IsMulCommutative E ∧
    ∃ a ∈ Subgroup.normalizer (E : Set K), ∃ b ∈ Subgroup.normalizer (E : Set K),
      ∀ g ∈ ({a, b, a * b} : Set K),
        (∀ e ∈ E, g ^ 4 * e * (g ^ 4)⁻¹ = e) ∧ ∃ e ∈ E, g ^ 2 * e * (g ^ 2)⁻¹ ≠ e

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

namespace CFSG.LocalAnalysis.RankThreeTheoremC

@[expose] def KFactLThreeFourAutSection : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 3 →
    ∀ (V : Type) [Group V] [Finite V], IsPGroup q V → CFSG.Open.pRank q (⊤ : Subgroup V) ≤ 3 →
    ∀ (A : Subgroup (MulAut V)) (K : Type) [Group K], CFSG.AGLEmbedding.IsLinThreeFour K →
    ∀ φ : ↥A →* K, ¬ Function.Surjective φ

end CFSG.LocalAnalysis.RankThreeTheoremC
