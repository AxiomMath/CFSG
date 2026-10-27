module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

@[expose] def KFactL34Borel : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsRankThreeL34 K → ∀ u : K, orderOf u = 3 →
    ∀ V : Subgroup K, rankTwoMaximalInvariantTwoSubgroup (zpowers u) V →
      IsSylowOf 2 V ⊤ ∧ centralizer ({u} : Set K) ⊓ V = ⊥ ∧
        zpowers u ⊔ V = normalizer (V : Set K)

@[expose] def KFactL34Graph : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal →
    centralizer (K : Set X) = ⊥ → IsRankThreeL34 ↥K →
    ∀ S : Subgroup X, S ≤ K → IsSylowOf 2 S K → ∀ u ∈ K, orderOf u = 3 →
      u ∈ normalizer (S : Set X) → ∀ W : Subgroup X, IsPGroup 2 W →
        W ≤ normalizer (S : Set X) → W ≤ centralizer ({u} : Set X) →
          Nat.card W ≤ 2 ∧ ∀ w ∈ W, w ≠ 1 → ∀ t ∈ centralizer ({u} : Set X) ⊓ K,
            w * t = t * w → t ∈ zpowers u

@[expose] def KFactL34OutThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal →
    centralizer (K : Set X) = ⊥ → IsRankThreeL34 ↥K →
    ∀ F : Subgroup X, IsPGroup 3 F → Nat.card F ≤ 3 * Nat.card (F ⊓ K : Subgroup X)

@[expose] def KFactL34SylowTransitive : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsRankThreeL34 K → ∀ (S : Sylow 3 K) (a b : K),
    a ∈ (S : Subgroup K) → b ∈ (S : Subgroup K) → a ≠ 1 → b ≠ 1 →
      ∃ n ∈ normalizer ((S : Subgroup K) : Set K), n * a * n⁻¹ = b

end CFSG.LocalAnalysis.RankThreeTheoremC
