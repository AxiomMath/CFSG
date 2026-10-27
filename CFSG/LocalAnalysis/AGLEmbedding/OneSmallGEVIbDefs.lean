module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def IbPerfectSections (p : ℕ) {X : Type*} [Group X] (J : Subgroup X) : Prop :=
  ∀ V : Subgroup X, V ≤ J → ⁅V, V⁆ = V → ¬ p ^ 2 ∣ Nat.card V

@[expose] def KFactBlockToralIb : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), IsComponentOf L ⊤ →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → IsParabolicTwo L J → J ≠ L →
    (∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) →
    ∀ p : ℕ, p.Prime → 5 ≤ p → IbPerfectSections p J →
    ∀ x ∈ L, x ^ p = 1 → x ∉ Subgroup.centralizer (L : Set Y) →
    (∃ V : Subgroup Y, ⁅V, V⁆ = V ∧ V ≤ Subgroup.normalizer (L : Set Y) ∧
      V ≤ Subgroup.normalizer (pCoreOf 2 J : Set Y) ∧ x ∈ V) →
    (∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) →
    (∃ E : Subgroup Y, E ≤ L ⊓ Subgroup.centralizer ({x} : Set Y) ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 3) → False

@[expose] def KFactBlockOutRankIb : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), IsComponentOf L ⊤ →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → IsParabolicTwo L J → J ≠ L →
    (∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) →
    ∀ p : ℕ, p.Prime → 5 ≤ p → IbPerfectSections p J →
    ∀ E : Subgroup Y, E ≤ Subgroup.normalizer (L : Set Y) → IsElemAbelian p E →
      Nat.card E = p ^ 2 → E ⊓ (L ⊔ Subgroup.centralizer (L : Set Y)) = ⊥ → False

@[expose] def CitedBlockThreeToralIb : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G) (p : ℕ), Open.IsKGroup ↥M →
    Asc81bHyp M S → IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    NineThreeThree M S L → p.Prime → 5 ≤ p →
    IbPerfectSections p (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) →
    ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) →
      IsElemAbelian p E → Nat.card E = p ^ 3 → False

structure D1IbBlockInputs : Prop where
  h84 : Asc81bEightFour
  h85 : Asc81bEightFive
  h86 : Asc81bEightSix
  h93 : Asc81bNineThree
  hD2 : D1NoXBlock
  hK2 : KFactParabolicThree
  hC3 : CitedBlockThreeTransvection
  hK5 : KFactBlockThreeAltSeven
  hOP : KFactBlockOutPrime
  hSch : KFactCatalogSchreier
  hOR : KFactBlockOutRankIb
  hTA : KFactBlockToralIb
  hC3T : CitedBlockThreeToralIb

variable {G : Type} [Group G] [Finite G]

structure D1IbConfig (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (z : G) : Prop where
  data : D1OneSmallData p P M H R Rbar K
  elt : D1SmallCZElt p H R K z
  b0 : D1CzB0 p R z
  cz_le : Subgroup.centralizer ({z} : Set G) ≤ H
  five_le : 5 ≤ p
  not_fi22 : ¬ (p = 5 ∧ IsFi22 K)
  phase : D1PhaseThree p P M H R
  dec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i
  exp : ∀ r ∈ R, r ^ p = 1
  card_T : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
    Subgroup (H ⧸ primeComplementCore (G := H) p)) = p ^ 2
  perf : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
    ¬ p ^ 2 ∣ Nat.card V
  uniq : ∀ L₁ L₂ : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L₁ →
    IsWeakSBlock M (pCoreOf 2 H) L₂ → barM M L₁ = barM M L₂
  cover : ∃ U : Subgroup G, U ≤ H ⊓ M ∧ ⁅U, U⁆ = U ∧ z ∈ U

end CFSG.AGLEmbedding
