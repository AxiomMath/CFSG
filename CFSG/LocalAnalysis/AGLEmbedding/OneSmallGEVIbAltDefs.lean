module

public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def PerfectSectionsAltSqC (p : ℕ) {X : Type*} [Group X] (J : Subgroup X) : Prop :=
  ∀ V : Subgroup X, V ≤ J → ⁅V, V⁆ = V → ∃ N : Subgroup ↥V, N.Normal ∧ ¬ p ^ 2 ∣ N.index ∧
    ∃ f : ↥V →* alternatingGroup (Fin p) × alternatingGroup (Fin p),
      p.Coprime (Nat.card ↥(f.ker ⊓ N))

theorem perfectSectionsAltSqC_of {p : ℕ} (hp : 2 ≤ p) {X : Type*} [Group X] {J : Subgroup X}
    (hJ : PerfectSectionsAltSq p J) : PerfectSectionsAltSqC p J := by
  intro V hVJ hVp
  obtain ⟨V₀, hV₀V, -, hcop, f, hf⟩ := hJ V hVJ hVp
  refine ⟨⊤, inferInstance, by simp; omega, f, ?_⟩
  rw [inf_top_eq, hf, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₀V).toEquiv.symm]
  exact hcop

@[expose] def KFactBlockToralAltIb : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), IsComponentOf L ⊤ →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → IsParabolicTwo L J → J ≠ L →
    (∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) →
    ∀ p : ℕ, (p = 5 ∨ p = 7) → PerfectSectionsAltSqC p J →
    ∀ x ∈ L, x ^ p = 1 → x ∉ Subgroup.centralizer (L : Set Y) →
    (∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) →
    ∀ W : Subgroup Y, ⁅W, W⁆ = W → W ≤ Subgroup.normalizer (L : Set Y) →
      W ≤ Subgroup.centralizer ({x} : Set Y) →
    (∃ E : Subgroup Y, E ≤ W ⊓ L ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2) → False

@[expose] def KFactBlockOutRankAltIb : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), IsComponentOf L ⊤ →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → IsParabolicTwo L J → J ≠ L →
    (∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) →
    ∀ p : ℕ, (p = 5 ∨ p = 7) → PerfectSectionsAltSqC p J →
    ∀ E : Subgroup Y, E ≤ Subgroup.normalizer (L : Set Y) → IsElemAbelian p E →
      Nat.card E = p ^ 2 → E ⊓ (L ⊔ Subgroup.centralizer (L : Set Y)) = ⊥ → False

theorem kFactBlockOutRankAlt_of_ib (h : KFactBlockOutRankAltIb) : KFactBlockOutRankAlt :=
  fun Y _ _ L J hL hcl hpar hne hnB p hp hJ E hEN hE hEc hE1 =>
    h Y L J hL hcl hpar hne hnB p hp
      (perfectSectionsAltSqC_of (by rcases hp with rfl | rfl <;> norm_num) hJ) E hEN hE hEc hE1

@[expose] def CitedBlockThreeToralAltIb : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G) (p : ℕ), Open.IsKGroup ↥M →
    Asc81bHyp M S → IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    NineThreeThree M S L → (p = 5 ∨ p = 7) →
    PerfectSectionsAltSqC p (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) →
    ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) →
      IsElemAbelian p E → Nat.card E = p ^ 3 → False

theorem citedBlockThreeToralAlt_of_ib (h : CitedBlockThreeToralAltIb) :
    CitedBlockThreeToralAlt :=
  fun G _ _ M S L p hK hA hL hX hS h3 hp hJ E hE hEl hEc =>
    h G M S L p hK hA hL hX hS h3 hp
      (perfectSectionsAltSqC_of (by rcases hp with rfl | rfl <;> norm_num) hJ) E hE hEl hEc

@[expose] def KFactAltTwoPGammaSylow : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p : ℕ), p.Prime → 5 ≤ p → IsAltTwoP p K →
    ∀ T : Sylow p K, (T : Subgroup K) ≤ perfectCore (GLBCore p 1 (T : Subgroup K))

structure D1IbAltInputs : Prop where
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
  hΓ : KFactAltTwoPGamma
  hΓS : KFactAltTwoPGammaSylow
  hOR : KFactBlockOutRankAltIb
  hTA : KFactBlockToralAltIb
  hC3T : CitedBlockThreeToralAltIb

variable {G : Type} [Group G] [Finite G]

structure D1IbAltConfig (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (z : G) : Prop where
  data : D1OneSmallData p P M H R Rbar K
  elt : D1SmallCZElt p H R K z
  b0 : D1CzB0 p R z
  cz_le : Subgroup.centralizer ({z} : Set G) ≤ H
  prime57 : p = 5 ∨ p = 7
  alt : IsAltTwoP p K
  not_fi22 : ¬ (p = 5 ∧ IsFi22 K)
  phase : D1PhaseThree p P M H R
  dec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i
  exp : ∀ r ∈ R, r ^ p = 1
  card_T : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
    Subgroup (H ⧸ primeComplementCore (G := H) p)) = p ^ 2
  card_R_le : Nat.card R ≤ p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p))
    ⊓ K : Subgroup (H ⧸ primeComplementCore (G := H) p))
  rbar_le : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
    K ⊔ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))
  out : Group.IsSolvable (ComponentClassification.OuterAutomorphisms.Outer K)
  uprime : KFactUPrime p K
  cover : ∃ V : Subgroup G, V ≤ H ⊓ M ∧ ⁅V, V⁆ = V ∧ z ∈ V ∧
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → V ≤ Subgroup.normalizer (L : Set G)

end CFSG.AGLEmbedding
