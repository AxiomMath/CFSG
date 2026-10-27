module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactSmallOrbitsCube : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 → Nat.card T = p ^ 3 →
      (∀ X : Subgroup K, X ≤ T →
        (∀ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), ∀ x ∈ X, n * x * n⁻¹ ∈ X) →
        Nat.card X ≠ p ^ 2) ∧
      (∀ t ∈ (T : Subgroup K), t ≠ 1 →
        ∃ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), n * t * n⁻¹ ≠ t)

@[expose] def KFactBlockPlaneIb : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), IsComponentOf L ⊤ →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → IsParabolicTwo L J → J ≠ L →
    (∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) →
    ∀ p : ℕ, p.Prime → 5 ≤ p → IbPerfectSections p J →
    ∀ x ∈ L, x ^ p = 1 → x ∉ Subgroup.centralizer (L : Set Y) →
    (∃ V : Subgroup Y, ⁅V, V⁆ = V ∧ V ≤ Subgroup.normalizer (L : Set Y) ∧
      V ≤ Subgroup.normalizer (pCoreOf 2 J : Set Y) ∧ x ∈ V) →
    (∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) →
    ∀ E : Subgroup Y, E ≤ L ⊓ Subgroup.centralizer ({x} : Set Y) → IsElemAbelian p E →
      Nat.card E = p ^ 2 → x ∈ E →
    ∀ y ∈ Subgroup.normalizer (L : Set Y), y ∈ Subgroup.normalizer (E : Set Y) →
      (∃ k : ℕ, y ^ p ^ k = 1) → ∀ e ∈ E, y * e * y⁻¹ = e

@[expose] def CitedBlockThreeToralIbSq : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G) (p : ℕ), Open.IsKGroup ↥M →
    Asc81bHyp M S → IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    NineThreeThree M S L → p.Prime → 5 ≤ p →
    IbPerfectSections p (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) →
    ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) →
      IsElemAbelian p E → Nat.card E = p ^ 2 → False

theorem citedBlockThreeToralIb_of_sq (h : CitedBlockThreeToralIbSq) : CitedBlockThreeToralIb := by
  intro G _ _ M S L p hK hA hL hX hS h3 hp hp5 hJ E hEP hEel hEcard
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, hF⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) (n := 2) p
    (by rw [hEcard]; exact pow_dvd_pow p (by norm_num : 2 ≤ 3))
  refine h G M S L p hK hA hL hX hS h3 hp hp5 hJ (F.map E.subtype)
    ((Subgroup.map_subtype_le F).trans hEP) ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩ ?_
  · obtain ⟨_, ⟨a, -, rfl⟩⟩ := a
    obtain ⟨_, ⟨b, -, rfl⟩⟩ := b
    exact Subtype.ext (by simpa using congrArg Subtype.val (hEel.1.is_comm.comm a b))
  · rintro _ ⟨a, -, rfl⟩
    exact hEel.2 a a.2
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hF]

variable {G : Type} [Group G] [Finite G]

structure D1IbCubeConfig (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
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
    Subgroup (H ⧸ primeComplementCore (G := H) p)) = p ^ 3
  perf : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
    ¬ p ^ 2 ∣ Nat.card V
  uniq : ∀ L₁ L₂ : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L₁ →
    IsWeakSBlock M (pCoreOf 2 H) L₂ → barM M L₁ = barM M L₂
  cover : ∃ U : Subgroup G, U ≤ H ⊓ M ∧ ⁅U, U⁆ = U ∧ z ∈ U

structure D1IbCubeInputs : Prop where
  blocks : D1IbBlockInputs
  plane : KFactBlockPlaneIb
  three : CitedBlockThreeToralIbSq
  orbits : KFactSmallOrbitsCube

end CFSG.AGLEmbedding
