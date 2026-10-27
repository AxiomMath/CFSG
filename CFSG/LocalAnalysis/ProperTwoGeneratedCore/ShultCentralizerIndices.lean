module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairStatements
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorField
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ShultCentralizerIndicesDenominator
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ShultCentralizerIndicesHull

public section

namespace CFSG.ProperTwoGeneratedCore.RankOnePair

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair
open CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair

universe u

variable {G : Type u} [Group G]

@[expose] def LinearHullIdentification (L : Subgroup G) (k : Type) [Field k] (f : ℕ) : Prop :=
  2 ≤ f ∧ Nat.card k = 2 ^ f ∧ Nonempty (L ≃* GLAProj (GLASLGroup (Fin 2) k))

@[expose] def SuzukiHullIdentification (L : Subgroup G) (k : Type) [Field k] (a : ℕ) : Prop :=
  1 ≤ a ∧ Nat.card k = 2 ^ (2 * a + 1) ∧ Nonempty (L ≃* GLASzGroup a k)

variable [Finite G]

@[expose] def PairCommutatorGenerationTheorem (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (H : Subgroup G) (z : G), MinimalInvolutionPointLocalFailure H z →
    ∀ beta : rightCosetSpace H, beta ≠ rightCosetMk H 1 →
      ∀ t ∈ rightPairFlipFiber H z beta, pairGeneratedHull H z beta t = ⊤

theorem PairCommutatorGenerationTheorem.pairGenerationTheorem
    (hgen : PairCommutatorGenerationTheorem G) : HighRankPair.PairGenerationTheorem G := by
  intro H z h beta hbeta t ht
  apply top_unique
  rw [← hgen H z h beta hbeta t ht, ← minimalLocalFailureProperPairHull_eq_native]
  exact sylowAssemblyProper_pair_hull_le_generated h hbeta ht

theorem shult_centralizer_indices_of_distinguished_three_point
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (hgen : PairCommutatorGenerationTheorem G)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hpairRank : twoRank (pairPointStabilizer H beta) = 1)
    {u : G} (huD : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2)
    (hut : Commute u t) (huz : Commute u z)
    (hodd : CFSG.oddCore (localInvolutionPointHull z u) = ⊥)
    {k : Type} [Field k]
    (hmodel : (∃ f, LinearHullIdentification (localInvolutionPointHull z u) k f) ∨
      ∃ a, SuzukiHullIdentification (localInvolutionPointHull z u) k a) :
    let D := pairPointStabilizer H beta
    let M := Subgroup.centralizer ({u} : Set G)
    let C := D ⊓ Subgroup.centralizer (Subgroup.closure ({u, t} : Set G) : Set G)
    let q := Nat.card ↥(({1} : Set G) ∪ (involutionPointClass z ∩ (M : Set G) ∩ (H : Set G)))
    Nat.card k = q ∧ C.relIndex (D ⊓ M) = q - 1 ∧
      (DistinguishedThreePointCentralization H D t →
        (∀ f, LinearHullIdentification (localInvolutionPointHull z u) k f →
          C.relIndex (D ⊓ Subgroup.centralizer ({u * t} : Set G)) = q + 1) ∧
        ∀ a, SuzukiHullIdentification (localInvolutionPointHull z u) k a →
          C.relIndex (D ⊓ Subgroup.centralizer ({u * t} : Set G)) = q - 2 ^ (a + 1) + 1 ∨
            C.relIndex (D ⊓ Subgroup.centralizer ({u * t} : Set G)) =
              q + 2 ^ (a + 1) + 1) := by
  intro D M C q
  classical
  have htclass : t ∈ involutionPointClass z := ht.1
  have hflip : pointRightCosetMul H (rightCosetMk H 1) t = beta := by
    rw [pointRightCosetMul_eq_translate]
    exact ht.2
  have hunoncentral : u ∉ Subgroup.center G := by
    obtain ⟨hsimple, x, y, hxy⟩ := minimalLocalFailure_nonabelian_simple h
    intro hucenter
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hbot | htop
    · exact (orderOf_eq_prime_iff.mp hu).2 (Subgroup.mem_bot.mp (hbot ▸ hucenter))
    · exact hxy (Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top y) x)
  have hlinear : ∀ f, LinearHullIdentification (localInvolutionPointHull z u) k f →
      Nat.card k = q ∧ C.relIndex (D ⊓ M) = q - 1 := by
    rintro f ⟨hf, hcard, ⟨e⟩⟩
    have : Finite k := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    obtain ⟨-, -, -, -, -, -, -, hindex, hparam⟩ :=
      original_linear_first_index_and_parameter h.local_datum beta hbeta u t hu huz hut
        htclass hflip f hf hcard e
    have hq : q = 2 ^ f := hparam.symm
    exact ⟨hcard.trans hparam, by rw [hq]; exact hindex⟩
  have hsuzuki : ∀ a, SuzukiHullIdentification (localInvolutionPointHull z u) k a →
      Nat.card k = q ∧ C.relIndex (D ⊓ M) = q - 1 := by
    rintro a ⟨ha, hcard, ⟨e⟩⟩
    have : Finite k := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    obtain ⟨-, -, -, -, -, -, -, hindex, hparam⟩ :=
      original_suzuki_first_index_and_parameter h.local_datum beta hbeta u t hu huz hut
        htclass hflip a ha hcard e
    have hq : q = 2 ^ (2 * a + 1) := hparam.symm
    exact ⟨hcard.trans hparam, by rw [hq]; exact hindex⟩
  have hnum : Nat.card k = q ∧ C.relIndex (D ⊓ M) = q - 1 := by
    rcases hmodel with ⟨f, hf⟩ | ⟨a, ha⟩
    · exact hlinear f hf
    · exact hsuzuki a ha
  refine ⟨hnum.1, hnum.2, fun hthree => ⟨?_, ?_⟩⟩
  · rintro f ⟨hf, hcard, ⟨e⟩⟩
    have : Finite k := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    obtain ⟨-, -, rho, b, B, -, -, hpair⟩ := linear_field_model_pair_full f hf hcard
    obtain ⟨hnormal, htL, hclass, -, ⟨e₁⟩, hfix⟩ := product_hull_model_of_full_model_pair h
      hcomm hsmallerR1 beta hbeta ht hpairRank huD hu hut huz hodd rho b B _ hpair e
    have hdegree : Nat.card (elementFixedSet H (u * t)) = Nat.card k + 1 := by
      rw [hfix, Projectivization.card_of_finrank_two _ _ (by simp),
        GaloisField.card 2 f (by omega), hcard]
    rw [← hnum.1]
    exact linear_second_index_of_fixedSet_card h.local_datum beta hbeta htclass hflip hu hut
      huD huz hunoncentral hthree (hgen H z h beta hbeta t ht) _
      (localInvolutionPointHull_le_centralizer z (u * t)) hnormal htL hclass f hf hcard e₁
      hdegree
  · rintro a ⟨ha, hcard, ⟨e⟩⟩
    have : Finite k := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    obtain ⟨-, rho, b, B, -, -, hpair⟩ := suzuki_field_model_pair_full a ha hcard
    obtain ⟨hnormal, htL, hclass, -, ⟨e₁⟩, hfix⟩ := product_hull_model_of_full_model_pair h
      hcomm hsmallerR1 beta hbeta ht hpairRank huD hu hut huz hodd rho b B _ hpair e
    have hdegree : Nat.card (elementFixedSet H (u * t)) = Nat.card k ^ 2 + 1 := by
      rw [hfix, hcard]
      exact suzuki_ovoid_card a
    rw [← hnum.1]
    exact suzuki_second_index_of_fixedSet_card h.local_datum beta hbeta htclass hflip hu hut
      huD huz hunoncentral hthree (hgen H z h beta hbeta t ht) _
      (localInvolutionPointHull_le_centralizer z (u * t)) hnormal htL hclass a ha hcard e₁
      hdegree

end CFSG.ProperTwoGeneratedCore.RankOnePair
