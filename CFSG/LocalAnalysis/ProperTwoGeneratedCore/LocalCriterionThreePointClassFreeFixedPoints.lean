module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFreeSelection
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeClass

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G]

@[expose] def distinguishedTripleCentralization (H : Subgroup G) (z : G) : Prop :=
  ∀ r ∈ involutionPointClass z, ∀ epsilon delta : rightCosetSpace H,
    pointRightCosetMul H epsilon r = epsilon → delta ≠ epsilon →
      (rightCosetStabilizer H epsilon ⊓ rightCosetStabilizer H delta) ⊓
          rightCosetStabilizer H (pointRightCosetMul H delta r) =
        (rightCosetStabilizer H epsilon ⊓ rightCosetStabilizer H delta) ⊓
          Subgroup.centralizer ({r} : Set G)

theorem noncentral_pair_subgroup_class_flip_has_no_fixed_point
    {H : Subgroup G} {z : G} (htriple : distinguishedTripleCentralization H z)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta)
    (M : Subgroup G) (hMD : M ≤ pairPointStabilizer H beta)
    (hnoncentral : ⁅M, Subgroup.zpowers t⁆ ≠ ⊥) :
    ∀ gamma ∈ pointFixedSet H M, pointRightCosetMul H gamma t ≠ gamma := by
  intro gamma hgamma hfixed
  let alpha := rightCosetMk H 1
  have hflip : pointRightCosetMul H alpha t = beta := by
    rw [pointRightCosetMul_eq_translate]
    exact ht.2
  have halpha : alpha ≠ gamma := by
    intro heq
    apply hbeta
    rw [← hflip, heq, hfixed]
    exact heq.symm
  have hid := htriple t ht.1 gamma alpha hfixed halpha
  have hMgamma := (mem_pointFixedSet_iff H M gamma).mp hgamma
  have hMtriple : M ≤ (rightCosetStabilizer H gamma ⊓ rightCosetStabilizer H alpha) ⊓
      rightCosetStabilizer H (pointRightCosetMul H alpha t) := by
    rw [hflip]
    exact le_inf (le_inf hMgamma (hMD.trans inf_le_left)) (hMD.trans inf_le_right)
  rw [hid] at hMtriple
  exact hnoncentral ((commutator_zpowers_eq_bot_iff M t).mpr (hMtriple.trans inf_le_right))

theorem normalized_three_point_subgroup_centralizes_class_fixed_point [Finite G]
    {H : Subgroup G} {z : G} (htriple : distinguishedTripleCentralization H z)
    (W : Subgroup G) (hthree : 3 ≤ Nat.card (pointFixedSet H W))
    (s : G) (hs : s ∈ involutionPointClass z)
    (hsW : s ∈ Subgroup.normalizer (W : Set G))
    (epsilon : rightCosetSpace H) (hepsilon : epsilon ∈ pointFixedSet H W)
    (hfixed : pointRightCosetMul H epsilon s = epsilon) :
    W ≤ Subgroup.centralizer ({s} : Set G) := by
  have hcard : 1 < (pointFixedSet H W).ncard := by
    change 1 < Nat.card (pointFixedSet H W)
    omega
  obtain ⟨delta, hdelta, hne⟩ := Set.exists_ne_of_one_lt_ncard hcard epsilon
  have hdeltaS := normalizer_preserves_pointFixedSet hsW hdelta
  have hWtriple : W ≤ (rightCosetStabilizer H epsilon ⊓ rightCosetStabilizer H delta) ⊓
      rightCosetStabilizer H (pointRightCosetMul H delta s) :=
    le_inf (le_inf ((mem_pointFixedSet_iff H W epsilon).mp hepsilon)
      ((mem_pointFixedSet_iff H W delta).mp hdelta))
      ((mem_pointFixedSet_iff H W _).mp hdeltaS)
  rw [htriple s hs epsilon delta hfixed hne] at hWtriple
  exact hWtriple.trans inf_le_right

theorem noncentral_pair_odd_normalizer_entire_class_fixed_points [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (htriple : distinguishedTripleCentralization H z)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta)
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (M : Subgroup G) (hM : IsPGroup p M)
    (hMD : M ≤ pairPointStabilizer H beta)
    (htM : t ∈ Subgroup.normalizer (M : Set G))
    (hnoncentral : ⁅M, Subgroup.zpowers t⁆ ≠ ⊥) :
    involutionPointClass z ∩ (Subgroup.normalizer (M : Set G) : Set G) =
        conjugacyWithin (Subgroup.normalizer (M : Set G)) t ∧
      ∀ s ∈ involutionPointClass z ∩ (Subgroup.normalizer (M : Set G) : Set G),
        ∀ gamma ∈ pointFixedSet H M, pointRightCosetMul H gamma s ≠ gamma := by
  have hno := noncentral_pair_subgroup_class_flip_has_no_fixed_point
    htriple beta hbeta t ht M hMD hnoncentral
  obtain ⟨hclass, _, hpropagate⟩ := no_fixed_point_odd_normalizer_full_class
    h p hp hpodd hM ht.1 htM hno
  refine ⟨hclass, ?_⟩
  intro s hs
  exact (hpropagate s (hclass ▸ hs)).1

end CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
