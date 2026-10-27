module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFreeObstruction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFreeMaximality
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFreeConclusions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalOddFixed

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree

open CFSG.ShultStronglyClosedTI
open CFSG.Open
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalOddFixed

variable {G : Type*} [Group G] [Finite G]

theorem maximal_three_point_normalizer_original_right_double_transitivity
    (H : Subgroup G)
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (p : ℕ) (hp : p.Prime) (W : Subgroup G) (hW : IsPGroup p W)
    (hthree : 3 ≤ Nat.card (pointFixedSet H W))
    (hmax : ∀ V : Subgroup G, IsPGroup p V → W ≤ V →
      3 ≤ Nat.card (pointFixedSet H V) → V ≤ W) :
    ∀ a ∈ pointFixedSet H W, ∀ b ∈ pointFixedSet H W,
      ∀ c ∈ pointFixedSet H W, ∀ d ∈ pointFixedSet H W,
        a ≠ b → c ≠ d → ∃ n ∈ Subgroup.normalizer (W : Set G),
          pointRightCosetMul H a n = c ∧ pointRightCosetMul H b n = d := by
  exact normalizer_inverse_action_two_pretransitive_original_right H W
    (maximal_three_point_normalizer_two_pretransitive H hdoubly p hp W hW hthree hmax)

theorem maximal_noncentral_pair_prime_overgroup_entire_normalizer_class_empty
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (htriple : distinguishedTripleCentralization H z)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta)
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (M : Subgroup G) (hM : IsPGroup p M)
    (hMD : M ≤ pairPointStabilizer H beta)
    (htM : t ∈ Subgroup.normalizer (M : Set G))
    (hnoncentral : ⁅M, Subgroup.zpowers t⁆ ≠ ⊥)
    (W : Subgroup G) (hMW : M ≤ W) (hW : IsPGroup p W)
    (hthree : 3 ≤ Nat.card (pointFixedSet H W))
    (hmax : ∀ V : Subgroup G, IsPGroup p V → W ≤ V →
      3 ≤ Nat.card (pointFixedSet H V) → V ≤ W) :
    (Subgroup.normalizer (W : Set G) : Set G) ∩ involutionPointClass z = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro s hs
  obtain ⟨⟨epsilon, hepsilon, hfixed, _⟩, _, _⟩ :=
    local_involution_point_maximal_odd_prime_fixed_set_normalizing_involution
      h hdoubly p hp hpodd hW hthree hmax hs.2 hs.1
  exact noncentral_pair_prime_overgroup_normalizing_class_has_no_fixed_point
    h htriple beta hbeta t ht p hp hpodd M hM hMD htM hnoncentral
    W hMW hthree s hs.2 hs.1 epsilon hepsilon hfixed

end CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree

namespace CFSG.ProperTwoGeneratedCore

open CFSG.ShultStronglyClosedTI
open CFSG.Open
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree

variable {G : Type*} [Group G] [Finite G]

theorem local_involution_point_three_point_noncentral_subgroup_class_free_maximal_prime_normalizer
    (H : Subgroup G) (z : G) (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (htriple : distinguishedTripleCentralization H z)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (htclass : t ∈ involutionPointClass z)
    (hswap : rightCosetTranslate H (rightCosetMk H 1) t = beta ∧
      rightCosetTranslate H beta t = rightCosetMk H 1)
    (X : Subgroup G) (hXD : X ≤ pairPointStabilizer H beta)
    (hXnorm : t ∈ Subgroup.normalizer (X : Set G))
    (hnoncentral : ⁅X, Subgroup.zpowers t⁆ ≠ ⊥)
    (hthree : 3 ≤ Nat.card (pointFixedSet H X)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ P : Sylow p X,
      t ∈ Subgroup.normalizer (((P : Subgroup X).map X.subtype : Subgroup G) : Set G) ∧
      ⁅(P : Subgroup X).map X.subtype, Subgroup.zpowers t⁆ ≠ ⊥ ∧
      pointFixedSet H X ⊆ pointFixedSet H ((P : Subgroup X).map X.subtype) ∧
      3 ≤ Nat.card (pointFixedSet H ((P : Subgroup X).map X.subtype)) ∧
      (∃ W : Subgroup G, (P : Subgroup X).map X.subtype ≤ W ∧ IsPGroup p W ∧
        3 ≤ Nat.card (pointFixedSet H W) ∧
        ∀ V : Subgroup G, IsPGroup p V → W ≤ V →
          3 ≤ Nat.card (pointFixedSet H V) → V ≤ W) ∧
      (∀ W : Subgroup G, (P : Subgroup X).map X.subtype ≤ W → IsPGroup p W →
        3 ≤ Nat.card (pointFixedSet H W) →
        (∀ V : Subgroup G, IsPGroup p V → W ≤ V →
          3 ≤ Nat.card (pointFixedSet H V) → V ≤ W) →
        (∀ a ∈ pointFixedSet H W, ∀ b ∈ pointFixedSet H W,
          ∀ c ∈ pointFixedSet H W, ∀ d ∈ pointFixedSet H W,
            a ≠ b → c ≠ d → ∃ n ∈ Subgroup.normalizer (W : Set G),
              pointRightCosetMul H a n = c ∧ pointRightCosetMul H b n = d) ∧
        (Subgroup.normalizer (W : Set G) : Set G) ∩ involutionPointClass z = ∅ ∧
        ((∀ A : Subgroup G, IsElemAbelian 2 A → Nat.card A = 4 →
          ∃ s ∈ A, s ∈ involutionPointClass z) →
          ∀ A : Subgroup G, A ≤ Subgroup.normalizer (W : Set G) →
            IsElemAbelian 2 A → Nat.card A ≠ 4)) := by
  have ht : t ∈ rightPairFlipFiber H z beta := ⟨htclass, hswap.1⟩
  obtain ⟨p, hp, hpodd, P, htP, hPnoncentral, hfixed, hPthree⟩ :=
    original_three_point_noncentral_sylow_selection h S hzS hzcenter
      beta hbeta t ht X hXD hXnorm hnoncentral hthree
  let M := (P : Subgroup X).map X.subtype
  have hM : IsPGroup p M := P.isPGroup'.map X.subtype
  have hMD : M ≤ pairPointStabilizer H beta := (Subgroup.map_subtype_le (P : Subgroup X)).trans hXD
  refine ⟨p, hp, hpodd, P, htP, hPnoncentral, hfixed, hPthree,
    exists_global_maximal_three_point_prime_overgroup H p M hM hPthree, ?_⟩
  intro W hMW hW hWthree hWmax
  have hempty := maximal_noncentral_pair_prime_overgroup_entire_normalizer_class_empty
    h hdoubly htriple beta hbeta t ht p hp hpodd M hM hMD htP hPnoncentral
    W hMW hW hWthree hWmax
  exact ⟨maximal_three_point_normalizer_original_right_double_transitivity
    H hdoubly p hp W hW hWthree hWmax, hempty,
    entire_class_empty_excludes_covered_four_groups z _ hempty⟩

end CFSG.ProperTwoGeneratedCore
