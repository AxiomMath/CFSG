module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexBaseTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexTower
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexPointIndex
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexNormalizer

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

universe u v

theorem translated_coset_index_of_full_model_and_conjugation
    {G : Type u} {F : Type v} [Group G] [Group F] [Finite G] [Finite F]
    {H : Subgroup G} {z u : G} (h : InvolutionPointLocalEmbedding H z)
    (beta : pointRightCosetSpace H) (hb : beta ≠ rightCosetMk H 1)
    (huD : u ∈ pairPointStabilizer H beta) (hzu : Commute z u)
    (L : Subgroup G) (hLC : L ≤ Subgroup.centralizer ({u} : Set G))
    (f : L →* F) (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker))
    (B : Subgroup F) (hB : IsBorelSubgroup B) (hmodel : IsSimpleBenderGroup F)
    (e : cosetFixedSet H u ≃ F ⧸ B)
    (hbase : e ⟨rightCosetMk H 1, (point_right_base_fixed_iff H u).mpr
      (pairPointStabilizer_le_point H beta huD)⟩ = QuotientGroup.mk 1)
    (he : letI := cosetFixedSetInverseRightAction H L u hLC
      ∀ a : L, ∀ omega : cosetFixedSet H u, e (a • omega) = f a • e omega)
    (hconj : ∀ s ∈ translatedCosetUnitSet H z u,
      ∀ t ∈ translatedCosetUnitSet H z u,
        ∃ n : Subgroup.normalizer (translatedCosetUnitSet H z u),
          rightConjugateElem s (n : G) = t) :
    (pairPointStabilizer H beta).relIndex
        (Subgroup.normalizer (translatedCosetUnitSet H z u)) =
      Nat.card (cosetUnitSet H z u) * (Nat.card (cosetFixedSet H u) - 1) := by
  have huH := pairPointStabilizer_le_point H beta huD
  have hNH := translated_coset_normalizer_le_point h huH hzu
  have hcentralizer := translated_normalizer_centralizer_eq_point_centralizer h huH hzu
  have hindex := point_centralizer_index_of_full_model_identification
    H L u huH hLC f hf hodd B hB hmodel e hbase he beta
      ((mem_point_right_stabilizer_iff H beta u).mp huD.2) hb
  rw [normalizer_index_tower _ _ u (translated_coset_normalizer_intersection h beta hb huD),
    translated_coset_conjugation_index H z u hconj, hcentralizer, hindex]

theorem translated_coset_full_index_and_sylow_consequences
    {G : Type u} {F : Type v} [Group G] [Group F] [Finite G] [Finite F]
    {H : Subgroup G} {z u : G} (h : InvolutionPointLocalEmbedding H z)
    (beta : pointRightCosetSpace H) (hb : beta ≠ rightCosetMk H 1)
    (huD : u ∈ pairPointStabilizer H beta) (hu : IsInvolution u) (hzu : Commute z u)
    (hfour : ¬ TwoRankAtLeastTwo (pairPointStabilizer H beta))
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (L : Subgroup G) (hLC : L ≤ Subgroup.centralizer ({u} : Set G))
    (f : L →* F) (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker))
    (B : Subgroup F) (hB : IsBorelSubgroup B) (hmodel : IsSimpleBenderGroup F)
    (e : cosetFixedSet H u ≃ F ⧸ B)
    (hbase : e ⟨rightCosetMk H 1, (point_right_base_fixed_iff H u).mpr
      (pairPointStabilizer_le_point H beta huD)⟩ = QuotientGroup.mk 1)
    (he : letI := cosetFixedSetInverseRightAction H L u hLC
      ∀ a : L, ∀ omega : cosetFixedSet H u, e (a • omega) = f a • e omega)
    (hconj : ∀ s ∈ translatedCosetUnitSet H z u,
      ∀ t ∈ translatedCosetUnitSet H z u,
        ∃ n : Subgroup.normalizer (translatedCosetUnitSet H z u),
          rightConjugateElem s (n : G) = t)
    (hq : ∃ a : ℕ, Nat.card (cosetUnitSet H z u) = 2 ^ a)
    (hk : ∃ i : ℕ, Nat.card (cosetFixedSet H u) = Nat.card (cosetUnitSet H z u) ^ i + 1) :
    let D := pairPointStabilizer H beta
    let N := Subgroup.normalizer (translatedCosetUnitSet H z u)
    let d := Nat.card (cosetUnitSet H z u) * (Nat.card (cosetFixedSet H u) - 1)
    translatedCosetUnitSet H z u ∩ (D : Set G) = {u} ∧
      N ≤ H ∧ N ⊓ D = (N ⊓ Subgroup.centralizer ({u} : Set G)) ⊓ D ∧
      (∃ Q : Sylow 2 D, (Q : Subgroup D).map D.subtype ≤ N ⊓ D) ∧
      D.relIndex N = d ∧
      (∀ S : Sylow 2 N, D.relIndex ((S : Subgroup N).map N.subtype) = d) ∧
      d ∣ Nat.card (pointRightCosetSpace H) - 1 ∧
      (Nat.card (pointRightCosetSpace H) - 1 = d →
        ∀ S : Sylow 2 N, ∃ R : Sylow 2 G,
          (R : Subgroup G) = (S : Subgroup N).map N.subtype) := by
  let D := pairPointStabilizer H beta
  let N := Subgroup.normalizer (translatedCosetUnitSet H z u)
  let d := Nat.card (cosetUnitSet H z u) * (Nat.card (cosetFixedSet H u) - 1)
  have hNH : N ≤ H := translated_coset_normalizer_le_point h
    (pairPointStabilizer_le_point H beta huD) hzu
  have hindex : D.relIndex N = d := translated_coset_index_of_full_model_and_conjugation
    h beta hb huD hzu L hLC f hf hodd B hB hmodel e hbase he hconj
  have hd : ∃ a : ℕ, D.relIndex N = 2 ^ a := by
    rw [hindex]
    exact q_times_degree_sub_one_twoPower _ _ hq hk
  obtain ⟨Q, hQ⟩ := translated_normalizer_contains_pair_sylow H D
    (pairPointStabilizer_le_point H beta) hfour z u hu huD
  refine ⟨translated_coset_inter_pair_eq_singleton h beta hb huD, hNH,
    translated_coset_normalizer_intersection h beta hb huD, ⟨Q, hQ⟩,
    hindex, ?_, ?_, ?_⟩
  · intro S
    exact (sylow_intersection_relIndex_eq N D hd S).trans hindex
  · change d ∣ Nat.card (pointRightCosetSpace H) - 1
    rw [← hindex]
    exact primePower_pair_index_dvd_original_degree H N hNH beta hb hdoubly Q
      (hQ.trans inf_le_left) hd
  · intro heq S
    exact every_normalizer_sylow_ambient_of_original_degree h N hNH beta hb hdoubly Q
      (hQ.trans inf_le_left) (hindex.trans heq.symm) S

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
