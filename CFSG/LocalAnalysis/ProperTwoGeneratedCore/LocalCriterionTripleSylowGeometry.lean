module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointOddCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

universe u

variable {G : Type u} [Group G]

theorem invariant_pair_subgroup_le_triple {H X : Subgroup G} {z : G}
    {beta : rightCosetSpace H} (hXB : X ≤ pairPointStabilizer H beta)
    (hzX : z ∈ Subgroup.normalizer (X : Set G)) :
    X ≤ triplePointStabilizer H z beta := by
  intro x hx
  refine ⟨hXB hx, (mem_rightCosetStabilizer_iff H _ x).mpr ?_⟩
  have hconj : z * x * z⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hzX x).mp hx
  have hfix : rightCosetTranslate H beta (z * x * z⁻¹) = beta :=
    (mem_rightCosetStabilizer_iff H beta _).mp (hXB hconj).2
  calc
    rightCosetTranslate H (rightCosetTranslate H beta z) x =
        rightCosetTranslate H beta (z * x) := rightCosetTranslate_mul H beta z x
    _ = rightCosetTranslate H
        (rightCosetTranslate H beta (z * x * z⁻¹)) z := by
      rw [rightCosetTranslate_mul]
      simp only [mul_assoc, inv_mul_cancel, mul_one]
    _ = rightCosetTranslate H beta z := by rw [hfix]

theorem triple_stabilizer_normalized_by_distinguished {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (beta : rightCosetSpace H) :
    z ∈ Subgroup.normalizer (triplePointStabilizer H z beta : Set G) := by
  have hzinv : z⁻¹ = z := inv_eq_self_of_orderOf_eq_two h.distinguished_order
  have hzz : z * z = 1 := by
    have hzpow := pow_orderOf_eq_one z
    rw [h.distinguished_order, pow_two] at hzpow
    exact hzpow
  have hbase : rightCosetTranslate H (rightCosetMk H 1) z = rightCosetMk H 1 :=
    (rightCosetTranslate_distinguished_fixed_iff h _).mpr rfl
  have hreturn : rightCosetTranslate H (rightCosetTranslate H beta z) z = beta := by
    rw [rightCosetTranslate_mul, hzz, rightCosetTranslate_one]
  have hconj (x : G) (hx : x ∈ triplePointStabilizer H z beta) :
      z * x * z⁻¹ ∈ triplePointStabilizer H z beta := by
    have ha : rightCosetTranslate H (rightCosetMk H 1) x = rightCosetMk H 1 :=
      (mem_rightCosetStabilizer_iff H _ x).mp hx.1.1
    have hb : rightCosetTranslate H beta x = beta :=
      (mem_rightCosetStabilizer_iff H _ x).mp hx.1.2
    have hg : rightCosetTranslate H (rightCosetTranslate H beta z) x =
        rightCosetTranslate H beta z := (mem_rightCosetStabilizer_iff H _ x).mp hx.2
    refine ⟨⟨(mem_rightCosetStabilizer_iff H _ _).mpr ?_,
      (mem_rightCosetStabilizer_iff H _ _).mpr ?_⟩,
      (mem_rightCosetStabilizer_iff H _ _).mpr ?_⟩
    · rw [hzinv, ← rightCosetTranslate_mul, ← rightCosetTranslate_mul, hbase, ha, hbase]
    · rw [hzinv, ← rightCosetTranslate_mul, ← rightCosetTranslate_mul, hg, hreturn]
    · rw [hzinv, ← rightCosetTranslate_mul, ← rightCosetTranslate_mul, hreturn, hb]
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  refine ⟨hconj x, fun hx => ?_⟩
  have hinvol : z * (z * x * z⁻¹) * z⁻¹ = x := by
    rw [hzinv]
    calc
      z * (z * x * z) * z = (z * z) * x * (z * z) := by group
      _ = x := by rw [hzz, one_mul, mul_one]
  simpa only [hinvol] using hconj _ hx

theorem triple_stabilizer_right_conjugate_eq {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (beta : rightCosetSpace H) :
    rightConjugate (triplePointStabilizer H z beta) z =
      triplePointStabilizer H z beta := by
  have hzN := (Subgroup.normalizer (triplePointStabilizer H z beta : Set G)).inv_mem
    (triple_stabilizer_normalized_by_distinguished h beta)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hzN

theorem triple_stabilizer_normal_in_generated {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (beta : rightCosetSpace H) :
    ((triplePointStabilizer H z beta).subgroupOf
      (triplePointStabilizer H z beta ⊔ Subgroup.zpowers z)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
  exact sup_le Subgroup.le_normalizer
    (Subgroup.zpowers_le.mpr (triple_stabilizer_normalized_by_distinguished h beta))

theorem triple_z_centralizer_eq_pair (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) :
    triplePointStabilizer H z beta ⊓ Subgroup.centralizer ({z} : Set G) =
      pairPointStabilizer H beta ⊓ Subgroup.centralizer ({z} : Set G) := by
  apply le_antisymm (inf_le_inf_right _ inf_le_left)
  exact le_inf (pair_z_centralizer_le_triple H z beta) inf_le_right

end CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
