module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSylowLift
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Real

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.UnbalancedLayer

theorem exists_coset_involution :
    ∀ (G : Type) [Group G] [Finite G] (J S : Subgroup G), ⁅J, J⁆ = J →
      IsL34Type (J ⧸ Open.fusionZStar J) → S ≤ normalizer (J : Set G) → IsPGroup 2 S →
      IsSylowTwoIn (S ⊓ J) J →
      ∀ s ∈ S, ∃ y ∈ S, s⁻¹ * y ∈ withKernel J ∧ y * y ∈ coreActionKernel J := by
  intro G _ _ J T hJ hL hTN hT2 hTJ s hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (T.subgroupOf (normalizer (J : Set G))) :=
    hT2.of_equiv (subgroupOfEquivOfLe hTN).symm
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have hW : IsSylowTwoIn ((P : Subgroup ↥(normalizer (J : Set G))).map
      (normalizer (J : Set G)).subtype) (normalizer (J : Set G)) :=
    ⟨map_subtype_le _, P,
      (comap_map_eq_self_of_injective (normalizer (J : Set G)).subtype_injective _).symm⟩
  set W := (P : Subgroup ↥(normalizer (J : Set G))).map (normalizer (J : Set G)).subtype
  have hTW : T ≤ W := fun x hx => ⟨⟨x, hTN hx⟩, hP (mem_subgroupOf.mpr hx), rfl⟩
  have hWJ : W ⊓ J ≤ T := by
    obtain ⟨-, Q, hQ⟩ := hTJ
    have hWJ2 : IsPGroup 2 ((W ⊓ J).subgroupOf J) :=
      ((GrS4.isPGroup_of_isSylowTwoIn hW).to_le inf_le_left).of_equiv
        (subgroupOfEquivOfLe inf_le_right).symm
    have hle : (Q : Subgroup ↥J) ≤ (W ⊓ J).subgroupOf J := by
      rw [hQ]
      intro x hx
      exact mem_subgroupOf.mpr ⟨hTW (mem_subgroupOf.mp hx).1, (mem_subgroupOf.mp hx).2⟩
    have heq := Q.is_maximal' hWJ2 hle
    intro x hx
    have hx' : (⟨x, hx.2⟩ : ↥J) ∈ (Q : Subgroup ↥J) := by
      rw [← heq]
      exact mem_subgroupOf.mpr hx
    rw [hQ] at hx'
    exact (mem_subgroupOf.mp hx').1
  obtain ⟨q, l, hQs, hT0, hreal⟩ := exists_frame_Sigma0 hJ hL hW
  obtain ⟨ρ, ⟨t, ht, ν, hν, rfl⟩, hβ⟩ := hreal s (hTW hs)
  obtain ⟨e, he⟩ := hQs.qsurj t (T0_le_S ht)
  obtain ⟨p, hpWJ, hpJ, hpe⟩ := (hT0 e).1 (by rw [he]; exact ht)
  have hpT : p ∈ T := hWJ hpWJ
  have hsN : s ∈ normalizer (J : Set G) := hTN hs
  have hpN : p ∈ normalizer (J : Set G) := hTN hpT
  have hyN : s * p ∈ normalizer (J : Set G) := mul_mem hsN hpN
  have hβs : ∀ e', q (betaHat J hsN e') = t * ν * q e' * (t * ν)⁻¹ := hβ
  have hy : ∀ e', q (betaHat J hyN e') = ν * q e' * ν⁻¹ := by
    intro e'
    rw [betaHat_mul J hsN hpN, betaHat_of_mem hpJ hpN, map_mul, map_mul, map_inv, hpe, he, hβs]
    group
  refine ⟨s * p, mul_mem hs hpT, ?_, ?_⟩
  · rw [inv_mul_cancel_left]
    exact mem_sup_left hpJ
  · refine GrS4.mem_coreActionKernel_of_realization_eq_one hJ (mul_mem hyN hyN) hQs.ker
      fun e' => ?_
    rw [betaHat_mul J hyN hyN, hy, hy]
    calc ν * (ν * q e' * ν⁻¹) * ν⁻¹ = ν * ν * q e' * (ν * ν)⁻¹ := by group
      _ = q e' := by rw [hν.mul_self]; group

end CFSG.ComponentClassification.GrSLit.L34Facts
