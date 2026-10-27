module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassVF3Wedge
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Levi

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction CFSG.SeitzReduction.E7Pilot

variable {K : Type} [Field K]

private theorem parabolicLevi_vNodes_le_sup :
    parabolicLevi .E7 K vNodes ≤
      rootSpan .E7 K (parabolicRoots .E7 vNodes) ⊔ torusGroup .E7 K := by
  refine sup_le le_sup_right ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · rw [SetLike.mem_coe, ← pinnedX_single]
    refine mem_sup_left (pinnedX_mem_rootSpan (S := parabolicRoots .E7 vNodes)
      ⟨isRoot_single .E7 j, fun i hi => ?_⟩ c)
    exact Pi.single_eq_of_ne (by rintro rfl; exact hi hj) _
  · rw [SetLike.mem_coe, ← pinnedX_neg_single]
    refine mem_sup_left (pinnedX_mem_rootSpan (S := parabolicRoots .E7 vNodes)
      ⟨isRoot_neg_single .E7 j, fun i hi => ?_⟩ c)
    rw [Pi.neg_apply, Pi.single_eq_of_ne (by rintro rfl; exact hi hj), neg_zero]

section Certs


theorem mem_parabolicRadical_of_commute_range_spToAdjointE7 [Finite K] [CharP K 2]
    {y : adjointGroup .E7 K}
    (hyv : y ∈ centralizer ({e7ASRep K 4} : Set (adjointGroup .E7 K))) (hy2 : y * y = 1)
    (hyL : ∀ l ∈ (spToAdjointE7 K).range, y * l = l * y) :
    (y : ModGL .E7 K) ∈ parabolicRadical .E7 K vNodes := by
  have hgv : (y : ModGL .E7 K) * vAS K = vAS K * y := by
    have h := congrArg Subtype.val (mem_centralizer_singleton_iff.1 hyv)
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, coe_e7ASRep_four] at h
  obtain ⟨-, -, -, -, hQM, -, huniq, -⟩ := parabolic_root_radical_Levi_factors .E7 K vNodes
  have hMN : parabolicLevi .E7 K vNodes ≤
      normalizer (parabolicRadical .E7 K vNodes : Set (ModGL .E7 K)) :=
    (parabolicLevi_le_parabolicSubgroup vNodes).trans
      (parabolicSubgroup_le_normalizer_parabolicRadical vNodes)
  obtain ⟨⟨q, m⟩, ⟨hq, hm, he⟩, hu⟩ := huniq _ (mem_parabolicSubgroup_of_commute_vAS y.2 hgv)
  simp only at hq hm he
  have hmL : ∀ l ∈ (spToAdjointE7 K).range,
      m * (l : ModGL .E7 K) = (l : ModGL .E7 K) * m := by
    intro l hl
    have hlM : (l : ModGL .E7 K) ∈ parabolicLevi .E7 K vNodes :=
      mem_subgroupOf.1 (range_spToAdjointE7_le_parabolicLevi hl)
    have hly : (y : ModGL .E7 K) = (l : ModGL .E7 K) * q * (l : ModGL .E7 K)⁻¹ *
        ((l : ModGL .E7 K) * m * (l : ModGL .E7 K)⁻¹) := by
      have h := congrArg Subtype.val (hyL l hl)
      simp only [Subgroup.coe_mul] at h
      calc (y : ModGL .E7 K) = (l : ModGL .E7 K) * y * (l : ModGL .E7 K)⁻¹ := by
            rw [← h, mul_inv_cancel_right]
        _ = (l : ModGL .E7 K) * (q * m) * (l : ModGL .E7 K)⁻¹ := by rw [he]
        _ = _ := by group
    have h1 := hu ((l : ModGL .E7 K) * q * (l : ModGL .E7 K)⁻¹,
      (l : ModGL .E7 K) * m * (l : ModGL .E7 K)⁻¹)
      ⟨(mem_normalizer_iff.1 (hMN hlM) q).1 hq, mul_mem (mul_mem hlM hm) (inv_mem hlM), hly⟩
    have h2 : (l : ModGL .E7 K) * m * (l : ModGL .E7 K)⁻¹ = m := congrArg Prod.snd h1
    calc m * (l : ModGL .E7 K) = (l : ModGL .E7 K) * m * (l : ModGL .E7 K)⁻¹ * l := by
          rw [h2]
      _ = (l : ModGL .E7 K) * m := by group
  have hmv : m * vAS K = vAS K * m := by
    rw [he] at hgv
    exact (commute_of_mul_commute_vAS hq hm hgv).1
  have hm2 : m * m = 1 := by
    have hyy : (y : ModGL .E7 K) * y = 1 := by
      have h := congrArg Subtype.val hy2
      simpa using h
    rw [he] at hyy
    have h4 : q * (m * q * m⁻¹) * (m * m) = 1 := by
      rw [← hyy]
      group
    have h5 : m * m ∈ parabolicRadical .E7 K vNodes ⊓ parabolicLevi .E7 K vNodes := by
      refine mem_inf.2 ⟨?_, mul_mem hm hm⟩
      rw [eq_inv_of_mul_eq_one_right h4]
      exact inv_mem (mul_mem hq ((mem_normalizer_iff.1 (hMN hm) q).1 hq))
    rwa [hQM, mem_bot] at h5
  have hHA : torusGroup .E7 K ≤
      normalizer (rootSpan .E7 K (parabolicRoots .E7 vNodes) : Set (ModGL .E7 K)) :=
    torusGroup_le_normalizer_rootSpan fun _ hα => hα.1
  have hmHA : m ∈ ((torusGroup .E7 K ⊔ rootSpan .E7 K (parabolicRoots .E7 vNodes) :
      Subgroup (ModGL .E7 K)) : Set (ModGL .E7 K)) := by
    rw [SetLike.mem_coe, sup_comm]
    exact parabolicLevi_vNodes_le_sup hm
  rw [coe_mul_of_left_le_normalizer_right _ _ hHA] at hmHA
  obtain ⟨t, ht, a, ha, hm_eq⟩ := hmHA
  replace hm_eq : t * a = m := hm_eq
  subst hm_eq
  have hta : t * a * t⁻¹ ∈ rootSpan .E7 K (parabolicRoots .E7 vNodes) :=
    (mem_normalizer_iff.1 (hHA ht) a).1 ha
  have ht2 : t ^ 2 ∈ rootSpan .E7 K (parabolicRoots .E7 vNodes) := by
    have e : t * t = (t * a * t⁻¹)⁻¹ * (t * a * (t * a)) * a⁻¹ := by group
    rw [sq, e, hm2, mul_one]
    exact mul_mem (inv_mem hta) (inv_mem ha)
  have htA : t ∈ rootSpan .E7 K (parabolicRoots .E7 vNodes) := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    have hcard : Nat.card Kˣ + 1 = 2 ^ (n : ℕ) := by
      rw [Nat.card_units K, Nat.card_eq_fintype_card, hn]
      exact Nat.sub_add_cancel Nat.one_le_two_pow
    obtain ⟨k, hk⟩ : ∃ k, (n : ℕ) = k + 1 := ⟨(n : ℕ) - 1, by have := n.pos; omega⟩
    have e : t = (t ^ 2) ^ 2 ^ k := by
      rw [← pow_mul, ← pow_succ', ← hk, ← hcard, pow_succ,
        pow_card_units_eq_one_of_mem_torusGroup_e7 ht, one_mul]
    rw [e]
    exact pow_mem ht2 _
  obtain ⟨l₀, ⟨b₀, rfl⟩, hl₀⟩ := rootSpan_inf_centralizer_le_range_spToAdjointE7
    (mem_inf.2 ⟨mul_mem htA ha, mem_centralizer_singleton_iff.2 hmv⟩)
  have hb₀ : b₀ ∈ center _ := by
    rw [mem_center_iff]
    intro b
    apply spToAdjointE7_injective (K := K)
    apply Subtype.ext
    have h1 := hmL (spToAdjointE7 K b) ⟨b, rfl⟩
    rw [← hl₀] at h1
    simp only [map_mul, Subgroup.coe_mul, Subgroup.coe_subtype] at h1 ⊢
    exact h1.symm
  rw [CFSG.Timmesfeld.LieEmbed.center_statedSp_eq_bot (K := K), mem_bot] at hb₀
  rw [he, ← hl₀, hb₀, map_one, map_one, mul_one]
  exact hq

end Certs

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
