module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypNF
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicOddCore
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicYCore
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma22Basic
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.LocalAnalysis.ComponentClassification.AS76bExistBasic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bHypII

public section

namespace CFSG.ComponentClassification.RankTwoClassical.NFQuot

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ABGLocalTools

variable {Q : Type} [Group Q] [Finite Q]

local notation "O" => standardComponentOddCore Q
local notation "π" => QuotientGroup.mk' (standardComponentOddCore Q)

omit [Finite Q] in
theorem rightConjugate_map_mk' (H : Subgroup Q) (q : Q) :
    rightConjugate (H.map π) (π q) = (rightConjugate H q).map π := by
  ext y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective O y
  rw [mem_rightConjugate_iff, mem_map, mem_map]
  constructor
  · rintro ⟨h, hh, he⟩
    refine ⟨q⁻¹ * h * q, (mem_rightConjugate_iff H q _).mpr (by simpa [mul_assoc] using hh), ?_⟩
    rw [map_mul, map_mul, map_inv, he]
    group
  · rintro ⟨h, hh, he⟩
    refine ⟨q * h * q⁻¹, (mem_rightConjugate_iff H q h).mp hh, ?_⟩
    rw [map_mul, map_mul, map_inv, he]

omit [Finite Q] in
theorem mem_of_mem_sup {M N : Subgroup Q} [N.Normal] (hodd : Odd (Nat.card N))
    (hNM : N ≤ centralizer (M : Set Q)) {x : Q} (hx : x ∈ M ⊔ N) {k : ℕ} (hk : x ^ 2 ^ k = 1) :
    x ∈ M := by
  obtain ⟨m, hm, n, hn, rfl⟩ := mem_sup_of_normal_right.mp hx
  have hc : Commute m n := (mem_centralizer_iff.mp (hNM hn)) m hm
  have h1 : n ^ 2 ^ k = (m ^ 2 ^ k)⁻¹ := by
    rw [hc.mul_pow] at hk
    exact eq_inv_of_mul_eq_one_right hk
  have hcop : Nat.Coprime (2 ^ k) (orderOf n) := by
    refine Nat.Coprime.pow_left k (Nat.prime_two.coprime_iff_not_dvd.mpr fun h2 => ?_)
    have : Odd (orderOf n) := by
      have h := Subgroup.orderOf_dvd_natCard N hn
      exact hodd.of_dvd_nat h
    exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h2)
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  have hnM : n ∈ M := by
    rw [← hj, h1]
    exact pow_mem (inv_mem (pow_mem hm _)) j
  exact mul_mem hm hnM

theorem oddCore_le_of_rankTwoHyp {M : Subgroup Q} (hH : RankTwoHypNF Q M) :
    O ≤ centralizer (M : Set Q) :=
  standardComponentOddCore_le_centralizer hH.standard hH.rank

section Standard

variable {M : Subgroup Q} (hH : RankTwoHypNF Q M)
include hH

theorem rankTwoHyp_map : RankTwoHypNF (Q ⧸ O) (M.map π) := by
  have hodd := odd_card_standardComponentOddCore (G := Q)
  have hNA := (oddCore_le_of_rankTwoHyp hH)
  refine ⟨?_, ?_, ?_⟩
  · exact standard_map hH.standard hodd hNA
  · intro hn
    apply hH.not_normal
    have h1 : (M ⊔ O).Normal := by
      have := hn.comap (QuotientGroup.mk' O)
      rwa [comap_map_eq, QuotientGroup.ker_mk'] at this
    rw [← normalizer_eq_top_iff, ← normalizer_sup_eq hodd hNA hH.standard.1.1]
    exact normalizer_eq_top_iff.mpr h1
  · exact two_le_pRank_map hodd hNA hH.standard.1.1 hH.rank

noncomputable def quotCenterMap : rankTwoQuot M ≃* rankTwoQuot (M.map π) :=
  quotCenterEquivMap (oddCore_le_of_rankTwoHyp hH) hH.standard.1.1

theorem odd_card_center_map (hZ : Odd (Nat.card (center ↥M))) :
    Odd (Nat.card (center ↥(M.map π))) := by
  set f := (QuotientGroup.mk' O).subgroupMap M
  have hle : center ↥(M.map π) ≤ (center ↥M).map f := by
    intro z hz
    obtain ⟨m, rfl⟩ := (QuotientGroup.mk' O).subgroupMap_surjective M z
    refine ⟨m, ?_, rfl⟩
    change m ∈ center ↥M
    rw [← ker_quotCenter_map (oddCore_le_of_rankTwoHyp hH) hH.standard.1.1, MonoidHom.mem_ker,
      MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hz
  exact hZ.of_dvd_nat ((card_dvd_of_le hle).trans (card_map_dvd _ _))

theorem isSylowOf_map {R : Subgroup Q} (hR : IsSylowOf 2 R (centralizer (M : Set Q))) :
    IsSylowOf 2 (R.map π) (centralizer ((M.map π : Subgroup (Q ⧸ O)) : Set (Q ⧸ O))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [centralizer_map_eq odd_card_standardComponentOddCore (oddCore_le_of_rankTwoHyp hH)
    hH.standard.1.1]
  exact RankTwoSporadic.IsSylowOf.map hR π

theorem not_conj_le_map {R : Subgroup Q} (hR : IsPGroup 2 R)
    (hno : ∀ x : Q, ¬ rightConjugate R x ≤ M) (h : Q ⧸ O) :
    ¬ rightConjugate (R.map π) h ≤ M.map π := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective O h
  rw [rightConjugate_map_mk']
  intro hle
  apply hno q
  intro x hx
  have hxMO : x ∈ M ⊔ O := by
    have : x ∈ (M.map π).comap π := hle ⟨x, hx, rfl⟩
    rwa [comap_map_eq, QuotientGroup.ker_mk'] at this
  have hRq : IsPGroup 2 (rightConjugate R q) := hR.map _
  obtain ⟨k, hk⟩ := hRq ⟨x, hx⟩
  exact mem_of_mem_sup odd_card_standardComponentOddCore (oddCore_le_of_rankTwoHyp hH) hxMO
    (by simpa using congrArg Subtype.val hk)

end Standard

end CFSG.ComponentClassification.RankTwoClassical.NFQuot
