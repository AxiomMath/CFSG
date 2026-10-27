module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairClassSize
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoParts
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOnePairHullRank
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairPremises

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.RankOnePair
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

theorem one_le_pRank_two_of_mem [Finite G] {X : Subgroup G} {x : G} (hx : x ∈ X)
    (hord : orderOf x = 2) : 1 ≤ CFSG.Open.pRank 2 X := by
  have hx2 : x ^ 2 = 1 := (orderOf_eq_prime_iff.mp hord).1
  have helem : IsElemAbelian 2 (Subgroup.zpowers x) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
      exact (Commute.zpow_zpow_self x i j).eq
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]
  exact le_csSup (CFSG.RankThreeCoreUniqueness.Helpers.pRank_set_bddAbove 2 one_lt_two X)
    ⟨Subgroup.zpowers x, (Subgroup.zpowers_le).mpr hx, helem, by rw [Nat.card_zpowers, hord]; rfl⟩

theorem two_dvd_card_of_subset_mul [Finite G] {B C J : Subgroup G} (hCB : C ≤ B)
    (hJ : (J.subgroupOf B).Normal) (hJodd : Odd (Nat.card J))
    (hfac : (B : Set G) ⊆ (C : Set G) * (J : Set G)) (hB : 2 ∣ Nat.card B) :
    2 ∣ Nat.card C := by
  let φ : C →* B ⧸ J.subgroupOf B :=
    (QuotientGroup.mk' (J.subgroupOf B)).comp (Subgroup.inclusion hCB)
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (J.subgroupOf B) q
    obtain ⟨c, hc, x, hx, hcx⟩ := Set.mem_mul.mp (hfac b.2)
    refine ⟨⟨c, hc⟩, ?_⟩
    change (QuotientGroup.mk (Subgroup.inclusion hCB ⟨c, hc⟩) : B ⧸ J.subgroupOf B) =
      QuotientGroup.mk b
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    change c⁻¹ * (b : G) ∈ J
    rw [← hcx, inv_mul_cancel_left]
    exact hx
  have hJB : Nat.card (J.subgroupOf B) ∣ Nat.card J := by
    rw [← Subgroup.card_map_of_injective B.subtype_injective, Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (J.subgroupOf B)
  rw [hcard] at hB
  have hnot : ¬ 2 ∣ Nat.card (J.subgroupOf B) := fun h2 =>
    (Nat.not_even_iff_odd.mpr hJodd) (even_iff_two_dvd.mpr (h2.trans hJB))
  have hq : 2 ∣ Nat.card (B ⧸ J.subgroupOf B) :=
    (Nat.prime_two.dvd_mul.mp hB).resolve_right hnot
  exact hq.trans (Subgroup.card_dvd_of_surjective hφ)

theorem exists_commute_of_odd_card_conjugacyWithin [Finite G] {H : Subgroup G} {z : G}
    (hodd : Odd (Nat.card (conjugacyWithin H z))) {x : G} (hxH : x ∈ H) (hx : x ^ 2 = 1) :
    ∃ z₀ ∈ conjugacyWithin H z, Commute x z₀ := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq, hx])
  have hmem : ∀ w ∈ conjugacyWithin H z, x * w * x⁻¹ ∈ conjugacyWithin H z := by
    rintro w ⟨k, rfl⟩
    exact ⟨k * ⟨x, hxH⟩⁻¹, by simp [mul_assoc]⟩
  let f : conjugacyWithin H z → conjugacyWithin H z := fun w => ⟨x * w * x⁻¹, hmem w w.2⟩
  have hf : Function.Involutive f := fun w => Subtype.ext (by
    change x * (x * (w : G) * x⁻¹) * x⁻¹ = w
    rw [hxinv]
    calc x * (x * (w : G) * x) * x = (x * x) * w * (x * x) := by group
      _ = w := by rw [← sq, hx, one_mul, mul_one])
  set σ : Equiv.Perm (conjugacyWithin H z) := hf.toPerm f
  have hσ2 : σ ^ 2 = 1 := by
    ext w
    simp [sq, σ, hf w]
  have hpg : IsPGroup 2 (Subgroup.zpowers σ) := by
    rintro ⟨g, j, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change (σ ^ j) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσ2, one_zpow]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hw⟩ := hpg.nonempty_fixed_point_of_prime_not_dvd_card (conjugacyWithin H z)
    (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hodd))
  have hfw : f w = w := hw ⟨σ, Subgroup.mem_zpowers σ⟩
  refine ⟨w, w.2, ?_⟩
  have h1 : x * (w : G) * x⁻¹ = w := congrArg Subtype.val hfw
  calc x * (w : G) = x * w * x⁻¹ * x := by group
    _ = w * x := by rw [h1]

variable [Finite G]

theorem minimalLocalFailure_pair_stabilizer_two_rank_one
    (hcomm : ProperStrongEmbeddingCommutingImages G) (hR1 : SmallerR1Full G)
    (hW : HighRankPairWitnessTheorem G) (hNC : NoncentralPairActionTheorem G)
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1) :
    twoRank (pairPointStabilizer H beta) = 1 ∧
      ∀ t ∈ rightPairFlipFiber H z beta, ∃ z₀ ∈ conjugacyWithin H z,
        ∃ w ∈ pairPointStabilizer H beta, orderOf w = 2 ∧ Commute w t ∧ Commute w z₀ ∧
          ¬ Subgroup.centralizer ({w} : Set G) ≤ H ∧
          MinimalInvolutionPointLocalFailure H z₀ ∧
          involutionPointClass z₀ = involutionPointClass z := by
  obtain ⟨hodd, -, hdoubly, -⟩ := minimalLocalFailureSylowFixedPointsFromProperCommutingImages h
    hcomm
  have hz := h.local_datum.distinguished_order
  have hle : twoRank (pairPointStabilizer H beta) ≤ 1 := by
    by_contra hlt
    have hrank : 2 ≤ twoRank (pairPointStabilizer H beta) := by omega
    obtain ⟨t, ht⟩ := exists_mem_rightPairFlipFiber h.local_datum hbeta
    have hin := highRankPair_class_size_nine_or_twenty_seven hcomm hR1 hW hNC h hbeta hrank
    have hout := highRankPair_class_size_ne_nine_and_twenty_seven hcomm hR1 hW hNC h hbeta ht
      hrank
    rcases hin with h9 | h27
    · exact hout.1 h9
    · exact hout.2 h27
  have hge : 1 ≤ twoRank (pairPointStabilizer H beta) := by
    have hnotSE : ¬ fusionStronglyEmbedded H := by
      intro hSE
      apply h.failure
      rw [minimalLocalFailure_hull_eq_top h]
      have hmap := hSE.map_mulEquiv (Subgroup.topEquiv.symm : G ≃* (⊤ : Subgroup G))
      convert hmap using 1
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, MulEquiv.symm_symm]
      rfl
    have hHeven : Even (Nat.card H) := even_iff_two_dvd.mpr (by
      rw [← hz]
      exact Subgroup.orderOf_dvd_natCard H h.local_datum.distinguished_mem)
    obtain ⟨g, hg, hgeven⟩ : ∃ g : G, g ∉ H ∧
        ¬ Odd (Nat.card (H ⊓ H.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G)) := by
      by_contra hall
      push Not at hall
      exact hnotSE ⟨h.local_datum.proper, hHeven, fun g hg => hall g hg⟩
    have h2 : 2 ∣ Nat.card (H ⊓ H.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) :=
      even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hgeven)
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2
    rw [← pRank_inf_conj_eq_pair_twoRank hdoubly hbeta hg]
    exact one_le_pRank_two_of_mem y.2 ((Subgroup.orderOf_coe y).trans hy)
  refine ⟨le_antisymm hle hge, fun t ht => ?_⟩
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hfacK := pair_group_eq_centralizer_mul_odd_core h.local_datum S hzS hzcenter hbeta ht
  set B := pairPointStabilizer H beta
  have hBeven : 2 ∣ Nat.card B := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.RankThreeCoreUniqueness.Helpers.prime_dvd_card_of_pRank_pos 2 (⊤ : Subgroup B) (by
      change 0 < twoRank B
      omega)
  have hfacB : (B : Set G) ⊆ (B ⊓ Subgroup.centralizer ({t} : Set G) : Set G) *
      (pairOddCore H beta : Set G) := by
    intro b hb
    have hbK : b ∈ (pairFlipGroup H beta t : Set G) :=
      pairPointStabilizer_le_pairFlipGroup H beta t hb
    rw [hfacK] at hbK
    obtain ⟨c, hc, x, hx, rfl⟩ := Set.mem_mul.mp hbK
    have hxB : x ∈ B := (pairOddCore_le H beta t).1 hx
    have hcB : c ∈ B := by
      simpa using B.mul_mem hb (B.inv_mem hxB)
    exact Set.mem_mul.mpr ⟨c, ⟨hcB, hc.2⟩, x, hx, rfl⟩
  have hJnormal : ((pairOddCore H beta).subgroupOf B).Normal := by
    have hcomap : (pairOddCore H beta).subgroupOf B = CFSG.oddCore B :=
      Subgroup.comap_map_eq_self_of_injective B.subtype_injective _
    rw [hcomap]
    infer_instance
  have hCeven := two_dvd_card_of_subset_mul inf_le_left hJnormal (pairOddCore_odd H beta)
    hfacB hBeven
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 hCeven
  have hword : orderOf (w : G) = 2 := (Subgroup.orderOf_coe w).trans hw
  have hwB : (w : G) ∈ B := w.2.1
  have hwt : Commute (w : G) t := Subgroup.mem_centralizer_singleton_iff.mp w.2.2
  have hwH : (w : G) ∈ H := pairPointStabilizer_le_point H beta hwB
  obtain ⟨z₀, hz₀, hwz₀⟩ := exists_commute_of_odd_card_conjugacyWithin hodd hwH
    (orderOf_eq_prime_iff.mp hword).1
  obtain ⟨h₀, hclass, -⟩ := minimalLocalFailure_at_point_class_member h hz₀
  refine ⟨z₀, hz₀, w, hwB, hword, hwt, hwz₀, fun hle => ?_, h₀, hclass⟩
  exact pair_flip_not_mem_point hbeta ht
    (hle (Subgroup.mem_centralizer_singleton_iff.mpr hwt.eq.symm))

theorem pairStabilizerRankOneTheorem
    (hW : HighRankPairWitnessTheorem G)
    (hNC : NoncentralPairActionTheorem G) : PairStabilizerRankOneTheorem G :=
  fun _ _ h _ hbeta => minimalLocalFailure_pair_stabilizer_two_rank_one
    (properStrongEmbeddingCommutingImages_holds G) (smallerR1Full G) hW hNC h hbeta

end CFSG.ProperTwoGeneratedCore.HighRankPair
