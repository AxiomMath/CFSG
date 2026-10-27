module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryPairIndexStatement
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryPairIndexTransfer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryPairIndexHomology
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryPairIndexCount
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ThreePointLeastFailure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ShultCentralizerIndices
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryPairIndexTorus

public section

namespace CFSG.ProperTwoGeneratedCore.UnitaryPairIndex

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator
open CFSG.ProperTwoGeneratedCore.PairHullCommonCentralizer
open CFSG.ProperTwoGeneratedCore.CosetNormalizer
open CFSG.ProperTwoGeneratedCore.HighRankPair
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism CFSG.ShultStronglyClosedTI.UnitaryExcluded
open scoped commutatorElement

namespace Saturation

variable {G : Type} [Group G]

theorem mem_normalizer_sup {A B : Subgroup G} {t : G} (hA : t ∈ Subgroup.normalizer (A : Set G))
    (hB : t ∈ Subgroup.normalizer (B : Set G)) :
    t ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ s : G, s ∈ Subgroup.normalizer (A : Set G) →
      s ∈ Subgroup.normalizer (B : Set G) → ∀ h ∈ A ⊔ B, s * h * s⁻¹ ∈ A ⊔ B := by
    intro s hsA hsB h hh
    have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj s).toMonoidHom := by
      apply sup_le
      · intro a ha
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hsA a).mp ha)
      · intro b hb
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hsB b).mp hb)
    exact hle hh
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact key t hA hB h
  · intro hh
    have := key t⁻¹ (Subgroup.inv_mem _ hA) (Subgroup.inv_mem _ hB) _ hh
    simpa [mul_assoc] using this

theorem eq_one_of_mul_self_eq_one_of_odd [Finite G] {c : G} {I : Subgroup G}
    (hIodd : Odd (Nat.card I)) (hc : c ∈ I) (hcc : c * c = 1) : c = 1 := by
  have hodd : Odd (orderOf c) := by
    have := orderOf_dvd_natCard (⟨c, hc⟩ : I)
    rw [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hIodd this
  have h2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hcc])
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

end Saturation

open Saturation

theorem unitaryMonomialTheorem_of_pairGeneration
    (G : Type) [Group G] [Finite G]
    (hgen : RankOnePair.PairCommutatorGenerationTheorem G)
    (hker : UnitaryInvolutoryKernelsConclusion G) : UnitaryMonomialTheorem G := by
  intro H z h beta hbeta t ht hrank w hwB hw hwz hwt hdeg
  classical
  obtain ⟨-, hKv, hoddw, hoddv⟩ := hker H z h beta hbeta t ht hrank w hwB hw hwz hwt hdeg
  have hgen' := hgen H z h beta hbeta t ht
  obtain ⟨f, hf, hq, W₀, hW₀E, hW₀L, hW₀t, hW₀U, hW₀LE, hW₀card, g, hgL, hgz, hgW⟩ :=
    Torus.unitary_pair_hull_torus h hbeta ht hrank hwB hw hwz hwt hdeg hoddw
  obtain ⟨k, _, _, _, J, hJ, hk, hfixJ, hW₀wt, φ, hφ⟩ :=
    Transfer.unitary_pair_torus_in_wt h hbeta ht hrank hwB hw hwz hwt hdeg hKv hoddv hf hq hW₀L
      hW₀U hW₀card hgL hgz hgW
  have hcomm := properStrongEmbeddingCommutingImages_holds G
  have hR1 := smallerR1Full G
  have hz2 := h.local_datum.distinguished_order
  have htclass : t ∈ involutionPointClass z := ht.1
  have ht2 : orderOf t = 2 := order_two_of_mem_pointClass hz2 htclass
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
  have hIE : pairOddCore H beta ≤ pairPointStabilizer H beta := (pairOddCore_le H beta t).1
  have hIodd : Odd (Nat.card (pairOddCore H beta)) := pairOddCore_odd H beta
  have hInorm : pairFlipGroup H beta t ≤ Subgroup.normalizer (pairOddCore H beta : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (pairOddCore_le H beta t).2.1).mp
      (pairOddCore_normal_in_pair_group hz2 hbeta ht)
  have hEN : pairPointStabilizer H beta ≤ Subgroup.normalizer (pairOddCore H beta : Set G) :=
    (pairPointStabilizer_le_pairFlipGroup H beta t).trans hInorm
  have htI : t ∈ Subgroup.normalizer (pairOddCore H beta : Set G) :=
    hInorm (flip_mem_pairFlipGroup H beta t)
  have hwI : w ∈ Subgroup.normalizer (pairOddCore H beta : Set G) := hEN hwB
  obtain ⟨S, hzS, hzc⟩ := h.central_sylow
  have hEt : ⁅pairPointStabilizer H beta, Subgroup.zpowers t⁆ ≤ pairOddCore H beta :=
    commutator_pairPointStabilizer_le h.local_datum S hzS hzc hbeta ht
  have htE : t ∈ Subgroup.normalizer (pairPointStabilizer H beta : Set G) :=
    flip_mem_normalizer_pairPointStabilizer hz2 hbeta ht
  have hwt' : Commute t (w * t) := (hwt.symm.mul_right (Commute.refl t))
  have htLwt : t ∈ localInvolutionPointHull z (w * t) :=
    mem_localInvolutionPointHull htclass hwt'
  have htLw : t ∈ localInvolutionPointHull z w := mem_localInvolutionPointHull htclass hwt.symm
  have hwtne : w ≠ t := by
    intro hwteq
    have : t ∈ pairPointStabilizer H beta := hwteq ▸ hwB
    have htH : t ∈ H := by
      have := this.1
      rwa [rightCosetStabilizer_base] at this
    exact not_mem_of_mem_rightPairFlipFiber hbeta ht htH
  have hcommI : ∀ (A : Subgroup G), A ≤ pairOddCore H beta →
      ⁅A, Subgroup.zpowers t⁆ ≤ pairOddCore H beta := by
    intro A hA
    exact (Subgroup.commutator_mono (hA.trans hIE) le_rfl).trans hEt
  have hXL := commutator_centralizer_le_localHull (z := z) (pairOddCore H beta) htLwt
  have hXI := hcommI _ (inf_le_left : pairOddCore H beta ⊓ Subgroup.centralizer {w * t} ≤ _)
  have hYL := commutator_centralizer_le_localHull (z := z) (pairOddCore H beta) htLw
  have hYI := hcommI _ (inf_le_left : pairOddCore H beta ⊓ Subgroup.centralizer {w} ≤ _)
  have hW₀ne : ∃ a ∈ W₀, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : W₀ = ⊥ := (Subgroup.eq_bot_iff_forall W₀).mpr hcon
    rw [hbot, Subgroup.card_bot] at hW₀card
    have hpos : 0 < Nat.gcd 3 (2 ^ f + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hle : Nat.gcd 3 (2 ^ f + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have hmul := Nat.div_mul_cancel (Nat.gcd_dvd_right 3 (2 ^ f + 1))
    rw [← hW₀card, one_mul] at hmul
    omega
  have hkey : ¬ ∀ a ∈ W₀, ∀ x ∈ ⁅pairOddCore H beta ⊓ Subgroup.centralizer {w * t},
      Subgroup.zpowers t⁆, a * x = x * a := by
    intro hcent
    obtain ⟨a, ha, ha1⟩ := hW₀ne
    have hzU : z ∈ ({1} ∪ distinguishedRoots H z w : Set G) :=
      Or.inr ⟨⟨distinguished_mem_pointClass z, h.local_datum.distinguished_mem⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr hwz.symm.eq⟩
    have htop : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({a} : Set G) := by
      rw [← hgen']
      refine sup_le (sup_le ?_ ?_) ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (hW₀U a ha z hzU).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (hW₀t a ha).symm
      ·
        have hgen4 := odd_four_group_ambient_commutator_generation (pairOddCore H beta) w t hw
          ht2 hwtne hwt hwI htI hIodd
        have hrc : rightInvolutionCommutatorSubgroup t (pairOddCore H beta) ≤
            ⁅pairOddCore H beta, Subgroup.zpowers t⁆ := by
          rw [rightInvolutionCommutatorSubgroup, Subgroup.closure_le]
          rintro _ ⟨j, rfl⟩
          rw [Subgroup.commutator_comm]
          have := Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ (Subgroup.mem_zpowers t))
            (Subgroup.inv_mem _ j.2)
          simpa [commutatorElement_def, mul_assoc] using this
        refine hrc.trans ?_
        rw [hgen4]
        apply sup_le
        · intro y hy
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (hW₀LE a ha y ⟨hYL hy, hIE (hYI hy)⟩).symm
        · intro y hy
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (hcent a ha y hy).symm
    have hcen : a ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subgroup.mem_centralizer_singleton_iff.mp (htop (Subgroup.mem_top y))
    obtain ⟨hsimple, x, y, hxy⟩ := minimalLocalFailure_nonabelian_simple h
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hbot | htop'
    · rw [hbot] at hcen
      exact ha1 (Subgroup.mem_bot.mp hcen)
    · exact hxy (Subgroup.mem_center_iff.mp (htop' ▸ Subgroup.mem_top y) x)
  have hH'E : (W₀ ⊔ pairOddCore H beta) ⊓ localInvolutionPointHull z (w * t) ≤
      pairPointStabilizer H beta := inf_le_left.trans (sup_le hW₀E hIE)
  have hXH' : ⁅pairOddCore H beta ⊓ Subgroup.centralizer {w * t}, Subgroup.zpowers t⁆ ≤
      (W₀ ⊔ pairOddCore H beta) ⊓ localInvolutionPointHull z (w * t) :=
    le_inf (hXI.trans le_sup_right) hXL
  have hWH : ⁅W₀, (W₀ ⊔ pairOddCore H beta) ⊓ localInvolutionPointHull z (w * t)⁆ ≠ ⊥ := by
    intro hbot
    apply hkey
    intro a ha x hx
    have hac := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot) ha
    exact ((Subgroup.mem_centralizer_iff.mp hac) x (hXH' hx)).symm
  have hsolv : Group.IsSolvable
      ((W₀ ⊔ pairOddCore H beta) ⊓ localInvolutionPointHull z (w * t) : Subgroup G) := by
    apply CFSG.FeitThompson.isSolvable_of_odd_natCard _
    have hW₀N : W₀ ≤ Subgroup.normalizer (pairOddCore H beta : Set G) := hW₀E.trans hEN
    have h1 := card_sup_mul_card_inf hW₀N
    have hW₀odd : Odd (Nat.card W₀) := by
      rw [hW₀card]
      exact Inner.odd_torus_order (by omega)
    have hodd2 : Odd (Nat.card (pairOddCore H beta ⊔ W₀ : Subgroup G)) := by
      have h2 : Odd (Nat.card (pairOddCore H beta ⊔ W₀ : Subgroup G) *
          Nat.card (pairOddCore H beta ⊓ W₀ : Subgroup G)) := by
        rw [h1]
        exact hIodd.mul hW₀odd
      exact (Nat.odd_mul.mp h2).1
    have hle : (W₀ ⊔ pairOddCore H beta) ⊓ localInvolutionPointHull z (w * t) ≤
        pairOddCore H beta ⊔ W₀ := inf_le_left.trans (le_of_eq (sup_comm _ _))
    exact Odd.of_dvd_nat hodd2 (Subgroup.card_dvd_of_le hle)
  have htW₀ : t ∈ Subgroup.normalizer (W₀ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hW₀t x hx, mul_inv_cancel_right]
      exact hx
    · intro hx
      have := hW₀t _ hx
      have hx' : x = t * x * t⁻¹ := by
        calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
          _ = t⁻¹ * (t * (t * x * t⁻¹)) := by rw [mul_assoc t⁻¹, ← this]
          _ = t * x * t⁻¹ := by group
      rw [hx']
      exact hx
  have htL : t ∈ Subgroup.normalizer (localInvolutionPointHull z (w * t) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have := conj_mem_localHull_of_commute (z := z) hwt'.inv_left hx
      simpa only [inv_inv] using this
    · intro hx
      have := conj_mem_localHull_of_commute (z := z) hwt' hx
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using this
  have htH' : t ∈ Subgroup.normalizer
      (((W₀ ⊔ pairOddCore H beta) ⊓ localInvolutionPointHull z (w * t) : Subgroup G) : Set G) := by
    have h1 := mem_normalizer_sup htW₀ htI
    rw [Subgroup.mem_normalizer_iff] at h1 htL ⊢
    intro x
    exact and_congr (h1 x) (htL x)
  have hfixΩ : ∀ ω ∈ pointFixedSet H
      ((W₀ ⊔ pairOddCore H beta) ⊓ localInvolutionPointHull z (w * t)),
      ω = rightCosetMk H 1 ∨ ω = beta := by
    intro ω hω
    by_contra hcon
    push Not at hcon
    obtain ⟨hωα, hωβ⟩ := hcon
    have hαfix : rightCosetMk H 1 ∈ pointFixedSet H
        ((W₀ ⊔ pairOddCore H beta) ⊓ localInvolutionPointHull z (w * t)) :=
      (mem_pointFixedSet_iff H _ _).mpr ((hH'E).trans inf_le_left)
    have hβfix : beta ∈ pointFixedSet H
        ((W₀ ⊔ pairOddCore H beta) ⊓ localInvolutionPointHull z (w * t)) :=
      (mem_pointFixedSet_iff H _ _).mpr ((hH'E).trans inf_le_right)
    have h3 : 3 ≤ Nat.card (pointFixedSet H
        ((W₀ ⊔ pairOddCore H beta) ⊓ localInvolutionPointHull z (w * t))) := by
      have hsub : ({rightCosetMk H 1, beta, ω} : Set (pointRightCosetSpace H)) ⊆
          pointFixedSet H ((W₀ ⊔ pairOddCore H beta) ⊓ localInvolutionPointHull z (w * t)) := by
        intro x hx
        rcases hx with rfl | rfl | rfl
        · exact hαfix
        · exact hβfix
        · exact hω
      have hcard3 : ({rightCosetMk H 1, beta, ω} : Set (pointRightCosetSpace H)).ncard = 3 :=
        Set.ncard_eq_three.mpr ⟨_, _, _, hbeta.symm, Ne.symm hωα, Ne.symm hωβ, rfl⟩
      rw [Nat.card_coe_set_eq, ← hcard3]
      exact Set.ncard_le_ncard hsub (Set.toFinite _)
    have hbot :=
      RankOnePair.minimalLocalFailure_rank_one_pair_three_point_normalized_subgroup_centralization
        h hcomm hR1 beta hbeta hrank t ht _ hH'E htH' h3
    apply hkey
    intro a _ x hx
    have hXbot : ⁅pairOddCore H beta ⊓ Subgroup.centralizer {w * t}, Subgroup.zpowers t⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro c hc
      have hct : ⁅c, t⁆ ∈ ⁅pairOddCore H beta ⊓ Subgroup.centralizer {w * t},
          Subgroup.zpowers t⁆ := Subgroup.commutator_mem_commutator hc (Subgroup.mem_zpowers t)
      have hcomm' := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot) (hXH' hct)
      have hctt : ⁅c, t⁆ * t = t * ⁅c, t⁆ :=
        (Subgroup.mem_centralizer_iff.mp hcomm' t (Subgroup.mem_zpowers t)).symm
      have hinv := conj_commutatorElement_eq_inv ht2 c
      have hself : t⁻¹ * ⁅c, t⁆ * t = ⁅c, t⁆ := by rw [mul_assoc, hctt, inv_mul_cancel_left]
      have hcc : ⁅c, t⁆ * ⁅c, t⁆ = 1 := by
        calc ⁅c, t⁆ * ⁅c, t⁆ = ⁅c, t⁆ * (t⁻¹ * ⁅c, t⁆ * t) := by rw [hself]
          _ = ⁅c, t⁆ * ⁅c, t⁆⁻¹ := by rw [hinv]
          _ = 1 := mul_inv_cancel _
      have h1 := eq_one_of_mul_self_eq_one_of_odd hIodd (hXI hct) hcc
      have hct' : c * t = t * c := by
        rw [commutatorElement_def] at h1
        have := mul_inv_eq_one.mp h1
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((Commute.zpow_right (show Commute c t from hct') n).symm).eq
    rw [hXbot, Subgroup.mem_bot] at hx
    rw [hx, mul_one, one_mul]
  obtain ⟨hH'eq, -, hncard⟩ :=
    Homology.unitary_homology_subgroup_saturates_hyperbolic_rightCoset J (by omega) hk hfixJ hJ
      (scalarCenter J) le_rfl hbeta (localInvolutionPointHull z (w * t)) φ htLwt ht2 ht.2 hIE
      hEN hIodd hEt hW₀E hW₀wt hφ hW₀t hsolv hWH hfixΩ
  have hXle : pairOddCore H beta ⊓ localInvolutionPointHull z (w * t) ≤
      pairOddCore H beta ⊓ Subgroup.centralizer {w * t} :=
    inf_le_inf_left _ (localInvolutionPointHull_le_centralizer z (w * t))
  have hXn : t ∈ Subgroup.normalizer
      ((pairOddCore H beta ⊓ localInvolutionPointHull z (w * t) : Subgroup G) : Set G) := by
    have h1 := htI
    have h2 := htL
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro x
    exact and_congr (h1 x) (h2 x)
  have hXt : ∀ c ∈ pairOddCore H beta ⊓ Subgroup.centralizer {w * t},
      t * (c * t * c⁻¹) ∈ pairOddCore H beta ⊓ localInvolutionPointHull z (w * t) := by
    rintro c ⟨hcI, hcw⟩
    have hcwt : Commute c (w * t) := Subgroup.mem_centralizer_singleton_iff.mp hcw
    refine ⟨?_, ?_⟩
    · have h1 : t * c * t⁻¹ ∈ pairOddCore H beta :=
        (Subgroup.mem_normalizer_iff.mp htI c).mp hcI
      have h2 : t * (c * t * c⁻¹) = (t * c * t⁻¹) * c⁻¹ := by rw [htinv]; group
      rw [h2]
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hcI)
    · have h1 := conj_mem_localHull_of_commute (z := z) hcwt.inv_left htLwt
      rw [inv_inv] at h1
      exact Subgroup.mul_mem _ htLwt h1
  rw [Count.relIndex_eq_ncard_conj (pairPointStabilizer H beta) (pairOddCore H beta)
      (pairOddCore H beta ⊓ localInvolutionPointHull z (w * t)) ht2 hw hwt hwB htE hIE
      (pairOddCore_subgroupOf_normal H beta) hIodd hEt hXle hXn hXt, ← hH'eq, hncard, hq]

end CFSG.ProperTwoGeneratedCore.UnitaryPairIndex
