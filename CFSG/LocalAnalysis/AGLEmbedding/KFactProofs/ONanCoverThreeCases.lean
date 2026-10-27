module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverRankFiveCensus
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverThreeAut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverThreeSylow
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowONan
import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeData
import CFSG.LieType.SteinbergBRSmallAltSylow
import CFSG.Alternating.Multipliers.Main
import CFSG.Monster.B.TwoA.Fischer.M22Aut
import CFSG.Sporadic.Bridge.M22
import CFSG.Sporadic.Bridge.ONSurj
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Certificate9504

public section

namespace CFSG.AGLEmbedding.KFactProofs.CoverThree

open CFSG.Open TauCeti CFSG.ComponentClassification.OuterAutomorphisms CFSG.AGLEmbedding
open CFSG.GH74.Generic (card_center_dvd_hopfMultiplier)
open CFSG.RankThree.PartTwo.Sec4.Census (SporadicMultipliers sporadicMultiplierOrder)
open CFSG.AGLEmbedding.KFactProofs.CoverFive (isQuasisimple_of_open)
open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.AGLEmbedding.R3
  CFSG.AGLEmbedding.R3.ONThree

theorem smallCover_conclusion {K X : Type} [Group K] [Finite K] [Group X]
    (hK : Open.IsQuasisimple K) (hZp : IsPGroup 3 (Subgroup.center K))
    (hZ : Subgroup.center K ≠ ⊥) (e : K ⧸ Subgroup.center K ≃* X) {m : ℕ}
    (hm : Nat.card (Subgroup.center K) ∣ m) (hm9 : ¬ 3 ^ 2 ∣ m) (h9 : 3 ^ 2 ∣ Nat.card X)
    (h27 : ¬ 3 ^ 3 ∣ Nat.card X) (hOut : IsPGroup 2 (Outer X)) :
    KGenTwoModAb 3 K ∧ Nat.card (Subgroup.center K) = 3 ∧ KOutNormalSylow 3 K := by
  have hZ3 := card_center_eq_three_of_dvd hZp hZ hm hm9
  have hOutK : KOutTwoGroup K :=
    kOutTwoGroup_of_isPGroup_outer hK (hOut.of_equiv (equivalence e).symm)
  exact ⟨kGenTwoModAb_of_small hK hZ3 e h9 h27 hOutK, hZ3,
    kOutNormalSylow_three_of_kOutTwoGroup hOutK⟩

theorem smallCover_alternating {K : Type} [Group K] [Finite K]
    (hK : Open.IsQuasisimple K) (hZp : IsPGroup 3 (Subgroup.center K))
    (hZ : Subgroup.center K ≠ ⊥) {n : ℕ} (hn : 5 ≤ n) (h67 : n = 6 ∨ n = 7)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    KGenTwoModAb 3 K ∧ Nat.card (Subgroup.center K) = 3 ∧ KOutNormalSylow 3 K := by
  have hdvd := card_center_dvd_hopfMultiplier (isQuasisimple_of_open hK) e
  rw [(CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput n hn).2] at hdvd
  simp only [h67, ↓reduceIte] at hdvd
  rcases h67 with rfl | rfl
  · refine smallCover_conclusion hK hZp hZ e hdvd (by norm_num) ?_ ?_
      CFSG.LieType.SteinbergBR.SmallAlt.isPGroup_outer_six
    · rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    · rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
  · refine smallCover_conclusion hK hZp hZ e hdvd (by norm_num) ?_ ?_
      CFSG.LieType.SteinbergBR.SmallAlt.isPGroup_outer_seven
    · rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    · rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]

theorem smallCover_M22
    (hSpor : SporadicMultipliers) {K : Type} [Group K] [Finite K] (hK : Open.IsQuasisimple K)
    (hZp : IsPGroup 3 (Subgroup.center K)) (hZ : Subgroup.center K ≠ ⊥)
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.sporadic .M22).Group) :
    KGenTwoModAb 3 K ∧ Nat.card (Subgroup.center K) = 3 ∧ KOutNormalSylow 3 K := by
  have hdvd := card_center_dvd_hopfMultiplier (isQuasisimple_of_open hK) e
  rw [hSpor.1 .M22] at hdvd
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have hcard : Nat.card (CFSGIndex.sporadic .M22).Group = 443520 := by
    rw [← Nat.card_congr b.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M22
  have hout : Nat.card (Outer NativeSporadic.M22) = 2 :=
    CFSG.Monster.B.TwoA.Fischer.catalog_M22_full_automorphism_order.2.1
  have hOut : IsPGroup 2 (Outer (CFSGIndex.sporadic .M22).Group) :=
    (IsPGroup.of_card (n := 1) (by rw [hout, pow_one])).of_equiv (equivalence b)
  exact smallCover_conclusion hK hZp hZ e hdvd (by norm_num [sporadicMultiplierOrder])
    (by rw [hcard]; norm_num) (by rw [hcard]; norm_num) hOut

theorem coverWeakGen_ONan_three
    [Finite (NativeSporadic.Carrier .ONan)] :
    @CoverWeakGen (NativeSporadic.Carrier .ONan) _ 3 ⟨Nat.prime_three⟩ :=
  coverWeakGen_of_coverPointDatum (by norm_num)
    (coverPointDatum_of_check (spec3 154) (D := cpSpec) Nat.prime_three
      Certificates.certificate9504.2.1 Certificates.certificate9504.2.2)

theorem weakCore_and_rank_of_data {K X : Type} [Group K] [Finite K] [Group X]
    (hK : Open.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (hZp : IsPGroup 3 (Subgroup.center K)) (hZc : IsCyclic (Subgroup.center K))
    (hZ3 : Nat.card (Subgroup.center K) = 3) (e : K ⧸ Subgroup.center K ≃* X)
    (hcw : ∀ [Finite X], @CoverWeakGen X _ 3 ⟨Nat.prime_three⟩) (hD : AbelianSylowDatum X 3)
    (h3 : 3 ^ 3 ∣ Nat.card X) (T : Sylow 3 K) :
    GLBWeakCore 3 (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank 3 (⊤ : Subgroup K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperf : Group.IsPerfect K := ⟨hK.1⟩
  obtain ⟨π, hπ, hker⟩ := exists_surjective_ker_eq_center e
  have : Finite X := Finite.of_surjective π hπ
  exact ⟨hcw K π hπ hker hperf hZ hZp hZc T,
    three_le_pRank_cover_of_abelianSylowDatum π hπ hker hZ3 hZp hZc hD h3⟩

theorem onan_case
    (hSpor : SporadicMultipliers) {K : Type} [Group K] [Finite K]
    (hK : Open.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (hZp : IsPGroup 3 (Subgroup.center K)) (hZc : IsCyclic (Subgroup.center K))
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.sporadic .ONan).Group) (T : Sylow 3 K) :
    GLBWeakCore 3 (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank 3 (⊤ : Subgroup K) := by
  have hdvd := card_center_dvd_hopfMultiplier (isQuasisimple_of_open hK) e
  rw [hSpor.1 .ONan] at hdvd
  have hZ3 := card_center_eq_three_of_dvd hZp hZ (m := sporadicMultiplierOrder .ONan) hdvd
    (by norm_num [sporadicMultiplierOrder])
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have e' : K ⧸ Subgroup.center K ≃* NativeSporadic.Carrier .ONan := e.trans b.symm
  have hcw : ∀ [Finite (NativeSporadic.Carrier .ONan)],
      @CoverWeakGen (NativeSporadic.Carrier .ONan) _ 3 ⟨Nat.prime_three⟩ :=
    fun [_] => coverWeakGen_ONan_three
  have hD : AbelianSylowDatum (NativeSporadic.Carrier .ONan) 3 := abelianSylowDatum_ON_three
  have h3 : 3 ^ 3 ∣ Nat.card (NativeSporadic.Carrier .ONan) := by
    show 3 ^ 3 ∣ Nat.card NativeSporadic.ON
    rw [CFSG.Sporadic.ON.card_ON]
    norm_num
  exact weakCore_and_rank_of_data hK hZ hZp hZc hZ3 e' hcw hD h3 T

end CFSG.AGLEmbedding.KFactProofs.CoverThree
