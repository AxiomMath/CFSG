module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenFix
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicMultD1
import CFSG.LocalAnalysis.AGLEmbedding.CoverAbelianSylow
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverTorusRank
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanThreeCoverSpor
import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeData
import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaListLifts
import CFSG.Monster.B.TwoA.Fischer.M22Aut
import CFSG.RankThree.PartOne.K159.CenterRank
import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverE6RankMain
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverThreeCases
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverThreeRank

public section

namespace CFSG.AGLEmbedding.SporadicMultD1

open CFSG.Open CFSG.Assembly.LowTwoRank TauCeti
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.RankThree.PartTwo.Sec4.Census (tripleCoverAlternating tripleCoverLie_of_griess)
open CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.AGLEmbedding.KFactProofs CFSG.AGLEmbedding.KFactProofs.CoverFive

theorem four_le_pRank_three_or_residual_of_multD1 (hGA : GriessMultipliersAllModels)
    (hD : SporadicMultipliersD1)
    {K : Type} [Group K] [Finite K] (hq : Open.IsQuasisimple K)
    (hcat : IsCatalogGroup (K ⧸ Subgroup.center K)) (hZ : Subgroup.center K ≠ ⊥)
    (hZp : IsPGroup 3 (Subgroup.center K)) (hZc : IsCyclic (Subgroup.center K)) :
    4 ≤ Open.pRank 3 (⊤ : Subgroup K) ∨
      ∃ i : CFSGIndex, IsCoverThreeResidualIndex i ∧
        Nonempty (K ⧸ Subgroup.center K ≃* i.Group) := by
  obtain ⟨i, ⟨e⟩⟩ := hcat
  have hq' : CFSG.IsQuasisimple K := isQuasisimple_of_open hq
  have h3 : 3 ∣ Nat.card (Subgroup.center K) :=
    dvd_card_center_of_isPGroup Nat.prime_three hZ hZp
  have hodd : Odd (Nat.card (Subgroup.center K)) :=
    odd_card_center_of_isPGroup Nat.prime_three (by norm_num) hZp
  by_cases hrk : 4 ≤ Open.pRank 3 (⊤ : Subgroup K)
  · exact Or.inl hrk
  have hrk' : Open.pRank 3 (⊤ : Subgroup K) ≤ 3 := by omega
  refine Or.inr ⟨i, ?_, ⟨e⟩⟩
  cases i with
  | cyclic r hr =>
    exfalso
    obtain ⟨a, b, hab⟩ := hq'.2.2
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm (G := Multiplicative (ZMod r)) _ _
  | alternating n hn =>
    exact tripleCoverAlternating n K hn ⟨hq', h3, ⟨e⟩⟩
  | sporadic s =>
    rcases hD.sporadic_cases_of_three_dvd hq' e h3 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso
      have := HasLiftableTriple.four_le_pRank_of_cover kFactLiftJ3 e h3
      omega
    · exact (ThreeCover.false_McL hq hZp hZ hZc hrk' e).elim
    · exact (ThreeCover.false_Suz hZp hZ hZc hrk' e).elim
    · exact Or.inr rfl
    · exact (ThreeCover.false_Fi22 hZp hZ hZc hrk' e).elim
    · exact (ThreeCover.false_Fi24 hZp hZ hZc hrk' e).elim
  | lie d =>
    have hidx := tripleCoverLie_of_griess hGA d K ⟨hq', h3, ⟨e⟩⟩
    obtain ⟨dd, hv⟩ := d
    cases dd with
    | A r q =>
      obtain ⟨hpn, hpq⟩ := hidx
      by_cases hr : r + 1 = 3
      · exact Or.inl ⟨by omega, hpq⟩
      · exfalso
        have hmod := statedClassicalModel_psl_of_typeA r q hv e
        obtain ⟨B, hBp, hBc, hBcard⟩ := exists_elemAbelian_four_psl_of_ne_two Nat.prime_three
          (by norm_num) (by omega) h3 hodd hmod hpn (by simpa only [PrimePower.card_def] using hpq)
        have := le_pRank_of_pow_le_card Nat.prime_three le_top
          ⟨⟨⟨fun a b => Subtype.ext (hBc a a.2 b b.2)⟩⟩, hBp⟩ hBcard
        omega
    | twistedA r q =>
      rcases hidx with ⟨hpn, hpq⟩ | ⟨rfl, hq3⟩
      · by_cases hr : r + 1 = 3
        · exact Or.inl ⟨by omega, hpq⟩
        · exfalso
          have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
          obtain ⟨B, hBp, hBc, hBcard⟩ := exists_elemAbelian_four_psu_of_ne_two Nat.prime_three
            (by norm_num) (by omega) h3 hodd hmod hpn
            (by simpa only [PrimePower.card_def] using hpq)
          have := le_pRank_of_pow_le_card Nat.prime_three le_top
            ⟨⟨⟨fun a b => Subtype.ext (hBc a a.2 b b.2)⟩⟩, hBp⟩ hBcard
          omega
      · exfalso
        have := HasLiftableTriple.four_le_pRank_of_cover (kFactLiftU43 q hv hq3) e h3
        omega
    | B r q =>
      exfalso
      obtain ⟨rfl, hq3⟩ := hidx
      obtain ⟨hp3, -⟩ := CFSG.RankThree.PartOne.N143.primePower_eq_three hq3
      have hp2 : q.p ≠ 2 := by omega
      obtain ⟨-, F, _, _, hF3, ⟨eF⟩⟩ :=
        CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd 3 q hv hp2 le_rfl
          (G := K ⧸ Subgroup.center K) e
      have hF : Nat.card F = 3 := by rw [hF3, ← PrimePower.card_def]; exact hq3
      let e' : K ⧸ Subgroup.center K ≃* ↥CFSG.RankThree.PartOne.N143.O7.Om :=
        eF.trans (CFSG.RankThree.PartOne.N143.O7.modelEquiv hF)
      let φ' : K →* ↥CFSG.RankThree.PartOne.N143.O7.Om :=
        e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
      have hφ' : Function.Surjective φ' := e'.surjective.comp (QuotientGroup.mk'_surjective _)
      have hker : φ'.ker = Subgroup.center K :=
        CFSG.RankThree.PartOne.K159.ker_comp_mk'_eq_center e'
      have h4 := CFSG.RankThree.PartOne.N143.O7.four_le_localRank_of_cover φ' hφ' hker.le
        (by rw [hker]; exact h3)
      have := h4.trans (localRank_le_pRank Nat.prime_three)
      omega
    | G2 q =>
      exfalso
      have := HasLiftableTriple.four_le_pRank_of_cover (kFactLiftG23 q hv hidx) e h3
      omega
    | E6 q => exact Or.inr hidx
    | twistedE6 q => exact Or.inr hidx
    | C r q => exact hidx.elim
    | D r q => exact hidx.elim
    | twistedD r q => exact hidx.elim
    | E7 q => exact hidx.elim
    | E8 q => exact hidx.elim
    | F4 q => exact hidx.elim
    | trialityD4 q => exact hidx.elim
    | suzuki m => exact hidx.elim
    | reeG2 m => exact hidx.elim
    | reeF4 m => exact hidx.elim
    | tits => exact hidx.elim

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.AGLEmbedding.KFactProofs.CoverThree
open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.AGLEmbedding.R3
  CFSG.AGLEmbedding.R3.ONThree

theorem smallCover_M22_of_multD1
    (hD : SporadicMultipliersD1) {K : Type} [Group K] [Finite K] (hK : Open.IsQuasisimple K)
    (hZp : IsPGroup 3 (Subgroup.center K)) (hZ : Subgroup.center K ≠ ⊥)
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.sporadic .M22).Group) :
    KGenTwoModAb 3 K ∧ Nat.card (Subgroup.center K) = 3 ∧ KOutNormalSylow 3 K := by
  have hdvd : Nat.card (Subgroup.center K) ∣ 3 :=
    hD.card_center_dvd_three_of_mem (isQuasisimple_of_open hK) hZp (by decide) e
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have hcard : Nat.card (CFSGIndex.sporadic .M22).Group = 443520 := by
    rw [← Nat.card_congr b.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M22
  have hout : Nat.card (Outer NativeSporadic.M22) = 2 :=
    CFSG.Monster.B.TwoA.Fischer.catalog_M22_full_automorphism_order.2.1
  have hOut : IsPGroup 2 (Outer (CFSGIndex.sporadic .M22).Group) :=
    (IsPGroup.of_card (n := 1) (by rw [hout, pow_one])).of_equiv (equivalence b)
  exact smallCover_conclusion hK hZp hZ e hdvd (by norm_num)
    (by rw [hcard]; norm_num) (by rw [hcard]; norm_num) hOut

theorem weakCore_rank_onan
    {K : Type} [Group K] [Finite K]
    (hK : Open.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (hZp : IsPGroup 3 (Subgroup.center K)) (hZc : IsCyclic (Subgroup.center K))
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.sporadic .ONan).Group) (T : Sylow 3 K) :
    GLBWeakCore 3 (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank 3 (⊤ : Subgroup K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have e' : K ⧸ Subgroup.center K ≃* NativeSporadic.Carrier .ONan := e.trans b.symm
  have hD : AbelianSylowDatum (NativeSporadic.Carrier .ONan) 3 := abelianSylowDatum_ON_three
  have hperf : Group.IsPerfect K := ⟨hK.1⟩
  obtain ⟨π, hπ, hker⟩ := exists_surjective_ker_eq_center e'
  have hexp := (coverAbelianSylowLemma K _ π hπ hker hperf 3 Nat.prime_three (by norm_num) hZ hZp
    hZc hD T).1
  have hZT : Subgroup.center K ≤ (T : Subgroup K) := IsPGroup.le_sylow_of_normal hZp T
  have hdvd : Nat.card (Subgroup.center K) ∣ 3 := by
    have := hZc
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one fun z => Subtype.ext (hexp z.1 (hZT z.2))
  have hZ3 := card_center_eq_three_of_dvd hZp hZ (m := 3) hdvd (by norm_num)
  have hcw : ∀ [Finite (NativeSporadic.Carrier .ONan)],
      @CoverWeakGen (NativeSporadic.Carrier .ONan) _ 3 ⟨Nat.prime_three⟩ :=
    fun [_] => coverWeakGen_ONan_three
  have h3 : 3 ^ 3 ∣ Nat.card (NativeSporadic.Carrier .ONan) := by
    show 3 ^ 3 ∣ Nat.card NativeSporadic.ON
    rw [CFSG.Sporadic.ON.card_ON]
    norm_num
  exact weakCore_and_rank_of_data hK hZ hZp hZc hZ3 e' hcw hD h3 T

end CFSG.AGLEmbedding.SporadicMultD1

namespace CFSG.AGLEmbedding

open CFSG.Open TauCeti
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.AGLEmbedding.KFactProofs.CoverThree CFSG.AGLEmbedding.SporadicMultD1

theorem kFactCoverThreeFix_of_multD1
    (hGA : GriessMultipliersAllModels) (hD : SporadicMultipliersD1) : KFactCoverThreeFix := by
  intro K _ _ hK hcat hZ hZp hZc hrank T
  rcases four_le_pRank_three_or_residual_of_multD1 hGA hD hK hcat hZ hZp hZc with
    h4 | ⟨i, hi, ⟨e⟩⟩
  · omega
  · cases i with
    | cyclic r hr => exact hi.elim
    | alternating n hn =>
      obtain ⟨h1, h2, h3⟩ := smallCover_alternating hK hZp hZ hn hi e
      exact Or.inl ⟨kGenTwoModAbFix_of_kGenTwoModAb h1, h2, h3⟩
    | sporadic s =>
      rcases hi with rfl | rfl
      · obtain ⟨h1, h2, h3⟩ := smallCover_M22_of_multD1 hD hK hZp hZ e
        exact Or.inl ⟨kGenTwoModAbFix_of_kGenTwoModAb h1, h2, h3⟩
      · exact Or.inr (weakCore_rank_onan hK hZ hZp hZc e T)
    | lie d =>
      rcases hi with hi | hi
      · exact Or.inl (linThreeFix_case hGA sl3CoverGenTwoModAbFix hK hZp hZ
          (isLinThreeCover3_of_isLieThreeIndex hi) e)
      · exact absurd (coverE6RankFour K hK hZ hZp hZc d hi ⟨e⟩) (by omega)

end CFSG.AGLEmbedding
