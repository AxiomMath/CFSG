module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3AEightThirteenR3
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81LThreeFourAutDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineTwelveOneCfgOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightBridge
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneComp
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneSection
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneLayer
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenTwentyTwo
import CFSG.RankThree.PartTwo.KFacts.L34CenterProof
import CFSG.RankThree.PartTwo.Sec18.Item186a

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem agl81NineTwelveLThreeFour_of
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (hL34 : KFactLThreeFourAutSection) : AGL81NineTwelveLThreeFour G := by
  intro hS _ _ _ H _ _ hH _ _ K hKc hKL
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  haveI := hS.simple
  have hHtop : H ≠ ⊤ := CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hS.nonab hH.1
  obtain ⟨Y', hY', hYK⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_isPComponent_of_isComponent
    3 (isComponent_of_isComponentOf_top'' hKc)
  set Y : Subgroup G := Y'.map H.subtype with hYdef
  have hYY : Y.subgroupOf H = Y' :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hY : IsPComponentIn 3 Y H := ⟨Subgroup.map_subtype_le _, by rw [hYY]; exact hY'⟩
  have hYH : Y ≤ H := hY.1
  haveI : Group.IsPerfect ↥Y := IsPComponentIn.isPerfect hp hY
  obtain ⟨-, -, hsn, -, -⟩ := hY.2
  have hYK' : (Y.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) = K := by
    rw [hYY]
    exact hYK
  let eS := Subgroup.subgroupOfEquivOfLe hYH
  have hmap := CFSG.pPrimeCore_map_iso 3 eS
  let e₁ : (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) ≃* ↥K :=
    ((QuotientGroup.congr (CFSG.pPrimeCore 3 ↥(Y.subgroupOf H)) (CFSG.pPrimeCore 3 ↥Y) eS
      hmap).symm.trans
      (CFSG.ComponentClassification.CatalogueBHeldSmallCore.subnormalCoreQuotientEquivImage 3
        (Y.subgroupOf H) hsn)).trans (MulEquiv.subgroupCongr hYK')
  obtain ⟨e₀⟩ := nonempty_quot_pPrimeCore_quot_mulEquiv (Y := ↥Y) hp hp2
  have hLY : IsLinThreeFour ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸
      CFSG.pPrimeCore 3 (↥Y ⧸ CFSG.pCore 2 ↥Y)) := by
    obtain ⟨d, hd, ⟨f⟩⟩ := hKL
    exact ⟨d, hd, ⟨(e₀.trans e₁).trans f⟩⟩
  have hZ : center ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ CFSG.pPrimeCore 3 (↥Y ⧸ CFSG.pCore 2 ↥Y)) = ⊥ :=
    Hyp111.center_eq_bot_of_isLinThreeFour hLY
  have h2 : CFSG.pCore 2 (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥ := pCore_two_quot_eq_bot (Y := ↥Y)
  by_cases hc : CFSG.pPrimeCore 3 (↥Y ⧸ CFSG.pCore 2 ↥Y) ≤ center (↥Y ⧸ CFSG.pCore 2 ↥Y)
  ·
    have hYc := NineTwelveCfg.isTwoPrimeComponentIn_of_le_center' hp hp2 hY hc
    have hperf : ⁅Y, Y⁆ = Y := Subgroup.isPerfect_iff.1 (IsPComponentIn.isPerfect hp hY)
    refine ⟨Y, CFSG.RankThree.PartTwo.Sec18.mem_oTwoComponentsIn_of_quasisimple hYH hYc.2.1
      hperf hYc.2.2.1, ?_⟩
    have hZle : center (↥Y ⧸ CFSG.pCore 2 ↥Y) ≤ CFSG.pPrimeCore 3 (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
      intro z hz
      have hz' : QuotientGroup.mk' (CFSG.pPrimeCore 3 (↥Y ⧸ CFSG.pCore 2 ↥Y)) z ∈
          center ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ CFSG.pPrimeCore 3 (↥Y ⧸ CFSG.pCore 2 ↥Y)) := by
        rw [Subgroup.mem_center_iff]
        intro w
        obtain ⟨w', rfl⟩ := QuotientGroup.mk'_surjective _ w
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) w']
      rw [hZ, Subgroup.mem_bot] at hz'
      exact (QuotientGroup.eq_one_iff z).mp hz'
    have hZeq : center (↥Y ⧸ CFSG.pCore 2 ↥Y) = CFSG.pPrimeCore 3 (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
      le_antisymm hZle hc
    obtain ⟨eL⟩ := KFactProofs.UPrimeExcL34.nonempty_equiv_projSL hLY
    have hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 (↥Y ⧸ CFSG.pCore 2 ↥Y)) :=
      (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
    have h2grp : IsPGroup 2 (CFSG.pPrimeCore 3 (↥Y ⧸ CFSG.pCore 2 ↥Y)) :=
      CFSG.RankThree.PartTwo.KFacts.l34CenterThreePrimeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y) hYc.2.2.1
        ⟨(QuotientGroup.quotientMulEquivOfEq hZeq).trans eL⟩ _ hc hcop
    have hbot : CFSG.pPrimeCore 3 (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥ := by
      rw [eq_bot_iff, ← h2]
      exact le_sSup ⟨CFSG.pPrimeCore_normal, h2grp⟩
    obtain ⟨d, hd, ⟨f⟩⟩ := hLY
    exact ⟨d, hd, ⟨(QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hbot.symm)).trans f⟩⟩
  exfalso
  have hgen : closure {y : ↥Y ⧸ CFSG.pCore 2 ↥Y | ∃ n : ℕ, orderOf y = 3 ^ n} = ⊤ :=
    closure_pElem_quot_eq_top (Y := ↥Y) hp (CFSG.pCore 2 ↥Y)
      (IsPComponentIn.closure_pElem_eq_top hp hY)
  have hq : CFSG.IsQuasisimple ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸
      CFSG.pPrimeCore 3 (↥Y ⧸ CFSG.pCore 2 ↥Y)) :=
    CFSG.IsQuasisimple.of_mulEquiv e₀ (IsPComponentIn.isQuasisimple_quot hp hY)
  have hrk : ∀ r : ℕ, r.Prime → r ≠ 2 →
      CFSG.Open.pRank r (CFSG.pPrimeCore 3 (↥Y ⧸ CFSG.pCore 2 ↥Y)) ≤ 3 := by
    intro r hr hr2
    refine (pRank_pPrimeCore_quot_le (Y := ↥Y) hp hp2 hr hr2).trans ?_
    have h1 : CFSG.Open.pRank r (CFSG.pPrimeCore 3 ↥Y) ≤
        CFSG.Open.pRank r ((CFSG.pPrimeCore 3 ↥Y).map Y.subtype) :=
      CFSG.SectionRank.pRank_le_map hr.one_lt Y.subtype Y.subtype_injective _
    have h2' : CFSG.Open.pRank r ((CFSG.pPrimeCore 3 ↥Y).map Y.subtype) ≤ CFSG.Open.pRank r H :=
      CFSG.SectionRank.pRank_mono hr.one_lt ((Subgroup.map_subtype_le _).trans hYH)
    have h3 := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank r hr hr2 H hH.1
    rw [hS.rank] at h3
    omega
  have hK : CFSG.Open.IsKGroup (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    ((hS.kProper.isKGroup H hHtop).of_le hYH).quotient (CFSG.pCore 2 ↥Y)
  have hE : CFSG.layer ↥(CFSG.pPrimeCore 3 (↥Y ⧸ CFSG.pCore 2 ↥Y)) = ⊥ :=
    layer_pPrimeCore_eq_bot (Y := ↥Y ⧸ CFSG.pCore 2 ↥Y) hp hgen hK hSch hrk
  obtain ⟨q, hq', hq2, hq3, V, hV, hrank, A, φ, hφ⟩ :=
    exists_mulAut_surjective_of_not_le_center (Y := ↥Y ⧸ CFSG.pCore 2 ↥Y)
      hp hgen h2 hq hE hrk hc
  let e₂ := (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact hL34 q hq' hq2 hq3 ↥V hV hrank A _ hLY (e₂.toMonoidHom.comp φ)
    (e₂.surjective.comp hφ)

end CFSG.LocalAnalysis.RankThreeTheoremC
