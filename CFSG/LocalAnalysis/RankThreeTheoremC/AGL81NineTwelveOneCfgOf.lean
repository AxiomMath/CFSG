module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenFiveXOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeKFacts
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeListOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightBridge
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneComp
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneSection
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneLayer
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.Generic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open Subgroup

@[expose] def KFactNineThreeAutSection : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → p ≠ 3 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ i : TauCeti.CFSGIndex, IsNineThreeIndex p i →
    ∀ (V : Type) [Group V] [Finite V], IsPGroup q V → Open.pRank q (⊤ : Subgroup V) ≤ 3 →
    ∀ (A : Subgroup (MulAut V)) (φ : ↥A →* i.Group), ¬ Function.Surjective φ

variable {G : Type} [Group G] [Finite G]

namespace NineTwelveCfg

theorem isTwoPrimeComponentIn_of_le_center' {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H Y : Subgroup G} (hY : IsPComponentIn p Y H)
    (hc : CFSG.pPrimeCore p (↥Y ⧸ CFSG.pCore 2 ↥Y) ≤ center (↥Y ⧸ CFSG.pCore 2 ↥Y)) :
    IsTwoPrimeComponentIn Y H := by
  have hYH : Y ≤ H := hY.1
  have hsn : (Y.subgroupOf H).IsSubnormal := by
    obtain ⟨_, _, h, _, _⟩ := hY.2
    exact h
  haveI : Group.IsPerfect ↥Y := IsPComponentIn.isPerfect hp hY
  refine ⟨hYH, hsn, ?_, ?_⟩
  · let P : Type := ↥Y ⧸ CFSG.pCore 2 ↥Y
    have hPperf : Group.IsPerfect P := inferInstance
    have hq : CFSG.IsQuasisimple (P ⧸ CFSG.pPrimeCore p P) := by
      obtain ⟨e⟩ := nonempty_quot_pPrimeCore_quot_mulEquiv (Y := ↥Y) hp hp2
      exact CFSG.IsQuasisimple.of_mulEquiv e (IsPComponentIn.isQuasisimple_quot hp hY)
    have hker : (QuotientGroup.mk' (CFSG.pPrimeCore p P)).ker ≤ center P := by
      rw [QuotientGroup.ker_mk']
      exact hc
    exact (CFSG.LocalCores.isQuasisimple_iff_of_surjective hPperf (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) hker).mpr hq
  · have hperf : ⁅Y, Y⁆ = Y := Subgroup.isPerfect_iff.1 (IsPComponentIn.isPerfect hp hY)
    exact le_antisymm
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.closure_odd_of_perfect hperf)
      ((Subgroup.closure_le _).mpr fun x hx => hx.1)

end NineTwelveCfg

open NineTwelveCfg

theorem agl81NineTwelveOneCfg_of (h31 : KFactThreeOne) (h75 : KFactSevenFive)
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (hsec : KFactNineThreeAutSection) : AGL81NineTwelveOneCfg G := by
  intro hS p P M H Q K hd hp3 Y hY hYM
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  have hp : p.Prime := he.prime
  have hp2 : p ≠ 2 := he.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hYH : Y ≤ H := hY.1
  haveI : Group.IsPerfect ↥Y := IsPComponentIn.isPerfect hp hY
  by_cases hc : CFSG.pPrimeCore p (↥Y ⧸ CFSG.pCore 2 ↥Y) ≤ center (↥Y ⧸ CFSG.pCore 2 ↥Y)
  · exact isTwoPrimeComponentIn_of_le_center' hp hp2 hY hc
  exfalso
  haveI := hS.simple
  have hHtop : H ≠ ⊤ :=
    CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hS.nonab hd.maxH.1
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  obtain ⟨K', hKc, hsn, hYK, -⟩ := hY.2
  have hYK' : (Y.subgroupOf H).map π = K' := hYK
  have hK'c : IsComponentOf K' ⊤ := isComponentOf_top_of_isComponent' hKc
  have hK'X : ¬ K' ≤ d1X0 p M H := by
    intro hle
    apply hYM
    intro z hz
    rw [← hYK'] at hle
    obtain ⟨⟨m, hmH⟩, hm, hmz⟩ := hle ⟨⟨z, hYH hz⟩, hz, rfl⟩
    have ho : (⟨m, hmH⟩ : H)⁻¹ * ⟨z, hYH hz⟩ ∈ primeComplementCore (G := H) p := by
      rw [← QuotientGroup.eq_one_iff]
      show π ((⟨m, hmH⟩ : H)⁻¹ * ⟨z, hYH hz⟩) = 1
      rw [map_mul, map_inv, hmz, inv_mul_cancel]
    have hoM : ((⟨m, hmH⟩ : H)⁻¹ * ⟨z, hYH hz⟩ : H).1 ∈ M := hd.primeCore_le ⟨_, ho, rfl⟩
    have e : z = m * ((⟨m, hmH⟩ : H)⁻¹ * ⟨z, hYH hz⟩ : H).1 := by simp
    rw [e]
    exact M.mul_mem (Subgroup.mem_subgroupOf.mp hm).2 hoM
  obtain ⟨i, hi, ⟨eK⟩⟩ := exists_nineThreeIndex_of_component h31 h75 hS hS.kProper he hd.base
    hd.le_H hHtop hK'c hK'X
  have hZK : Subgroup.center K' = ⊥ :=
    (exists_threeOneIndex_of_component h31 hS.kProper he hd.base hd.le_H hHtop hK'c hK'X).2
  let eS := Subgroup.subgroupOfEquivOfLe hYH
  have hmap := CFSG.pPrimeCore_map_iso p eS
  let e₁ : (↥Y ⧸ CFSG.pPrimeCore p ↥Y) ≃* ↥K' :=
    ((QuotientGroup.congr (CFSG.pPrimeCore p ↥(Y.subgroupOf H)) (CFSG.pPrimeCore p ↥Y) eS
      hmap).symm.trans
      (CFSG.ComponentClassification.CatalogueBHeldSmallCore.subnormalCoreQuotientEquivImage p
        (Y.subgroupOf H) hsn)).trans (MulEquiv.subgroupCongr hYK)
  have hZY : Subgroup.center (↥Y ⧸ CFSG.pPrimeCore p ↥Y) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have : e₁ z ∈ Subgroup.center K' := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨w', rfl⟩ := e₁.surjective w
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) w']
    rw [hZK, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (e₁.map_eq_one_iff.mp this)
  have hgen : closure {y : ↥Y ⧸ CFSG.pCore 2 ↥Y | ∃ n : ℕ, orderOf y = p ^ n} = ⊤ :=
    closure_pElem_quot_eq_top (Y := ↥Y) hp (CFSG.pCore 2 ↥Y)
      (IsPComponentIn.closure_pElem_eq_top hp hY)
  have h2 : CFSG.pCore 2 (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥ := pCore_two_quot_eq_bot (Y := ↥Y)
  obtain ⟨e₀⟩ := nonempty_quot_pPrimeCore_quot_mulEquiv (Y := ↥Y) hp hp2
  have hq : CFSG.IsQuasisimple ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸
      CFSG.pPrimeCore p (↥Y ⧸ CFSG.pCore 2 ↥Y)) :=
    CFSG.IsQuasisimple.of_mulEquiv e₀ (IsPComponentIn.isQuasisimple_quot hp hY)
  have hrk : ∀ r : ℕ, r.Prime → r ≠ 2 →
      CFSG.Open.pRank r (CFSG.pPrimeCore p (↥Y ⧸ CFSG.pCore 2 ↥Y)) ≤ 3 := by
    intro r hr hr2
    refine (pRank_pPrimeCore_quot_le (Y := ↥Y) hp hp2 hr hr2).trans ?_
    have h1 : CFSG.Open.pRank r (CFSG.pPrimeCore p ↥Y) ≤
        CFSG.Open.pRank r ((CFSG.pPrimeCore p ↥Y).map Y.subtype) :=
      CFSG.SectionRank.pRank_le_map hr.one_lt Y.subtype Y.subtype_injective _
    have h2' : CFSG.Open.pRank r ((CFSG.pPrimeCore p ↥Y).map Y.subtype) ≤ CFSG.Open.pRank r H :=
      CFSG.SectionRank.pRank_mono hr.one_lt ((Subgroup.map_subtype_le _).trans hYH)
    have h3 := local_pRank_le_evenRank r hr hr2 H hd.maxH.1
    rw [hS.rank] at h3
    omega
  have hK : CFSG.Open.IsKGroup (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    ((hS.kProper.isKGroup H hHtop).of_le hYH).quotient (CFSG.pCore 2 ↥Y)
  have hE : CFSG.layer ↥(CFSG.pPrimeCore p (↥Y ⧸ CFSG.pCore 2 ↥Y)) = ⊥ :=
    layer_pPrimeCore_eq_bot (Y := ↥Y ⧸ CFSG.pCore 2 ↥Y) hp hgen hK hSch hrk
  obtain ⟨q, hq', hq2, hqp, V, hV, hrank, A, φ, hφ⟩ :=
    exists_mulAut_surjective_of_not_le_center (Y := ↥Y ⧸ CFSG.pCore 2 ↥Y)
      hp hgen h2 hq hE hrk hc
  obtain ⟨e₂⟩ := nonempty_center_quot_mulEquiv e₀
  let e₃ : ((↥Y ⧸ CFSG.pPrimeCore p ↥Y) ⧸ center (↥Y ⧸ CFSG.pPrimeCore p ↥Y)) ≃* i.Group :=
    ((QuotientGroup.quotientMulEquivOfEq hZY).trans QuotientGroup.quotientBot).trans
      (e₁.trans eK)
  let φ' : ↥A →* i.Group := (e₃.toMonoidHom.comp e₂.toMonoidHom).comp φ
  have hφ' : Function.Surjective φ' := (e₃.surjective.comp e₂.surjective).comp hφ
  exact hsec p q hp hp2 hp3 hq' hq2 hqp i hi ↥V hV hrank A φ' hφ'

end CFSG.LocalAnalysis.RankThreeTheoremC
