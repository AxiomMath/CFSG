module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineTwelveOneCfgOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeListOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightBridge
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneComp
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneSection
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneLayer
import CFSG.Quasithin.Vol2.Ch3Sec3Comp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenEight

variable {G : Type} [Group G] [Finite G]

section Common

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open Subgroup

theorem not_map_le_d1X0 {p : ℕ} {M N Y : Subgroup G}
    (hcore : (primeComplementCore (G := N) p).map N.subtype ≤ M) (hYN : Y ≤ N)
    (hYM : ¬ Y ≤ M) :
    ¬ (Y.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) ≤
      d1X0 p M N := by
  set π := QuotientGroup.mk' (primeComplementCore (G := N) p) with hπ
  intro hle
  apply hYM
  intro z hz
  obtain ⟨⟨m, hmN⟩, hm, hmz⟩ := hle ⟨⟨z, hYN hz⟩, hz, rfl⟩
  have ho : (⟨m, hmN⟩ : N)⁻¹ * ⟨z, hYN hz⟩ ∈ primeComplementCore (G := N) p := by
    rw [← QuotientGroup.eq_one_iff]
    show π ((⟨m, hmN⟩ : N)⁻¹ * ⟨z, hYN hz⟩) = 1
    rw [map_mul, map_inv, hmz, inv_mul_cancel]
  have hoM : ((⟨m, hmN⟩ : N)⁻¹ * ⟨z, hYN hz⟩ : N).1 ∈ M := hcore ⟨_, ho, rfl⟩
  have e : z = m * ((⟨m, hmN⟩ : N)⁻¹ * ⟨z, hYN hz⟩ : N).1 := by simp
  rw [e]
  exact M.mul_mem (Subgroup.mem_subgroupOf.mp hm).2 hoM

end Common

section NineTwelve

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open Subgroup

theorem isTwoPrimeComponentIn_of_escape (h31 : KFactThreeOne) (h75 : KFactSevenFive)
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (hsec : KFactNineThreeAutSection) (hS : Setting G) {p : ℕ} {P : Sylow p G}
    {M H₁ R₁ : Subgroup G} (he : D1Escape p P M H₁ R₁) {B N : Subgroup G}
    (hB : IsAGLQ p M B) (hBN : B ≤ N) (hN : GLBIsMaxTwoLocal N) (hp3 : p ≠ 3)
    {Y : Subgroup G} (hY : RankThreeUC.AGL81C.IsPComponentIn p Y N) (hYM : ¬ Y ≤ M) :
    RankThreeUC.AGL81C.IsTwoPrimeComponentIn Y N := by
  have hp : p.Prime := he.prime
  have hp2 : p ≠ 2 := he.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hYN : Y ≤ N := hY.1
  haveI : Group.IsPerfect ↥Y := IsPComponentIn.isPerfect hp hY
  by_cases hc : CFSG.pPrimeCore p (↥Y ⧸ CFSG.pCore 2 ↥Y) ≤ center (↥Y ⧸ CFSG.pCore 2 ↥Y)
  · exact NineTwelveCfg.isTwoPrimeComponentIn_of_le_center' hp hp2 hY hc
  exfalso
  haveI := hS.simple
  have hNtop : N ≠ ⊤ :=
    CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hS.nonab hN.1
  have hcore : (primeComplementCore (G := N) p).map N.subtype ≤ M :=
    core_le_of_base (muAt_of_escape he) hB hBN
  set π := QuotientGroup.mk' (primeComplementCore (G := N) p) with hπ
  obtain ⟨K', hKc, hsn, hYK, -⟩ := hY.2
  have hYK' : (Y.subgroupOf N).map π = K' := hYK
  have hK'c : IsComponentOf K' ⊤ := isComponentOf_top_of_isComponent' hKc
  have hK'X : ¬ K' ≤ d1X0 p M N := by
    rw [← hYK']
    exact not_map_le_d1X0 hcore hYN hYM
  obtain ⟨i, hi, ⟨eK⟩⟩ := exists_nineThreeIndex_of_component h31 h75 hS hS.kProper he hB hBN
    hNtop hK'c hK'X
  have hZK : Subgroup.center K' = ⊥ :=
    (exists_threeOneIndex_of_component h31 hS.kProper he hB hBN hNtop hK'c hK'X).2
  let eS := Subgroup.subgroupOfEquivOfLe hYN
  have hmap := CFSG.pPrimeCore_map_iso p eS
  let e₁ : (↥Y ⧸ CFSG.pPrimeCore p ↥Y) ≃* ↥K' :=
    ((QuotientGroup.congr (CFSG.pPrimeCore p ↥(Y.subgroupOf N)) (CFSG.pPrimeCore p ↥Y) eS
      hmap).symm.trans
      (CFSG.ComponentClassification.CatalogueBHeldSmallCore.subnormalCoreQuotientEquivImage p
        (Y.subgroupOf N) hsn)).trans (MulEquiv.subgroupCongr hYK)
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
    have h2' : CFSG.Open.pRank r ((CFSG.pPrimeCore p ↥Y).map Y.subtype) ≤ CFSG.Open.pRank r N :=
      CFSG.SectionRank.pRank_mono hr.one_lt ((Subgroup.map_subtype_le _).trans hYN)
    have h3 := local_pRank_le_evenRank r hr hr2 N hN.1
    rw [hS.rank] at h3
    omega
  have hK : CFSG.Open.IsKGroup (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    ((hS.kProper.isKGroup N hNtop).of_le hYN).quotient (CFSG.pCore 2 ↥Y)
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

end NineTwelve

section Commutator

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers
open Subgroup
open scoped commutatorElement
open CFSG.LocalAnalysis.RankThreeTheoremC.TenFiveX

theorem commutator_mem_primeComplementCore {p : ℕ} {M N : Subgroup G}
    (hcore : (primeComplementCore (G := N) p).map N.subtype ≤ M) {x : G}
    (hx : x ∈ d1PlusCore p N (d1KBar p M N)) (hxN : x ∈ N) {Y : Subgroup G}
    (hY : RankThreeUC.AGL81C.IsPComponentIn p Y N) (hYM : ¬ Y ≤ M) {y : G} (hy : y ∈ Y)
    (hyN : y ∈ N) :
    ((⟨y, hyN⟩ : N) * ⟨x, hxN⟩ * (⟨y, hyN⟩ : N)⁻¹ * (⟨x, hxN⟩ : N)⁻¹ : N) ∈
      primeComplementCore (G := N) p := by
  set π := QuotientGroup.mk' (primeComplementCore (G := N) p) with hπ
  have hyK : π ⟨y, hyN⟩ ∈ d1KBar p M N := by
    obtain ⟨K', hKc, -, hYK, -⟩ := hY.2
    have hYK' : (Y.subgroupOf N).map π = K' := hYK
    have hK' : IsComponentOf ((Y.subgroupOf N).map π) ⊤ := by
      rw [hYK']
      exact isComponentOf_top_of_isComponent' hKc
    exact le_d1KBar hK' (not_map_le_d1X0 hcore hY.1 hYM) ⟨⟨y, hyN⟩, hy, rfl⟩
  have hxC : π ⟨x, hxN⟩ ∈ Subgroup.centralizer (d1KBar p M N : Set _) := by
    obtain ⟨x', hx', hxx⟩ := Subgroup.mem_map.mp hx
    have : x' = ⟨x, hxN⟩ := Subtype.ext hxx
    rw [← this]
    exact hx'
  have hc : π ⟨y, hyN⟩ * π ⟨x, hxN⟩ = π ⟨x, hxN⟩ * π ⟨y, hyN⟩ :=
    (Subgroup.mem_centralizer_iff.mp hxC _ hyK)
  rw [← QuotientGroup.eq_one_iff]
  show π _ = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
  group

theorem commutator_mem_pCoreOf_of_twoPrime {p : ℕ} (hp : p.Prime) {M N : Subgroup G}
    (hcore : (primeComplementCore (G := N) p).map N.subtype ≤ M)
    {Y : Subgroup G} (hY : RankThreeUC.AGL81C.IsPComponentIn p Y N) (hYM : ¬ Y ≤ M)
    (hYc : RankThreeUC.AGL81C.IsTwoPrimeComponentIn Y N) {x : G}
    (hx : x ∈ d1PlusCore p N (d1KBar p M N)) {y : G} (hy : y ∈ Y) :
    y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 N := by
  have hxN : x ∈ N := by
    obtain ⟨x', -, rfl⟩ := Subgroup.mem_map.mp hx
    exact x'.2
  have hYN : Y ≤ N := hY.1
  have hyN : y ∈ N := hYN hy
  set π₂ := QuotientGroup.mk' (CFSG.pCore 2 ↥N) with hπ₂
  set N₀ := primeComplementCore (G := N) p with hN₀
  set Nh := N₀.map π₂ with hNhdef
  haveI hNh : Nh.Normal := Subgroup.Normal.map inferInstance π₂ (QuotientGroup.mk'_surjective _)
  have hperf : ⁅Y, Y⁆ = Y := Subgroup.isPerfect_iff.1 (hY.isPerfect hp)
  have hsubY : IsSubnormal Y N := (IsSubnormal.iff_subgroupOf hYN).2 hYc.2.1
  have hq : Open.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    ⟨hYc.2.2.1.1.commutator_eq_top, hYc.2.2.1.2.1⟩
  have hNH : N₀.map N.subtype ≤ N := Subgroup.map_subtype_le _
  have hHN : N ≤ Subgroup.normalizer ((N₀.map N.subtype : Subgroup G) : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨n, hn, rfl⟩
      refine ⟨⟨h, hh⟩ * n * (⟨h, hh⟩ : N)⁻¹, ?_, rfl⟩
      exact (inferInstance : N₀.Normal).conj_mem n hn _
    · rintro ⟨n, hn, hng⟩
      refine ⟨(⟨h, hh⟩ : N)⁻¹ * n * ⟨h, hh⟩, ?_, ?_⟩
      · have := (inferInstance : N₀.Normal).conj_mem n hn (⟨h, hh⟩ : N)⁻¹
        simpa using this
      · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hng ⊢
        rw [hng]
        group
  rcases CFSG.Quasithin.H13.Ch3Sec3.le_or_commutator_le_pCoreOf hsubY hperf hq hNH hHN with
    hle | hcomm
  · exfalso
    obtain ⟨K', hKc, -, hYK, -⟩ := hY.2
    have hbot : (Y.subgroupOf N).map (QuotientGroup.mk' N₀) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      intro w hw
      obtain ⟨n, hn, hnw⟩ := hle hw
      have : n = w := Subtype.ext hnw
      rwa [← this]
    have hK'bot : K' = ⊥ :=
      (hYK : (Y.subgroupOf N).map (QuotientGroup.mk' N₀) = K').symm.trans hbot
    obtain ⟨-, hs, -⟩ := hKc.1
    subst hK'bot
    obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
    apply hab
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    congr 1
    exact Subtype.ext ((Subgroup.mem_bot.mp a'.2).trans (Subgroup.mem_bot.mp b'.2).symm)
  · have hstep1 : ∀ g ∈ Y, ∀ (hgN : g ∈ N), ∀ n ∈ N₀, Commute (π₂ ⟨g, hgN⟩) (π₂ n) := by
      intro g hg hgN n hn
      exact commute_of_mem_pCoreOf n.2 hgN
        (hcomm (Subgroup.commutator_mem_commutator hg ⟨n, hn, rfl⟩))
    have hF2 : ∀ g (hg : g ∈ Y) (hgN : g ∈ N),
        π₂ ⟨g, hgN⟩ * π₂ ⟨x, hxN⟩ * (π₂ ⟨g, hgN⟩)⁻¹ * (π₂ ⟨x, hxN⟩)⁻¹ ∈ Nh := by
      intro g hg hgN
      refine ⟨_, commutator_mem_primeComplementCore hcore hx hxN hY hYM hg hgN, ?_⟩
      simp only [map_inv, map_mul]
    have hC : ⁅Y, Y⁆ ≤ ((Subgroup.centralizer {π₂ ⟨x, hxN⟩}).comap π₂).map N.subtype := by
      rw [Subgroup.commutator_le]
      intro a ha' b hb'
      have haN := hYN ha'
      have hbN := hYN hb'
      refine ⟨⟨a, haN⟩ * ⟨b, hbN⟩ * (⟨a, haN⟩ : N)⁻¹ * (⟨b, hbN⟩ : N)⁻¹, ?_, rfl⟩
      have haNh : ∀ n' ∈ Nh, Commute (π₂ ⟨a, haN⟩) n' := by
        rintro _ ⟨n, hn, rfl⟩
        exact hstep1 a ha' haN n hn
      have hbNh : ∀ n' ∈ Nh, Commute (π₂ ⟨b, hbN⟩) n' := by
        rintro _ ⟨n, hn, rfl⟩
        exact hstep1 b hb' hbN n hn
      have key := commute_commutatorElement haNh hbNh (hF2 a ha' haN) (hF2 b hb' hbN)
      show π₂ _ ∈ Subgroup.centralizer _
      rw [Subgroup.mem_centralizer_singleton_iff, map_mul, map_mul, map_mul, map_inv, map_inv]
      rw [commutatorElement_def] at key
      exact key.eq
    rw [hperf] at hC
    obtain ⟨y', hy', hyy⟩ := hC hy
    have : y' = ⟨y, hyN⟩ := Subtype.ext hyy
    rw [this] at hy'
    apply mem_pCoreOf_of_commute hxN hyN
    exact Subgroup.mem_centralizer_singleton_iff.mp hy'

end Commutator

end CFSG.LocalAnalysis.RankThreeTheoremC.TenEight
