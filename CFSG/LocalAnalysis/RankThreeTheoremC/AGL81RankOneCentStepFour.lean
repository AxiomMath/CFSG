module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentStepTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneSylow
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentNormalizer
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentSylow
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneElevenEleven
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111WeakCore
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5MLayer
import CFSG.LocalAnalysis.RankThreeTheoremC.D1Component3
import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.Prop34
import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer
import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.Wreathed.OddKernelSylowQuotient
public import CFSG.ClassicalGroups
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG3
public import CFSG.Goldschmidt.StatementsH
public import CFSG.GroupTheory.QuasiDihedralFusion.InvolutionCentralizer
public import CFSG.GroupTheory.RegularModuleThree
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Parts
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJCompetitor
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaBlock
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMSide
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroLeaves
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenCfgOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeAlt
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeAtProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3ACentralBaseXQ
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3LinTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CentralU
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3InnerNotQRankTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Main
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.G2A5Setting
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.H13.Sp62D3
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch11SecSFacts
public import CFSG.Quasithin.Vol2.Ch11SecSSetup
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
import CFSG.LocalAnalysis.RankFourTheoremC.PPointBorelData
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614PrimeDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerOdd
import Certificates.Kernel.Sporadic.Fi22.C2068
import Certificates.Kernel.Sporadic.Fi22.C3151

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

section Generic

variable {p : ℕ} [Fact p.Prime] {C : Subgroup G}
  {K : Subgroup (C ⧸ primeComplementCore (G := C) p)}

theorem pRank_hyp111Pre :
    Open.pRank p (hyp111Pre p C K) = Open.pRank p (⊤ : Subgroup ↥K) := by
  have hp : p.Prime := Fact.out
  have hcop : p.Coprime (Nat.card (primeComplementCore (G := C) p)) :=
    primeComplementCore_coprime (G := C) p
  have hmap := pRank_map_mk_eq_pRank_map_subtype hp (primeComplementCore (G := C) p) hcop
    (K.comap (QuotientGroup.mk' (primeComplementCore (G := C) p)))
  rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hmap
  have htop := CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) K
  change Open.pRank p K = Open.pRank p (hyp111Pre p C K) at hmap
  omega

theorem pRank_eq_of_isSylowOf {B L : Subgroup G} (h : CFSG.ABGLocalTools.IsSylowOf p B L) :
    Open.pRank p B = Open.pRank p L := by
  obtain ⟨hBL, hB, hidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp h
  exact CFSG.LocalAnalysis.RankThreeTheoremC.pRank_eq_of_sylow Fact.out hBL hB hidx

theorem exists_orderOf_of_one_le_pRank {L : Subgroup G} (h : 1 ≤ Open.pRank p L) :
    ∃ u ∈ L, orderOf u = p := by
  have hp : p.Prime := Fact.out
  obtain ⟨E, hEL, -, hEc⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp L
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥E) p (by
    rw [hEc]
    exact dvd_pow_self p (by omega))
  exact ⟨u, hEL u.2, by rw [← hu, Subgroup.orderOf_coe]⟩

theorem one_le_pRank_d1KBar (hp2 : p ≠ 2) {M : Subgroup G} (hne : d1KBar p M C ≠ ⊥) :
    1 ≤ Open.pRank p (⊤ : Subgroup ↥(d1KBar p M C)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨L, hL, hLX⟩ : ∃ L : Subgroup (C ⧸ primeComplementCore (G := C) p),
      IsComponentOf L ⊤ ∧ ¬ L ≤ d1X0 p M C := by
    by_contra hcon
    push Not at hcon
    apply hne
    exact le_bot_iff.mp (iSup₂_le fun L hL => absurd hL.2 (by simpa using hcon L hL.1))
  obtain ⟨R⟩ : Nonempty (Sylow p (C ⧸ primeComplementCore (G := C) p)) := inferInstance
  obtain ⟨t, ⟨-, htL⟩, htp, -⟩ :=
    exists_mem_sylow_inf_component hp hp2 (primeComplementCore_quotient_eq_bot p) R hL
  have htK : t ∈ d1KBar p M C := le_d1KBar hL hLX htL
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  have htp' : t ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [htp])
  have hE := CFSG.Open.isElemAbelian_zpowers htp'
  exact CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.zpowers_le.mpr htK) hE
    (by rw [Nat.card_zpowers, htp, pow_one])

variable [hK : K.Normal]

local notation "φ" => RankOneSylow.act (primeComplementCore (G := C) p) K

theorem mem_d1PlusCore_iff_mem_ker (x : C) : (x : G) ∈ d1PlusCore p C K ↔ x ∈ MonoidHom.ker φ := by
  rw [RankOneSylow.d1PlusCore_eq]
  exact Subgroup.mem_map_iff_mem C.subtype_injective

theorem le_of_act_mem_normalizer {P : Sylow p G} {M : Subgroup G}
    (hcore : GLBWeakCore p (P : Subgroup G) ≤ M) (hp2 : p ≠ 2)
    (hZ : Subgroup.center ↥K = ⊥) (hK1 : 1 ≤ Open.pRank p (⊤ : Subgroup ↥K))
    (hXM : d1PlusCore p C K ≤ M) (hXr : Open.pRank p (d1PlusCore p C K) ≤ 1)
    {B E : Subgroup G} {b : G} (hBC : CFSG.ABGLocalTools.IsSylowOf p B C) (hBM : B ≤ M)
    (hbB : b ∈ B) (hb : ∀ c ∈ C, b * c = c * b) (hbo : orderOf b = p)
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) (hEB : E ≤ B) {c : C}
    (hc : φ c ∈ Subgroup.normalizer
      ((((B ⊓ hyp111Pre p C K).subgroupOf C).map φ : Subgroup (MulAut ↥K)) : Set (MulAut ↥K))) :
    (c : G) ∈ M := by
  have hp : p.Prime := Fact.out
  set Kp := hyp111Pre p C K with hKp
  set X := d1PlusCore p C K with hX
  set B₁ := B ⊓ Kp with hB₁
  set B₁' : Subgroup (MulAut ↥K) := (B₁.subgroupOf C).map φ with hB₁'
  set D : Subgroup G := (B₁'.comap φ).map C.subtype with hD
  set N : Subgroup G := ((Subgroup.normalizer (B₁' : Set (MulAut ↥K))).comap φ).map C.subtype
    with hN
  have hBC' : B ≤ C := hBC.le
  have hBp : IsPGroup p B := hBC.isPGroup
  have hKpC : Kp ≤ C := Subgroup.map_subtype_le _
  have hDC : D ≤ C := Subgroup.map_subtype_le _
  have hXC : X ≤ C := Subgroup.map_subtype_le _
  have hbC : b ∈ C := hBC' hbB
  have hbX : b ∈ X := mem_d1PlusCore_of_central hbC hb K
  have hbKp : b ∉ Kp := not_mem_hyp111Pre hZ hbX hbo
  have hmemD : ∀ {x : G}, x ∈ D → ∃ u ∈ B₁, u⁻¹ * x ∈ X := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, hu, hux⟩ := (hx : φ x ∈ B₁')
    refine ⟨u, hu, ?_⟩
    have hk : u⁻¹ * x ∈ MonoidHom.ker φ := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hux, inv_mul_cancel]
    have := (mem_d1PlusCore_iff_mem_ker (u⁻¹ * x)).mpr hk
    simpa using this
  have hB₁D : B₁ ≤ D := fun u hu =>
    ⟨⟨u, hBC' hu.1⟩, ⟨⟨u, hBC' hu.1⟩, hu, rfl⟩, rfl⟩
  have hbD : b ∈ D := by
    refine ⟨⟨b, hbC⟩, ?_, rfl⟩
    change φ ⟨b, hbC⟩ ∈ B₁'
    have hk : (⟨b, hbC⟩ : C) ∈ MonoidHom.ker φ := (mem_d1PlusCore_iff_mem_ker ⟨b, hbC⟩).mp hbX
    rw [MonoidHom.mem_ker.mp hk]
    exact B₁'.one_mem
  have hND : N ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.map_mono (Subgroup.le_normalizer_comap φ)).trans (Subgroup.le_normalizer_map _)
  have hDM : D ≤ M := by
    intro x hx
    obtain ⟨u, hu, hux⟩ := hmemD hx
    have : x = u * (u⁻¹ * x) := by group
    rw [this]
    exact M.mul_mem (hBM hu.1) (hXM hux)
  have hBB₁ : B ≤ Subgroup.normalizer (B₁ : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, le_normalizer_hyp111Pre hK (hBC' hg)⟩
  have hBN : B ≤ N := by
    intro g hg
    refine ⟨⟨g, hBC' hg⟩, ?_, rfl⟩
    change φ ⟨g, hBC' hg⟩ ∈ Subgroup.normalizer (B₁' : Set (MulAut ↥K))
    refine Subgroup.le_normalizer_map φ ⟨⟨g, hBC' hg⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp (hBB₁ hg) h
  have hBY : CFSG.ABGLocalTools.IsSylowOf p B (B ⊔ D) := hBC.of_le le_sup_left (sup_le hBC' hDC)
  have hB₂ : CFSG.ABGLocalTools.IsSylowOf p (B ⊓ D) D :=
    hBY.inf_of_le_normalizer le_sup_right (sup_le (hBN.trans hND) Subgroup.le_normalizer)
  have hB₂M : B ⊓ D ≤ M := inf_le_left.trans hBM
  have hB₂p : IsPGroup p ↥(B ⊓ D : Subgroup G) := hBp.to_le inf_le_left
  have hB₁syl : CFSG.ABGLocalTools.IsSylowOf p B₁ Kp :=
    hBC.inf_of_le_normalizer hKpC (le_normalizer_hyp111Pre hK)
  have hrB₁ : Open.pRank p B₁ = Open.pRank p (⊤ : Subgroup ↥K) :=
    (pRank_eq_of_isSylowOf hB₁syl).trans pRank_hyp111Pre
  have hNB₂ : Subgroup.normalizer ((B ⊓ D : Subgroup G) : Set G) ≤ M := by
    by_cases h2 : 2 ≤ Open.pRank p (⊤ : Subgroup ↥K)
    ·
      have h := CFSG.LocalAnalysis.RankThreeTheoremC.pRank_inf_succ_le_of_central hp
        (R := B ⊓ D) ⟨hbB, hbD⟩ hbo hbKp
        (Subgroup.mem_centralizer_iff.mpr fun k hk => (hb k (hKpC hk)).symm)
      have hle : B₁ ≤ (B ⊓ D) ⊓ Kp := le_inf (le_inf inf_le_left hB₁D) inf_le_right
      have := CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hle
      exact normalizer_le_of_three hcore hB₂M hB₂p (by omega)
    ·
      have hB₁p : IsPGroup p ↥B₁ := hBp.to_le inf_le_left
      have hB₁c : IsCyclic B₁ := RankOne.isCyclic_of_le_of_pRank_le_one (X := B₁) hp2 le_rfl hB₁p
        (by rw [hrB₁]; omega)
      obtain ⟨u₀, hu₀, hu₀o⟩ := exists_orderOf_of_one_le_pRank (L := B₁) (by rw [hrB₁]; exact hK1)
      have hu₀C : u₀ ∈ C := hBC' hu₀.1
      have hbu₀ : b ∉ Subgroup.zpowers u₀ := fun h =>
        hbKp ((Subgroup.zpowers_le.mpr hu₀.2) h)
      obtain ⟨hD₀e, hD₀c⟩ := RankOne.elemAbelian_pair hp hu₀o hbo hbu₀ (hb u₀ hu₀C).symm
      set D₀ := Subgroup.zpowers u₀ ⊔ Subgroup.zpowers b with hD₀
      have hkey : ∀ x ∈ B ⊓ D, x ^ p = 1 → x ∈ D₀ := by
        rintro x ⟨hxB, hxD⟩ hxp
        obtain ⟨u, hu, hux⟩ := hmemD hxD
        set v := u⁻¹ * x with hv
        have hvB : v ∈ B := B.mul_mem (B.inv_mem hu.1) hxB
        have hxuv : x = u * v := by rw [hv]; group
        have huv : u * v = v * u := commute_of_mem_inf hK hZ hBC' hBp hu.1 hvB hu.2 hux
        have hpow : u ^ p * v ^ p = 1 := by
          rw [← (Commute.mul_pow huv p), ← hxuv, hxp]
        have hupX : u ^ p ∈ X := by
          have : u ^ p = (v⁻¹) ^ p := by
            rw [inv_pow, eq_inv_iff_mul_eq_one, hpow]
          rw [this]
          exact X.pow_mem (X.inv_mem hux) p
        obtain ⟨n, hn⟩ := hBp ⟨u ^ p, B.pow_mem hu.1 p⟩
        have hup : u ^ p = 1 :=
          eq_one_of_mem_inf hZ (Kp.pow_mem hu.2 p) hupX (n := n)
            (by simpa using congrArg Subtype.val hn)
        have hvp : v ^ p = 1 := by rw [hup, one_mul] at hpow; exact hpow
        have huD : u ∈ Subgroup.zpowers u₀ := by
          by_cases hu1 : u = 1
          · rw [hu1]; exact Subgroup.one_mem _
          · have huo : orderOf u = p := orderOf_eq_prime hup hu1
            rw [← CFSG.LocalAnalysis.RankThreeTheoremC.zpowers_eq_of_orderOf_eq_of_isCyclic hB₁c
              hu hu₀ (huo.trans hu₀o.symm)]
            exact Subgroup.mem_zpowers u
        have hvD : v ∈ Subgroup.zpowers b := by
          by_cases hv1 : v = 1
          · rw [hv1]; exact Subgroup.one_mem _
          · exact mem_zpowers_of_pRank_le_one hp hXr hbX hbo (fun y hy => hb y (hXC hy)) hux
              (orderOf_eq_prime hvp hv1)
        rw [hxuv]
        exact D₀.mul_mem (Subgroup.mem_sup_left huD) (Subgroup.mem_sup_right hvD)
      have hD₀B₂ : D₀ ≤ B ⊓ D := sup_le
        (Subgroup.zpowers_le.mpr ⟨hu₀.1, hB₁D hu₀⟩) (Subgroup.zpowers_le.mpr ⟨hbB, hbD⟩)
      have hD₀exp : ∀ d ∈ D₀, d ^ p = 1 := hD₀e.2
      have hND₀ : Subgroup.normalizer ((B ⊓ D : Subgroup G) : Set G) ≤
          Subgroup.normalizer (D₀ : Set G) := by
        intro g hg
        rw [Subgroup.mem_normalizer_iff] at hg ⊢
        intro h
        constructor
        · intro hh
          refine hkey _ ((hg h).mp (hD₀B₂ hh)) ?_
          rw [conj_pow, hD₀exp h hh, mul_one, mul_inv_cancel]
        · intro hh
          have hhB : h ∈ B ⊓ D := (hg h).mpr (hD₀B₂ hh)
          refine hkey h hhB ?_
          have h1 : (g * h * g⁻¹) ^ p = 1 := hD₀exp _ hh
          rw [conj_pow, mul_inv_eq_one, mul_eq_left] at h1
          exact h1
      have hlt : Nat.card D₀ < Nat.card E := by
        rw [hD₀c, hEc]
        exact Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      obtain ⟨z, hzE, hzD₀⟩ : ∃ z ∈ E, z ∉ D₀ := by
        by_contra hcon
        push Not at hcon
        exact absurd (Subgroup.card_le_of_le hcon) (not_le.mpr hlt)
      have hzB : z ∈ B := hEB hzE
      have hz1 : z ≠ 1 := fun h => hzD₀ (h ▸ D₀.one_mem)
      have hzo : orderOf z = p := orderOf_eq_prime (hE.2 z hzE) hz1
      have hzu₀ : z * u₀ = u₀ * z := by
        have hmem : z * u₀ * z⁻¹ ∈ B₁ := (Subgroup.mem_normalizer_iff.mp (hBB₁ hzB) u₀).mp hu₀
        have hord : orderOf (z * u₀ * z⁻¹) = p := by
          have := orderOf_injective (MulAut.conj z).toMonoidHom (MulAut.conj z).injective u₀
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
          rw [this, hu₀o]
        have hzp : z * u₀ * z⁻¹ ∈ Subgroup.zpowers u₀ := by
          rw [← CFSG.LocalAnalysis.RankThreeTheoremC.zpowers_eq_of_orderOf_eq_of_isCyclic hB₁c
            hmem hu₀ (hord.trans hu₀o.symm)]
          exact Subgroup.mem_zpowers _
        exact CFSG.LocalAnalysis.RankFourTheoremC.PPointP.commute_of_normalizes_zpowers hu₀o
          ⟨1, by rw [pow_one, ← hzo, pow_orderOf_eq_one]⟩ hzp
      have hzc : ∀ d ∈ D₀, z * d = d * z := by
        have hle : D₀ ≤ Subgroup.centralizer ({z} : Set G) := by
          refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
          · rw [Subgroup.mem_centralizer_singleton_iff]
            exact hzu₀.symm
          · rw [Subgroup.mem_centralizer_singleton_iff]
            exact hb z (hBC' hzB)
        intro d hd
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hd)).symm
      have h2D₀ : 2 ≤ Open.pRank p D₀ := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hD₀e hD₀c
      exact hND₀.trans (normalizer_le_of_central hcore (hD₀B₂.trans hB₂M)
        (hB₂p.to_le hD₀B₂) h2D₀ (hBM hzB) hzo hzD₀ hzc)
  have hNM := le_of_le_normalizer_of_isSylowOf hND hDM hB₂ hNB₂
  exact hNM ⟨c, hc, rfl⟩

end Generic

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
