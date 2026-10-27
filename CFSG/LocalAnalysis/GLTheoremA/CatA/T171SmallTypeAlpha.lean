module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynTri
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171U42Red
public import CFSG.LocalAnalysis.GLTheoremA.S8.I1425ON
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bA6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09U33
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcLabel
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.GLTheoremA.S9.Basic
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Big
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LComp
public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Quasi
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.Fischer.Classification.Recognition.Basic
public import CFSG.GroupTheory.PLayer.Transport
public import CFSG.Adapters.StatedPSLTwoNine
public import CFSG.GH74.KGroups.U33
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Quasithin.H13.A5RowsOut
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Final
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeAFinal
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24LeafShape
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3All
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26AutMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Easy
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporAll
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporCheck
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporCo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporFi23
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporFiveB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporHN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporHN3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporHe3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporJ3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporLy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRu3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporSuz
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporTh
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporTh7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1ThreeTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZCo1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZMathHS1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZSpor
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K14ChevFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatB.StdSmallBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TStdCovDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Alt
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporFi24
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporHe7
public import CFSG.Quasithin.SteinbergCBGDTrace
public import Certificates.Certificate8007
public import Certificates.Certificate8008
public import Certificates.Data.TabCo1ThreeE

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived inner inner_map_congr)
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel hasLabel_congr hasLabel_mono
  hasLabel_of_equiv_centerQuot)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind)
open CFSG.ComponentClassification.PerfectAutomorphisms
  (hom_eq_id_of_central_displacement)
open CFSG.StandardType (MarkedModel markTag markRank markChar markDeg)
open scoped commutatorElement

theorem isSimpleGroup_of_isU42 {X : Type} [Group X] (h : CFSG.Assembly.LargeEvenIsU42 X) :
    IsSimpleGroup X := by
  obtain ⟨F, hF, hfin, hFcard, ⟨e⟩⟩ := h
  exact CFSG.LocalAnalysis.GLTheoremA.S10.isSimple_of_isU4two
    (CFSG.LocalAnalysis.GLTheoremA.CatB.catalogIs_u4two_of_statedProj hFcard e)

theorem isSimpleGroup_of_isA6 {X : Type} [Group X]
    (h : Nonempty (X ≃* alternatingGroup (Fin 6))) : IsSimpleGroup X := by
  obtain ⟨e⟩ := h
  exact e.isSimpleGroup_congr.mpr (alternatingGroup.isSimpleGroup (by norm_num))

theorem isSimpleGroup_of_glaSmall {G : Type} [Group G] {K : Subgroup G} (h : GLASmall K)
    (hq : CFSG.Open.IsQuasisimple ↥K) : IsSimpleGroup ↥K := by
  rcases h with hU | hA
  · exact isSimpleGroup_of_isU42 hU
  · exact isSimpleGroup_of_isA6 hA

theorem card_of_glaSmall {G : Type} [Group G] {K : Subgroup G} (h : GLASmall K) :
    Nat.card ↥K = 25920 ∨ Nat.card ↥K = 360 := by
  rcases h with hU | hA
  · exact Or.inl (CFSG.StandardType.IOneOrthEnd.card_of_isU42 hU)
  · obtain ⟨e⟩ := hA
    exact Or.inr ((Nat.card_congr e.toEquiv).trans
      CFSG.StandardType.IOneOrthEnd.card_alternatingGroup_six)

theorem three_dvd_card_of_glaSmall {G : Type} [Group G] {K : Subgroup G} (h : GLASmall K) :
    3 ∣ Nat.card ↥K := by
  rcases card_of_glaSmall h with hc | hc <;> rw [hc] <;> norm_num

theorem exists_noncomm_of_glaSmall {G : Type} [Group G] {K : Subgroup G} (h : GLASmall K)
    (hq : CFSG.Open.IsQuasisimple ↥K) : ∃ a b : ↥K, a * b ≠ b * a := by
  haveI := isSimpleGroup_of_glaSmall h hq
  rcases card_of_glaSmall h with hc | hc
  · by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    letI gK : Group ↥K := inferInstance
    letI : CommGroup ↥K := { gK with mul_comm := fun a b => hcon a b }
    have hprime : (Nat.card ↥K).Prime := (CommGroup.is_simple_iff_prime_card (α := ↥K)).1 ‹_›
    rw [hc] at hprime
    norm_num at hprime
  · by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    letI gK : Group ↥K := inferInstance
    letI : CommGroup ↥K := { gK with mul_comm := fun a b => hcon a b }
    have hprime : (Nat.card ↥K).Prime := (CommGroup.is_simple_iff_prime_card (α := ↥K)).1 ‹_›
    rw [hc] at hprime
    norm_num at hprime

theorem center_eq_bot_of_glaSmall {G : Type} [Group G] {K : Subgroup G} (h : GLASmall K)
    (hq : CFSG.Open.IsQuasisimple ↥K) : Subgroup.center ↥K = ⊥ := by
  haveI := isSimpleGroup_of_glaSmall h hq
  exact CFSG.StandardType.center_eq_bot_of_isSimpleGroup_of_nonabelian
    (exists_noncomm_of_glaSmall h hq)



section DerivedInner


theorem inner_of_hasLabel_B2der {S : Type} [Group S] [Finite S] {lab : GLALabel}
    (hX : HasLabel S (· = lab)) (hcen : Subgroup.center S = ⊥) (ht : lab.tag = .B2der)
    {α : MulAut S} (hα : α ^ 3 = 1) : α ∈ inner S := by
  have hM : MarkedModel lab (S ⧸ Subgroup.center S) :=
    CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel hX
  let eZ : S ⧸ Subgroup.center S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  have hMS : MarkedModel lab S := hM.of_mulEquiv eZ
  have hm : CFSG.Blueprint.LieModel S .PSL 2 3 2 := by
    simpa [MarkedModel, ht, markTag, markRank, markChar, markDeg] using hMS
  have hSC : CFSG.Open.StatedClassicalModel S .PSL 2 3 2 :=
    hm.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  obtain ⟨e6⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_alternating_six_of_psl_two_nine hSC
  have hin : MulAut.congr e6 α ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (alternatingGroup (Fin 6)) :=
    alt6_aut_three_inner _ (by rw [← map_pow, hα, map_one])
  rw [← inner_map_congr e6] at hin
  exact (Subgroup.mem_map_iff_mem (MulAut.congr e6).injective).mp hin

theorem inner_of_hasLabel_G2der {S : Type} [Group S] [Finite S] {lab : GLALabel}
    (hX : HasLabel S (· = lab)) (hcen : Subgroup.center S = ⊥) (ht : lab.tag = .G2der)
    {α : MulAut S} (hα : α ^ 3 = 1) : α ∈ inner S := by
  have hM : MarkedModel lab (S ⧸ Subgroup.center S) :=
    CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel hX
  let eZ : S ⧸ Subgroup.center S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  have hMS : MarkedModel lab S := hM.of_mulEquiv eZ
  have hm : CFSG.Blueprint.LieModel S .PSU 3 3 1 := by
    simpa [MarkedModel, ht, markTag, markRank, markChar, markDeg] using hMS
  obtain ⟨eU⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hm
  have hcardS : Nat.card S = 6048 :=
    (Nat.card_congr eU.toEquiv).trans
      ((CFSG.GH74.KGroups.card_group _ CFSG.GH74.KGroups.U33.QP_ok).trans
        CFSG.GH74.KGroups.U33.QP_valid.2)
  have hcardA : Nat.card (MulAut S) = 12096 := CFSG.GH74.KGroups.U33.card_mulAut eU
  have hle : Nat.card (MulAut S) ≤ 2 * Nat.card S := by
    rw [hcardA, hcardS]
  exact CFSG.Quasithin.H13.A5.mem_inner_of_pow_three_of_card_le hcen hle hα

theorem inner_of_hasLabel_twF4der {S : Type} [Group S] [Finite S] {lab : GLALabel}
    (hX : HasLabel S (· = lab)) (hcen : Subgroup.center S = ⊥) (ht : lab.tag = .twF4der)
    {α : MulAut S} (hα : α ^ 3 = 1) : α ∈ inner S := by
  have hM : MarkedModel lab (S ⧸ Subgroup.center S) :=
    CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel hX
  let eZ : S ⧸ Subgroup.center S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  have hMS : MarkedModel lab S := hM.of_mulEquiv eZ
  have hn1 : lab.n = 1 :=
    CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.n_eq_one_of_derived
      (CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.lambda2_of_hasLabel hX) (Or.inr (Or.inr ht))
  have hm : CFSG.Blueprint.LieModel S .Tits 0 2 1 := by
    simpa [MarkedModel, ht, markTag, markRank, markChar, markDeg, hn1] using hMS
  obtain ⟨eT⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv S 2 1
    ((CFSG.Blueprint.LieModel.reeTitsModel hm (t := .Tits)
      (by simp [CFSG.Blueprint.reeTitsTags])).2)
  have hin : MulAut.congr eT α ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner CFSG.Sporadic.Schreier.Tits.titsD :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.titsD_mem_inner_of_pow_eq_one
      Nat.prime_three (by norm_num) (by rw [← map_pow, hα, map_one])
  rw [← inner_map_congr eT] at hin
  exact (Subgroup.mem_map_iff_mem (MulAut.congr eT).injective).mp hin

end DerivedInner

theorem nonempty_equiv_chevTransfer {G : Type} [Group G] [Finite G] {L K : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (hap : IsPGroup 3 (Subgroup.zpowers a))
    (hKL : K ≤ L) (hKsimple : IsSimpleGroup ↥K)
    (hKglap : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({a} : Set G)) K) :
    Nonempty (↥K ≃* ↥(chevTransfer 3 L K)) := by
  have hJ0 : GLAPComponent 3 (fixSubgroup (chevAut 3 L ⟨a, ha⟩)) (chevTransfer 3 L K) :=
    glaPComponent_chevTransfer Nat.prime_three ha hap hKglap
  have hJ0ne : chevTransfer 3 L K ≠ ⊥ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_ne_bot hJ0
  let eK : ↥(K.subgroupOf L) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKL
  haveI : IsSimpleGroup ↥(K.subgroupOf L) := eK.isSimpleGroup_congr.mpr hKsimple
  let π : ↥(K.subgroupOf L) →* PSimple 3 L :=
    (chevQuotHom 3 L).comp (K.subgroupOf L).subtype
  have hrange : π.range = chevTransfer 3 L K := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hker : π.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact h
    · exfalso
      apply hJ0ne
      have hπ1 : π = 1 := by
        ext x
        exact MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x)
      have hbot : π.range = ⊥ := by
        rw [hπ1, MonoidHom.range_one]
      rwa [hrange] at hbot
  have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hker
  let π' : ↥(K.subgroupOf L) →* ↥(chevTransfer 3 L K) :=
    π.codRestrict _ fun x => by rw [← hrange]; exact ⟨x, rfl⟩
  have hπ'inj : Function.Injective π' := fun x y h => hinj (Subtype.ext_iff.1 h)
  have hπ'surj : Function.Surjective π' := by
    intro y
    have hy : (y : PSimple 3 L) ∈ π.range := by rw [hrange]; exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  exact ⟨eK.symm.trans (MulEquiv.ofBijective π' ⟨hπ'inj, hπ'surj⟩)⟩

theorem centralizes_of_centMod_of_isQuasisimple {G : Type} [Group G] [Finite G] {p : ℕ}
    {L : Subgroup G} {g : G} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hne : GLAPPrimeCore p ↥L ≠ ⊤) (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hc : CentMod p L g) : g ∈ Subgroup.centralizer (L : Set G) := by
  haveI : Group.IsPerfect ↥L := ⟨hq.1⟩
  have hOZ : GLAPPrimeCore p ↥L ≤ Subgroup.center ↥L :=
    le_center_of_normal_of_isQuasisimple hq inferInstance hne
  let σ : ↥L →* ↥L := (Subgroup.normalizerMonoidHom (H := L)) ⟨g, hg⟩
  have hσ : ∀ x : ↥L, ((σ x : ↥L) : G) = g * (x : G) * g⁻¹ := fun x =>
    chev_coe_normalizerMonoidHom ⟨g, hg⟩ x
  have hdisp : ∀ x : ↥L, x⁻¹ * σ x ∈ Subgroup.center ↥L := by
    intro x
    have hmemG : ⁅((x : ↥L) : G)⁻¹, g⁆ ∈ GLAPPrimeCoreOf p L :=
      hc.2 (Subgroup.commutator_mem_commutator (L.inv_mem x.2)
        (Subgroup.mem_zpowers g))
    have hmemL : ⁅((x : ↥L) : G)⁻¹, g⁆ ∈ L :=
      (Subgroup.map_subtype_le (GLAPPrimeCore p ↥L)) hmemG
    have hcore : (⟨⁅((x : ↥L) : G)⁻¹, g⁆, hmemL⟩ : ↥L) ∈ GLAPPrimeCore p ↥L :=
      (chev_mem_glaPPrimeCoreOf_iff hmemL).1 hmemG
    have hval : ((x⁻¹ * σ x : ↥L) : G) = ⁅((x : ↥L) : G)⁻¹, g⁆ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hσ, commutatorElement_def]
      group
    rw [show x⁻¹ * σ x = ⟨⁅((x : ↥L) : G)⁻¹, g⁆, hmemL⟩ from Subtype.ext hval]
    exact hOZ hcore
  have hid := hom_eq_id_of_central_displacement σ hdisp
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  have hfix : σ ⟨x, hx⟩ = ⟨x, hx⟩ := congrArg (fun φ : ↥L →* ↥L => φ ⟨x, hx⟩) hid
  have hval : g * x * g⁻¹ = x := by
    have := congrArg Subtype.val hfix
    simpa only [hσ, MonoidHom.id_apply] using this
  exact (mul_inv_eq_iff_eq_mul.mp hval).symm


section Main


theorem alphaRed_holds : AlphaRed := by
  intro Ω _ _ B x L _ hcfg hLn hmax hex hsmall d hLZ
  obtain ⟨D, K, hpre⟩ := hex
  obtain ⟨d0, hdD, hdnot⟩ := CFSG.LocalAnalysis.GLTheoremA.S171.exists_y hcfg.prime hcfg.ne_one hpre
  have hdN : d0 ∈ Subgroup.normalizer (L : Set Ω) := hcfg.norm (hpre.1 hdD)
  have hd3 : d0 ^ 3 = 1 := hpre.2.1.2 d0 hdD
  have hLx : L ≤ Subgroup.centralizer ({x} : Set Ω) := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp ((hcfg.cent x hcfg.mem).mpr
      (Subgroup.mem_zpowers x)) l hl)
  have hKcomp : CFSG.Open.IsComponentOf K
      (L ⊓ Subgroup.centralizer ({d0} : Set Ω)) := by
    rw [← CFSG.LocalAnalysis.GLTheoremA.S171.L_cs_eq hcfg.prime hcfg.ne_one hpre hdD hdnot hLx]
    exact hpre.2.2.2.2.2.1
  have hKq : CFSG.Open.IsQuasisimple ↥K := hKcomp.2.2
  have hKsmall : GLASmall K := hsmall D K hpre
  have hKle : K ≤ L := hKcomp.1.trans inf_le_left
  have h3K : 3 ∣ Nat.card ↥K := three_dvd_card_of_glaSmall hKsmall
  have h3L : 3 ∣ Nat.card ↥L := h3K.trans (Subgroup.card_dvd_of_le hKle)
  have hKglap : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({d0} : Set Ω)) K :=
    CFSG.RankThree.PartTwo.Sec4.Ronan148L.glaPComponent_three_of_isComponentOf hKcomp h3K
  have hKsimple : IsSimpleGroup ↥K := isSimpleGroup_of_glaSmall hKsmall hKq
  have hneL : GLAPPrimeCore 3 ↥L ≠ ⊤ := by
    intro htop
    have hcop : Nat.Coprime 3 (Nat.card ↥L) := by
      have h := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥L)
      rw [show CFSG.pPrimeCore 3 ↥L = ⊤ from htop, Subgroup.card_top] at h
      simpa using h
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop h3L
  have hLsn : CFSG.Open.IsSubnormal L (⊤ : Subgroup Ω) :=
    CFSG.Open.IsSubnormal.step le_top (hLn.subgroupOf ⊤) (CFSG.Open.IsSubnormal.refl ⊤)
  have hLglap : GLAPComponent 3 (⊤ : Subgroup Ω) L :=
    CFSG.HardMathSupport.Solomon.Coordinator.i253_glaPComponent_of_subnormal le_top hLsn
      hcfg.qs h3L
  have hqL : CFSG.Open.IsQuasisimple (PQuot 3 L) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hLglap
  have hLq : CFSG.Open.IsQuasisimple ↥L := hcfg.qs
  have hInnB : CFSG.LocalAnalysis.GLTheoremA.S10.InnDiagOn 3 B L :=
    CFSG.LocalAnalysis.GLTheoremA.S10.innDiagOn_of_inner hLglap hLq hcfg.idiag
  have hInnZ : CFSG.LocalAnalysis.GLTheoremA.S10.InnDiagOn 3
      (Subgroup.zpowers d0) L :=
    CFSG.LocalAnalysis.GLTheoremA.S10.innDiagOn_mono hInnB
      (Subgroup.zpowers_le.2 (hpre.1 hdD))
  obtain ⟨labL, hLabQuot, hinDiag⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.I141F.innDiagKind_chevAut hdN hqL hInnZ
  have hcenPS : Subgroup.center (PSimple 3 L) = ⊥ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.center_centerQuot_eq_bot hqL
  obtain ⟨hsimplePS, hncPS⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.chev_pSimple_simple_nonabelian Nat.prime_three hLglap
  haveI : IsSimpleGroup (PSimple 3 L) := hsimplePS
  have hperfPS : commutator (PSimple 3 L) = ⊤ :=
    (CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_isQuasisimple_of_simple hncPS).1
  have hLabPS : HasLabel (PSimple 3 L) (· = labL) :=
    hasLabel_of_equiv_centerQuot hperfPS
      ((QuotientGroup.quotientMulEquivOfEq hcenPS).trans QuotientGroup.quotientBot).symm hLabQuot
  have hα0pow : (chevAut 3 L ⟨d0, hdN⟩) ^ 3 = 1 :=
    CFSG.LocalAnalysis.GLTheoremA.chevAut_pow_eq_one 3 L hdN hd3
  have hα0ne : chevAut 3 L ⟨d0, hdN⟩ ≠ 1 := by
    intro h1
    have hcm : CentMod 3 L d0 :=
      (CFSG.LocalAnalysis.GLTheoremA.chevAut_eq_one_iff Nat.prime_three hLglap hdN).1 h1
    have hcent := centralizes_of_centMod_of_isQuasisimple hLq hneL hdN hcm
    exact hdnot ((hcfg.cent d0 (hpre.1 hdD)).1 hcent)
  have hα0der : chevAut 3 L ⟨d0, hdN⟩ ∈ innAutDerived (PSimple 3 L) := by
    by_cases hB2 : labL.tag = .B2der
    · exact CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived (PSimple 3 L)
        (inner_of_hasLabel_B2der hLabPS hcenPS hB2 hα0pow)
    by_cases hG2 : labL.tag = .G2der
    · exact CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived (PSimple 3 L)
        (inner_of_hasLabel_G2der hLabPS hcenPS hG2 hα0pow)
    by_cases hTw : labL.tag = .twF4der
    · exact CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived (PSimple 3 L)
        (inner_of_hasLabel_twF4der hLabPS hcenPS hTw hα0pow)
    · exact CFSG.LocalAnalysis.GLTheoremA.I141F.Tri.mem_innAutDerived_of_innDiagKind_of_not_derived
        hcenPS ⟨hB2, hG2, hTw⟩ hinDiag
  let J0 : Subgroup (PSimple 3 L) := chevTransfer 3 L K
  have hd3p : IsPGroup 3 (Subgroup.zpowers d0) :=
    CFSG.LocalAnalysis.GLTheoremA.isPGroup_zpowers_of_pow_eq_one hd3
  have hJ0glap : GLAPComponent 3 (fixSubgroup (chevAut 3 L ⟨d0, hdN⟩)) J0 :=
    CFSG.LocalAnalysis.GLTheoremA.glaPComponent_chevTransfer Nat.prime_three hdN hd3p hKglap
  obtain ⟨eKJ⟩ := nonempty_equiv_chevTransfer hdN hd3p hKle hKsimple hKglap
  have hqJ0 : CFSG.Open.IsQuasisimple ↥J0 :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eKJ hKq
  have hJ0comp : CFSG.Open.IsComponentOf J0
      (fixSubgroup (chevAut 3 L ⟨d0, hdN⟩)) :=
    ⟨hJ0glap.1, hJ0glap.2.1, hqJ0⟩
  have hcardJ0 : Nat.card (↥J0 ⧸ Subgroup.center ↥J0) =
      Nat.card (↥K ⧸ Subgroup.center ↥K) :=
    Nat.card_congr (QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥J0) eKJ
      (Subgroup.map_center_eq eKJ)).symm.toEquiv
  have hcardK : Nat.card (↥K ⧸ Subgroup.center ↥K) = Nat.card ↥K := by
    rw [center_eq_bot_of_glaSmall hKsmall hKq]
    exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
  have hJ0small : HStdExcl.SmallOrd J0 := by
    rcases card_of_glaSmall hKsmall with hc | hc
    · exact Or.inl (hcardJ0.trans (hcardK.trans hc))
    · exact Or.inr (hcardJ0.trans (hcardK.trans hc))
  haveI : IsSimpleGroup ↥K := hKsimple
  have hPsimpleK : Nonempty (PSimple 3 K ≃* ↥K) :=
    CFSG.LocalAnalysis.GLTheoremA.LevelLieU6.nonempty_pSimple_equiv_of_simple hKglap
  have hcatK : catalogIs (PSimple 3 K) S9.isU4two ∨
      catalogIs (PSimple 3 K) S10.isA6 := by
    rcases hKsmall with hU | hA6
    · exact Or.inl (CFSG.LocalAnalysis.GLTheoremA.S171.catalog_pSimple_u42 hKq hU).2
    · obtain ⟨ePK⟩ := hPsimpleK
      obtain ⟨eA⟩ := hA6
      refine Or.inr ⟨TauCeti.CFSGIndex.alternating 6 (by norm_num),
        by simp [CFSG.LocalAnalysis.GLTheoremA.S10.isA6], ⟨?_⟩⟩
      exact ePK.trans eA
  obtain ⟨eKJp⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.nonempty_pSimple_equiv_chevTransfer Nat.prime_three hdN hd3p
      hKglap
  have hJ0cat : catalogIs (PSimple 3 J0) S9.isU4two ∨
      catalogIs (PSimple 3 J0) S10.isA6 := by
    rcases hcatK with h | h
    · exact Or.inl ((CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr eKJp).mp h)
    · exact Or.inr ((CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr eKJp).mp h)
  obtain ⟨ePL⟩ := CFSG.LocalAnalysis.GLTheoremA.S9.nonempty_pSimple_equiv Nat.prime_three hLglap hLq
  obtain ⟨eLZ⟩ := hLZ
  let e : PSimple 3 L ≃* (TauCeti.CFSGIndex.lie d).Group := ePL.trans eLZ
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group :=
    Finite.of_equiv (PSimple 3 L) e.toEquiv
  let α : MulAut (TauCeti.CFSGIndex.lie d).Group := MulAut.congr e (chevAut 3 L ⟨d0, hdN⟩)
  let J : Subgroup (TauCeti.CFSGIndex.lie d).Group := J0.map e.toMonoidHom
  have hαpow : α ^ 3 = 1 := by
    dsimp only [α]
    rw [← map_pow, hα0pow, map_one]
  have hαne : α ≠ 1 := by
    intro h
    have h' : MulAut.congr e (chevAut 3 L ⟨d0, hdN⟩) = 1 := h
    rw [← map_one (MulAut.congr e)] at h'
    exact hα0ne ((MulAut.congr e).injective h')
  have hαder : α ∈ innAutDerived (TauCeti.CFSGIndex.lie d).Group :=
    (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr e).2
      hα0der
  have hfix : fixSubgroup α = (fixSubgroup (chevAut 3 L ⟨d0, hdN⟩)).map e.toMonoidHom := by
    dsimp only [α]
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e _
  have hJglap : GLAPComponent 3 (fixSubgroup α) J := by
    have h := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv Nat.prime_three e hJ0glap
    simpa only [J, hfix] using h
  have hJcomp : CFSG.Open.IsComponentOf J (fixSubgroup α) := by
    have h := CFSG.Fischer.Classification.Recognition.IsComponentOf.map_mulEquiv e hJ0comp
    simpa only [J, hfix] using h
  have hJsmall : HStdExcl.SmallOrd J := by
    have hcard := CFSG.Fischer.Classification.Recognition.card_quotient_center_map_mulEquiv e J0
    rcases hJ0small with h | h
    · exact Or.inl (hcard.trans h)
    · exact Or.inr (hcard.trans h)
  have hJcat : catalogIs (PSimple 3 J) S9.isU4two ∨
      catalogIs (PSimple 3 J) S10.isA6 := by
    obtain ⟨eJp⟩ := CFSG.LocalAnalysis.GLTheoremA.nonempty_pSimple_equiv_map Nat.prime_three
      e.toMonoidHom hJ0glap hJglap
    rcases hJ0cat with h | h
    · exact Or.inl ((CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr eJp).mp h)
    · exact Or.inr ((CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr eJp).mp h)
  exact ⟨α, hαpow, hαne, fun _ => hαder, J, hJglap, hJcomp, hJcat, hJsmall⟩

end Main

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
