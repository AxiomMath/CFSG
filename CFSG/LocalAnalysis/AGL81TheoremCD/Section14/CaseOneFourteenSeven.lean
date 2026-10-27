module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneDefs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34AutModel
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneSetup
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CoreTwoSL34
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgAct
import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
import CFSG.GroupTheory.ConjugatePairSubnormality
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.GroupTheory.PGroup.CardCoprime
import CFSG.HardMathSupport.Solomon.Coordinator.Th1J1.Transvection
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.NormalizerChain
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
import CFSG.Models.PGLOrders
import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.OffenderB10
import CFSG.Quasithin.Vol2.Ch3Sec1Aux
import CFSG.RankThree.PartOne.S11d.FinalLemmas
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.Quasithin.Background.A3Structure318Star

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

variable {G : Type} [Group G] [Finite G]

theorem CaseOneCtx.pCoreOf_two_J
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) :
    CFSG.Open.pCoreOf 2 J = (CFSG.pPrimeCore 3 ↥J).map J.subtype := by
  rw [CFSG.openPCoreOf_eq_map_pCore]
  rw [pCore_two_eq_pPrimeCore_three_of_isL34Type c.choice.J_comp.2.2.1
    (c.isSL34Star).1]

private theorem ker_mk_center_comp (J : Subgroup G) :
    ((QuotientGroup.mk' (Subgroup.center (threeStar J))).comp
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J))).ker =
      (oTwoZStar J).subgroupOf J := by
  rw [oTwoZStar]
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
    have hx' : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) x ∈
        Subgroup.center (threeStar J) :=
      (QuotientGroup.eq_one_iff _).mp hx
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_map_of_mem J.subtype (Subgroup.mem_comap.mpr hx'))
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
    have hyx' : y = x := Subtype.ext hyx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact (QuotientGroup.eq_one_iff _).mpr (by rwa [hyx'] at hy)

private abbrev barQuotient (J : Subgroup G) : Type :=
  threeStar J ⧸ Subgroup.center (threeStar J)

private def barMap (J : Subgroup G) : ↥J →* barQuotient J :=
  (QuotientGroup.mk' (Subgroup.center (threeStar J))).comp
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J))

private theorem ker_barMap (J : Subgroup G) :
    (barMap J).ker = (oTwoZStar J).subgroupOf J := by
  unfold barMap
  exact ker_mk_center_comp J

private theorem card_barQuotient {J : Subgroup G} (hL : IsL34Type (threeStar J)) :
    Nat.card (barQuotient J) = 20160 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_projSL_quotient_center_of_isL34Type hL
  rw [Nat.card_congr e.toEquiv, CFSG.PGLModel.card_projSL_three_four]

private theorem CaseOneCtx.isSylowOf_inf_J_of_isSylowOf_T
    {M H E Q J R T : Subgroup G} (c : CaseOneCtx G M H E Q J R T)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T H) :
    CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ J) J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTK : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ kSub 3 M H) (kSub 3 M H) :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.YCfg.isSylowOf_inf_of_subnormalIn hT
      (kSub_le 3 M H) (kSub_subgroupOf_isSubnormal 3 M H)
  have hTJ' : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ kSub 3 M H ⊓ J) J :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.YCfg.isSylowOf_inf_of_subnormalIn hTK
      c.choice.isKComp.1 (IsKComp.isSubnormal c.choice.isKComp)
  simpa [inf_assoc, inf_eq_right.mpr c.choice.isKComp.1] using hTJ'

private theorem CaseOneCtx.dvd_card_image_JM_of_isSylowOf_T
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T H) :
    64 ∣ Nat.card ↥(((J ⊓ M).subgroupOf J).map (barMap J)) ∧
      9 ∣ Nat.card ↥(((J ⊓ M).subgroupOf J).map (barMap J)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardJbar : Nat.card (barQuotient J) = 20160 := card_barQuotient (c.isSL34Star).1
  have hπ : Function.Surjective (barMap J) :=
    (QuotientGroup.mk'_surjective (Subgroup.center (threeStar J))).comp
      (QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥J))
  let Y : Subgroup (barQuotient J) := ((J ⊓ M).subgroupOf J).map (barMap J)
  have hTM : T ≤ M := c.T_sylow.le.trans inf_le_right
  have hTY : ((T ⊓ J).subgroupOf J).map (barMap J) ≤ Y :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono J
      (le_inf inf_le_right (inf_le_left.trans hTM)))
  have hQY : ((Q ⊓ J).subgroupOf J).map (barMap J) ≤ Y :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono J
      (le_inf inf_le_right (inf_le_left.trans (c.choice.Q_le_M c.nine))))
  obtain ⟨ST, hST⟩ := (c.isSylowOf_inf_J_of_isSylowOf_T hT).exists_sylow_eq_subgroupOf
  let ST' : Sylow 2 (barQuotient J) := ST.mapSurjective hπ
  have hST'coe : (ST' : Subgroup (barQuotient J)) = ((T ⊓ J).subgroupOf J).map (barMap J) := by
    rw [Sylow.coe_mapSurjective, hST]
  have hcardST' : Nat.card ↥(ST' : Subgroup (barQuotient J)) = 64 := by
    rw [Sylow.card_eq_multiplicity, hcardJbar]
    norm_num [Nat.factorization]
  obtain ⟨SQ, hSQ⟩ := (c.choice.isSylowOf_inf_J c.pre c.nine).exists_sylow_eq_subgroupOf
  let SQ' : Sylow 3 (barQuotient J) := SQ.mapSurjective hπ
  have hSQ'coe : (SQ' : Subgroup (barQuotient J)) = ((Q ⊓ J).subgroupOf J).map (barMap J) := by
    rw [Sylow.coe_mapSurjective, hSQ]
  have hcardSQ' : Nat.card ↥(SQ' : Subgroup (barQuotient J)) = 9 := by
    rw [Sylow.card_eq_multiplicity, hcardJbar]
    norm_num [Nat.factorization]
  constructor
  · rw [← hcardST']
    exact Subgroup.card_dvd_of_le (hST'coe ▸ hTY)
  · rw [← hcardSQ']
    exact Subgroup.card_dvd_of_le (hSQ'coe ▸ hQY)

private theorem CaseOneCtx.j_le_sup_oTwoZStar_of_isSylowOf_T
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T H) :
    J ≤ (J ⊓ M) ⊔ oTwoZStar J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdiv := c.dvd_card_image_JM_of_isSylowOf_T hT
  let Y : Subgroup (barQuotient J) := ((J ⊓ M).subgroupOf J).map (barMap J)
  have hKbar : CFSG.Quasithin.IsPSL 3 2 2 (barQuotient J) :=
    isPSL_of_isL34Type (c.isSL34Star).1
  have hYtop : Y = ⊤ := l34_eq_top_of_dvd_card hKbar hdiv.1 hdiv.2
  have hker : (barMap J).ker = (oTwoZStar J).subgroupOf J := ker_barMap J
  intro x hx
  have hxπ : barMap J ⟨x, hx⟩ ∈ Y := by rw [hYtop]; exact Subgroup.mem_top _
  obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hxπ
  have hyJM : (y : G) ∈ J ⊓ M := Subgroup.mem_subgroupOf.mp hy
  have hmem : (⟨x, hx⟩ * y⁻¹ : ↥J) ∈ (barMap J).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
  have hmemO : (x : G) * (y : G)⁻¹ ∈ oTwoZStar J := by
    rw [hker] at hmem
    simpa using Subgroup.mem_subgroupOf.mp hmem
  have hxeq : (x : G) = ((x : G) * (y : G)⁻¹) * (y : G) := by group
  rw [hxeq]
  simpa [sup_comm] using Subgroup.mul_mem_sup hmemO hyJM

theorem CaseOneCtx.not_isSylowOf_T
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) :
    ¬ CFSG.ABGLocalTools.IsSylowOf 2 T H := by
  intro hT
  have hJle := c.j_le_sup_oTwoZStar_of_isSylowOf_T hT
  exact c.choice.not_le_M c.player
    (hJle.trans (sup_le inf_le_right (c.choice.oTwoZStar_le_M c.pre c.nine c.typeA)))

theorem CaseOneCtx.normalizer_T_not_le
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) :
    ¬ Subgroup.normalizer (T : Set G) ≤ M := by
  intro hN
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := c.T_sylow.le.trans inf_le_left
  obtain ⟨T₁, hT₁, hTT₁⟩ :=
    CFSG.RankThree.PartOne.exists_isSylowOf_ge (p := 2) hTH c.T_sylow.isPGroup
  have hTne : T ≠ T₁ := by
    intro heq
    exact c.not_isSylowOf_T (heq ▸ hT₁)
  have hlt : T < T₁ := lt_of_le_of_ne hTT₁ hTne
  have hltN := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.lt_normalizer_inf_of_isPGroup
    hT₁.isPGroup hTT₁ hlt
  have hleKM : Subgroup.normalizer (T : Set G) ⊓ T₁ ≤ H ⊓ M :=
    le_inf (inf_le_right.trans hT₁.le) (inf_le_left.trans hN)
  have h2 : IsPGroup 2 ↥(Subgroup.normalizer (T : Set G) ⊓ T₁) :=
    hT₁.isPGroup.to_le inf_le_right
  have heq := c.T_sylow.eq_of_le hltN.le hleKM h2
  exact hltN.ne heq.symm

private theorem CaseOneCtx.card_image_inf_J_bar
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) :
    Nat.card ↥(((Q ⊓ J).subgroupOf J).map (barMap J)) = 9 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardJbar : Nat.card (barQuotient J) = 20160 := card_barQuotient (c.isSL34Star).1
  have hπ : Function.Surjective (barMap J) :=
    (QuotientGroup.mk'_surjective (Subgroup.center (threeStar J))).comp
      (QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥J))
  obtain ⟨SQ, hSQ⟩ := (c.choice.isSylowOf_inf_J c.pre c.nine).exists_sylow_eq_subgroupOf
  let SQ' : Sylow 3 (barQuotient J) := SQ.mapSurjective hπ
  have hSQ'coe : (SQ' : Subgroup (barQuotient J)) =
      ((Q ⊓ J).subgroupOf J).map (barMap J) := by
    rw [Sylow.coe_mapSurjective, hSQ]
  rw [← hSQ'coe, Sylow.card_eq_multiplicity, hcardJbar]
  norm_num [Nat.factorization]

private theorem CaseOneCtx.isElemAbelian_image_inf_J_bar
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M) :
    IsElemAbelian 3 (((Q ⊓ J).subgroupOf J).map (barMap J)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard := c.card_image_inf_J_bar
  have hQexp : ∀ x ∈ Q, x ^ 3 = 1 := (h142 H E Q J c.choice c.typeA).1.2.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · exact IsPGroup.commutative_of_card_eq_prime_sq (p := 3)
      (by rw [hcard]; norm_num) a b
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
    rw [← hxy, ← map_pow]
    have hy3 : y ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hQexp (y : G) (Subgroup.mem_subgroupOf.mp hy).1
    rw [hy3, map_one]

private theorem CaseOneCtx.image_bar_normalized
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) :
    ∀ s ∈ ((Q ⊓ J).subgroupOf J).map (barMap J),
      ∀ b ∈ (R.subgroupOf (Subgroup.normalizer (J : Set G))).map (jBarAct J),
        MulAut.conj s * b * (MulAut.conj s)⁻¹ ∈
          (R.subgroupOf (Subgroup.normalizer (J : Set G))).map (jBarAct J) := by
  intro s hs b hb
  let N : Subgroup G := Subgroup.normalizer (J : Set G)
  let B : Subgroup (MulAut (barQuotient J)) := (R.subgroupOf N).map (jBarAct J)
  change MulAut.conj s * b * (MulAut.conj s)⁻¹ ∈ B
  obtain ⟨q, hq, hsq⟩ := Subgroup.mem_map.mp hs
  obtain ⟨r, hr, hbr⟩ := Subgroup.mem_map.mp hb
  have hqQ : (q : G) ∈ Q := (Subgroup.mem_subgroupOf.mp hq).1
  have hrR : (r : G) ∈ R := Subgroup.mem_subgroupOf.mp hr
  have hqN : (q : G) ∈ N := c.choice.Q_le_normalizer_J c.pre c.nine hqQ
  have hqR : (q : G) ∈ Subgroup.normalizer (R : Set G) := c.R_max.2.2.1 hqQ
  have hqRmem : (q : G) * (r : G) * (q : G)⁻¹ ∈ R :=
    (Subgroup.mem_normalizer_iff.mp hqR (r : G)).mp hrR
  have hqNmem : (q : G) * (r : G) * (q : G)⁻¹ ∈ N :=
    N.mul_mem (N.mul_mem hqN r.2) (N.inv_mem hqN)
  have hJq : jBarAct J ⟨(q : G), hqN⟩ = MulAut.conj s := by
    rw [← hsq]
    simpa [barMap] using jBarAct_of_mem (J := J) (g := (q : G)) q.2
  have hconj : MulAut.conj s * b * (MulAut.conj s)⁻¹ =
      jBarAct J (⟨(q : G), hqN⟩ * r * ⟨(q : G), hqN⟩⁻¹) := by
    rw [map_mul, map_mul, map_inv, hJq, hbr]
  have hmemB : jBarAct J (⟨(q : G), hqN⟩ * r * ⟨(q : G), hqN⟩⁻¹) ∈ B := by
    refine Subgroup.mem_map.mpr ⟨⟨(q : G) * (r : G) * (q : G)⁻¹, hqNmem⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr hqRmem
    · apply congrArg (jBarAct J)
      apply Subtype.ext
      rfl
  rw [hconj]
  exact hmemB

theorem CaseOneCtx.jBarAct_R
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M) :
    Nat.card ((R.subgroupOf (Subgroup.normalizer (J : Set G))).map (jBarAct J)) ≤ 2 ∧
      ∀ r : ↥(Subgroup.normalizer (J : Set G)), (r : G) ∈ R → jBarAct J r ≠ 1 →
        ∃ g : ↥(Subgroup.normalizer (J : Set G)), (g : G) ∈ J ∧
          (jBarAct J (r * g * r * g⁻¹)) ^ 12 ≠ 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup G := Subgroup.normalizer (J : Set G)
  let B : Subgroup (MulAut (barQuotient J)) := (R.subgroupOf N).map (jBarAct J)
  have hKbar : CFSG.Quasithin.IsPSL 3 2 2 (barQuotient J) :=
    isPSL_of_isL34Type (c.isSL34Star).1
  have hRsub2 : IsPGroup 2 ↥(R.subgroupOf N) :=
    c.R_max.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe c.R_le_normalizer_J).symm
  have hB2 : IsPGroup 2 ↥B := hRsub2.map (jBarAct J)
  obtain ⟨hBcard, hBsec⟩ := l34_aut_two_subgroup hKbar hB2 c.card_image_inf_J_bar
    (c.isElemAbelian_image_inf_J_bar h142) c.image_bar_normalized
  refine ⟨?_, ?_⟩
  · simpa [B] using hBcard
  · intro r hrR hbne
    have hbB : jBarAct J r ∈ B :=
      Subgroup.mem_map_of_mem (jBarAct J) (Subgroup.mem_subgroupOf.mpr hrR)
    obtain ⟨g, hg⟩ := hBsec (jBarAct J r) hbB hbne
    obtain ⟨h, hhJ, hhconj⟩ := jBarAct_surjective_inner J g
    let g' : ↥N := ⟨h, Subgroup.le_normalizer hhJ⟩
    have hconjg : jBarAct J g' = MulAut.conj g := by
      exact hhconj
    refine ⟨g', hhJ, ?_⟩
    intro h12
    have harg : jBarAct J (r * g' * r * g'⁻¹) =
        jBarAct J r * MulAut.conj g * jBarAct J r * (MulAut.conj g)⁻¹ := by
      rw [map_mul, map_mul, map_mul, map_inv, hconjg]
    rw [harg] at h12
    exact hg h12

private theorem CaseOneCtx.isSubnormal_J_H {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) : (J.subgroupOf H).IsSubnormal :=
  CFSG.GroupTheory.isSubnormal_subgroupOf_trans c.choice.isKComp.1 (kSub_le 3 M H)
    (IsKComp.isSubnormal c.choice.isKComp) (kSub_subgroupOf_isSubnormal 3 M H)

private theorem CaseOneCtx.pCoreOf_two_J_le_R {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) : CFSG.Open.pCoreOf 2 J ≤ R :=
  (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_subnormal 2
    ((CFSG.Quasithin.isSubnormal_iff_subgroupOf
      (c.choice.isKComp.1.trans (kSub_le 3 M H))).mpr c.isSubnormal_J_H)).trans c.core_le_R

private theorem pCoreOf_two_le_pPrimeCore_three (J : Subgroup G) :
    CFSG.Open.pCoreOf 2 J ≤ (CFSG.pPrimeCore 3 ↥J).map J.subtype := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.openPCoreOf_eq_map_pCore]
  exact Subgroup.map_mono (CFSG.Quasithin.A318.pCore_two_le_pPrimeCore (p := 3) (by norm_num))

private theorem CaseOneCtx.charTwo_join {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) :
    CFSG.QuasithinUnique.CharTwo (J ⊔ R) := by
  have hH : IsTwoLocal H := c.choice.hypCGen.isTwoLocal
  have hchar : CFSG.QuasithinUnique.CharTwo H := c.choice.cstar.charTwo H hH
  exact CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hchar
    (sup_le (c.choice.isKComp.1.trans (kSub_le 3 M H)) c.R_max.1)
    (c.core_le_R.trans le_sup_right)

private theorem CaseOneCtx.Q_le_normalizer_join {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) :
    Q ≤ Subgroup.normalizer ((J ⊔ R : Subgroup G) : Set G) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (c.choice.Q_le_normalizer_J c.pre c.nine hq),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (c.R_max.2.2.1 hq)]

private theorem CaseOneCtx.pCoreOf_join_le_R {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) :
    CFSG.Open.pCoreOf 2 (J ⊔ R) ≤ R := by
  set X : Subgroup G := J ⊔ R with hXdef
  set O : Subgroup G := CFSG.Open.pCoreOf 2 X with hOdef
  have hOX : O ≤ X := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 X
  have hO2 : IsPGroup 2 O := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X
  have hXH : X ≤ H := sup_le (c.choice.isKComp.1.trans (kSub_le 3 M H)) c.R_max.1
  have hQO : Q ≤ Subgroup.normalizer (O : Set G) :=
    (c.Q_le_normalizer_join).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_localGroup_le_normalizer_pCoreOf 2 X)
  have hRO : R ≤ Subgroup.normalizer (O : Set G) :=
    le_sup_right.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X)
  have hRO2 : IsPGroup 2 ↥(R ⊔ O : Subgroup G) := by
    rw [sup_comm]
    exact hO2.to_sup_of_normal_left' (K := R) c.R_max.2.1 hRO
  have hQRO : Q ≤ Subgroup.normalizer ((R ⊔ O : Subgroup G) : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (c.R_max.2.2.1 hq),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQO hq)]
  have hROH : R ⊔ O ≤ H := sup_le c.R_max.1 (hOX.trans hXH)
  have hmax := c.R_max.2.2.2 (R ⊔ O) hROH hRO2 hQRO le_sup_left
  exact hmax ▸ le_sup_right

private noncomputable def jKernel (J R : Subgroup G) : Subgroup G :=
  R ⊓ ((jStarAct J).ker).map (Subgroup.normalizer (J : Set G)).subtype

private theorem mem_jKernel_iff {J R : Subgroup G}
    {r : ↥(Subgroup.normalizer (J : Set G))} :
    (r : G) ∈ jKernel J R ↔ (r : G) ∈ R ∧ jStarAct J r = 1 := by
  rw [jKernel, Subgroup.mem_inf]
  have h : (r : G) ∈ ((jStarAct J).ker).map
      (Subgroup.normalizer (J : Set G)).subtype ↔ jStarAct J r = 1 := by
    change (Subgroup.normalizer (J : Set G)).subtype r ∈
      ((jStarAct J).ker).map (Subgroup.normalizer (J : Set G)).subtype ↔ jStarAct J r = 1
    rw [Subgroup.mem_map_iff_mem (Subgroup.subtype_injective _)]
    exact MonoidHom.mem_ker
  exact and_congr Iff.rfl h

private theorem normalizer_le_normalizer_jKernelPart (J : Subgroup G) :
    Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer
      ((((jStarAct J).ker).map (Subgroup.normalizer (J : Set G)).subtype) : Set G) := by
  have hsub : ((((jStarAct J).ker).map (Subgroup.normalizer (J : Set G)).subtype).subgroupOf
      (Subgroup.normalizer (J : Set G))) = (jStarAct J).ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = x := Subtype.ext hyx
      rwa [hyx'] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.map_subtype_le (K := (jStarAct J).ker))]
  rw [hsub]
  infer_instance

private theorem CaseOneCtx.jKernel_conj_mem
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) {j x : G} (hj : j ∈ J)
    (hx : x ∈ jKernel J R) : j * x * j⁻¹ ∈ jKernel J R := by
  have hxR : x ∈ R := (Subgroup.mem_inf.mp hx).1
  have hxN : x ∈ Subgroup.normalizer (J : Set G) := c.R_le_normalizer_J hxR
  have hxact : jStarAct J ⟨x, hxN⟩ = 1 := (mem_jKernel_iff.mp hx).2
  have hxjN : j ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer hj
  have hKconj : j * x * j⁻¹ ∈ ((jStarAct J).ker).map
      (Subgroup.normalizer (J : Set G)).subtype :=
    (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_jKernelPart J hxjN) x).mp
      (Subgroup.mem_inf.mp hx).2
  have hcommR : j * x * j⁻¹ * x⁻¹ ∈ R := by
    have h := congrArg (fun f : MulAut (threeStar J) =>
      f (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) ⟨j, hj⟩)) hxact
    rw [jStarAct_apply_mk, MulAut.one_apply] at h
    let xj : ↥J := ⟨x * j * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxN j).mp hj⟩
    have hq : xj⁻¹ * ⟨j, hj⟩ ∈ CFSG.pPrimeCore 3 ↥J := (QuotientGroup.eq).mp h
    have hq' : x * j⁻¹ * x⁻¹ * j ∈ (CFSG.pPrimeCore 3 ↥J).map J.subtype :=
      Subgroup.mem_map.mpr ⟨xj⁻¹ * ⟨j, hj⟩, hq, by simp [xj, mul_assoc]⟩
    have hconjP : j * (x * j⁻¹ * x⁻¹ * j) * j⁻¹ ∈
        (CFSG.pPrimeCore 3 ↥J).map J.subtype :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.ABGLocalTools.mem_normalizer_map_subtype_of_characteristic
          (M := J) (C := CFSG.pPrimeCore 3 ↥J) (d := j) (Subgroup.le_normalizer hj))
        (x * j⁻¹ * x⁻¹ * j)).mp hq'
    have heq : j * (x * j⁻¹ * x⁻¹ * j) * j⁻¹ = j * x * j⁻¹ * x⁻¹ := by group
    rw [heq] at hconjP
    rw [← c.pCoreOf_two_J] at hconjP
    exact c.pCoreOf_two_J_le_R hconjP
  have hRconj : j * x * j⁻¹ ∈ R := by
    have h2 := R.mul_mem hcommR hxR
    simpa [mul_assoc] using h2
  exact Subgroup.mem_inf.mpr ⟨hRconj, hKconj⟩

private theorem CaseOneCtx.jKernel_normalized_by_J
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) :
    J ≤ Subgroup.normalizer (jKernel J R : Set G) := by
  intro j hj
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact c.jKernel_conj_mem hj hx
  · intro hy
    refine ⟨j⁻¹ * y * j, ?_, ?_⟩
    · simpa using c.jKernel_conj_mem (J.inv_mem hj) hy
    · simp [mul_assoc]

private theorem CaseOneCtx.jKernel_normalized_by_R
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) :
    R ≤ Subgroup.normalizer (jKernel J R : Set G) := by
  intro r hr
  rw [jKernel, Subgroup.mem_normalizer_iff_map_conj_eq,
    Subgroup.map_inf _ _ _ (MulAut.conj r).injective]
  have hRmap : R.map (MulAut.conj r).toMonoidHom = R :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hr)
  have hKmap : (((jStarAct J).ker).map (Subgroup.normalizer (J : Set G)).subtype).map
      (MulAut.conj r).toMonoidHom =
      ((jStarAct J).ker).map (Subgroup.normalizer (J : Set G)).subtype := by
    exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (normalizer_le_normalizer_jKernelPart J (c.R_le_normalizer_J hr)))
  change R.map (MulAut.conj r).toMonoidHom ⊓
      (((jStarAct J).ker).map (Subgroup.normalizer (J : Set G)).subtype).map
        (MulAut.conj r).toMonoidHom = R ⊓
      ((jStarAct J).ker).map (Subgroup.normalizer (J : Set G)).subtype
  rw [hRmap, hKmap]

private theorem CaseOneCtx.jKernel_normal_in_join
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) :
    (jKernel J R).subgroupOf (J ⊔ R) |>.Normal := by
  have hle : jKernel J R ≤ J ⊔ R := inf_le_left.trans le_sup_right
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  exact sup_le c.jKernel_normalized_by_J c.jKernel_normalized_by_R

private theorem CaseOneCtx.jKernel_le_pCoreOf_join
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) :
    jKernel J R ≤ CFSG.Open.pCoreOf 2 (J ⊔ R) :=
  CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (jKernel J R) (J ⊔ R)
    (inf_le_left.trans le_sup_right) c.jKernel_normal_in_join
    (c.R_max.2.1.to_le inf_le_left)

private theorem CaseOneCtx.pCoreOf_join_le_jKernel
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) :
    CFSG.Open.pCoreOf 2 (J ⊔ R) ≤ jKernel J R := by
  set X : Subgroup G := J ⊔ R with hXdef
  set O : Subgroup G := CFSG.Open.pCoreOf 2 X with hOdef
  have hOX : O ≤ X := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 X
  have hO2 : IsPGroup 2 O := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X
  have hO_le_R : O ≤ R := hOdef ▸ hXdef ▸ c.pCoreOf_join_le_R
  have hXO : X ≤ Subgroup.normalizer (O : Set G) := by
    rw [hOdef]
    exact CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X
  have hXleN : X ≤ Subgroup.normalizer (J : Set G) := by
    rw [hXdef]
    exact sup_le Subgroup.le_normalizer c.R_le_normalizer_J
  have hJO : J ≤ Subgroup.normalizer (O : Set G) := le_sup_left.trans hXO
  have hOJN : O ≤ Subgroup.normalizer (J : Set G) := hOX.trans hXleN
  have hOJ_le_O : ⁅O, J⁆ ≤ O := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hJO
  have hOJ_le_J : ⁅O, J⁆ ≤ J :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hOJN
  have hOJ_le_pCore : O ⊓ J ≤ CFSG.Open.pCoreOf 2 J := by
    refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (O ⊓ J) J
      inf_le_right ?_ (hO2.to_le inf_le_left)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    exact (le_inf hJO Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hcomm_le_pprime : ⁅O, J⁆ ≤ (CFSG.pPrimeCore 3 ↥J).map J.subtype :=
    (le_inf hOJ_le_O hOJ_le_J).trans
      (hOJ_le_pCore.trans (pCoreOf_two_le_pPrimeCore_three J))
  intro x hx
  have hxR : x ∈ R := hO_le_R hx
  have hxN : x ∈ Subgroup.normalizer (J : Set G) := hXleN (hOX hx)
  have hxk : jStarAct J ⟨x, hxN⟩ = 1 :=
    jStarAct_eq_one_of_commutator_le (J := J) (x := ⟨x, hxN⟩)
      (fun g hg => hcomm_le_pprime (Subgroup.commutator_mem_commutator hx hg))
  exact mem_jKernel_iff.mpr ⟨hxR, hxk⟩

private theorem CaseOneCtx.pCoreOf_join_eq_jKernel
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) :
    CFSG.Open.pCoreOf 2 (J ⊔ R) = jKernel J R :=
  le_antisymm c.pCoreOf_join_le_jKernel c.jKernel_le_pCoreOf_join

private theorem CaseOneCtx.mem_pCoreOf_join_iff_jBarAct
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) :
    ∀ r : ↥(Subgroup.normalizer (J : Set G)), (r : G) ∈ R →
      ((r : G) ∈ CFSG.Open.pCoreOf 2 (J ⊔ R) ↔ jBarAct J r = 1) := by
  intro r hr
  have hbar : jBarAct J r = 1 ↔ jStarAct J r = 1 := by
    rw [← MonoidHom.mem_ker, ← MonoidHom.mem_ker,
      IsKComp.ker_jBarAct c.choice.isKComp]
  rw [c.pCoreOf_join_eq_jKernel, mem_jKernel_iff]
  exact ⟨fun h => hbar.mpr h.2, fun h => ⟨hr, hbar.mp h⟩⟩

private theorem CaseOneCtx.relIndex_pCoreOf_join_le_two
    {M H E Q J R T : Subgroup G} (c : CaseOneCtx G M H E Q J R T)
    (h142 : FourteenTwoCaseOneAt M) :
    (CFSG.Open.pCoreOf 2 (J ⊔ R)).relIndex R ≤ 2 := by
  let N : Subgroup G := Subgroup.normalizer (J : Set G)
  let O : Subgroup G := CFSG.Open.pCoreOf 2 (J ⊔ R)
  let g : ↥R →* MulAut (barQuotient J) :=
    (jBarAct J).comp (Subgroup.inclusion c.R_le_normalizer_J)
  have hgker : g.ker = O.subgroupOf R := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact (c.mem_pCoreOf_join_iff_jBarAct ⟨(x : G), c.R_le_normalizer_J x.2⟩ x.2).symm
  have hrange : g.range = (R.subgroupOf N).map (jBarAct J) := by
    rw [MonoidHom.range_eq_map]
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      refine Subgroup.mem_map.mpr ⟨⟨(x : G), c.R_le_normalizer_J x.2⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr x.2
      · apply congrArg (jBarAct J)
        apply Subtype.ext
        rfl
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, Subgroup.mem_top _, ?_⟩
      apply congrArg (jBarAct J)
      apply Subtype.ext
      rfl
  have h1 : g.ker.index ≤ 2 := by
    rw [Subgroup.index_ker, hrange]
    exact (c.jBarAct_R h142).1
  rw [hgker] at h1
  simpa [Subgroup.relIndex] using h1

theorem CaseOneCtx.joinStructure
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M) :
    CFSG.QuasithinUnique.CharTwo (J ⊔ R) ∧ CFSG.Open.pCoreOf 2 (J ⊔ R) ≤ R ∧
      (CFSG.Open.pCoreOf 2 (J ⊔ R)).relIndex R ≤ 2 ∧
      ∀ r : ↥(Subgroup.normalizer (J : Set G)), (r : G) ∈ R →
        ((r : G) ∈ CFSG.Open.pCoreOf 2 (J ⊔ R) ↔ jBarAct J r = 1) := by
  refine ⟨c.charTwo_join, c.pCoreOf_join_le_R, c.relIndex_pCoreOf_join_le_two h142, ?_⟩
  intro r hr
  exact c.mem_pCoreOf_join_iff_jBarAct r hr

private noncomputable def joinOmega (J R : Subgroup G) : Subgroup G :=
  CFSG.Quasithin.omegaOneCenterOf (CFSG.Open.pCoreOf 2 (J ⊔ R))

private theorem join_le_normalizer_joinOmega (J R : Subgroup G) :
    J ⊔ R ≤ Subgroup.normalizer (joinOmega J R : Set G) :=
  (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _).trans
    (CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf _)

private theorem isElemAbelian_joinOmega (J R : Subgroup G) :
    IsElemAbelian 2 (joinOmega J R) :=
  CFSG.Quasithin.B2F.isElemAbelian_omegaOneCenterOf _

private theorem pCoreOf_join_le_centralizer_joinOmega (J R : Subgroup G) :
    CFSG.Open.pCoreOf 2 (J ⊔ R) ≤ Subgroup.centralizer (joinOmega J R : Set G) :=
  Subgroup.le_centralizer_iff.mp
    ((CFSG.Quasithin.A4.omegaOneCenterOf_le_centerOf _).trans inf_le_right)

private theorem CaseOneCtx.R_ne_bot {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) : R ≠ ⊥ := by
  intro hR
  have hne : CFSG.Open.pCoreOf 2 H ≠ ⊥ :=
    CFSG.Quasithin.pCoreOf_ne_bot_of_isTwoLocal c.choice.hypCGen.isTwoLocal
  exact hne (le_bot_iff.mp (hR ▸ c.core_le_R))

private theorem CaseOneCtx.exists_char_case_a {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T)
    (hcentral : J ≤ Subgroup.centralizer (joinOmega J R : Set G)) :
    ∃ C : Subgroup G, C ≠ ⊥ ∧ IsPGroup 2 C ∧
      Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (C : Set G) ∧
      J ≤ Subgroup.normalizer (C : Set G) := by
  have hcharX : CFSG.QuasithinUnique.CharTwo (J ⊔ R) := c.charTwo_join
  have hO_le_R : CFSG.Open.pCoreOf 2 (J ⊔ R) ≤ R := c.pCoreOf_join_le_R
  have hZY : CFSG.Quasithin.omegaOneCenterOf R ≤ joinOmega J R := by
    rw [joinOmega]
    refine Subgroup.closure_mono ?_
    intro z hz
    have hzR : z ∈ R := (Subgroup.mem_inf.mp hz.1).1
    have hzC : z ∈ Subgroup.centralizer (R : Set G) := (Subgroup.mem_inf.mp hz.1).2
    have hzO : z ∈ CFSG.Open.pCoreOf 2 (J ⊔ R) := by
      refine hcharX (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
      · exact (le_sup_right : R ≤ J ⊔ R) hzR
      · rw [Subgroup.mem_centralizer_iff]
        intro o ho
        exact (Subgroup.mem_centralizer_iff.mp hzC) o (hO_le_R ho)
    exact ⟨Subgroup.mem_inf.mpr ⟨hzO, by
      rw [Subgroup.mem_centralizer_iff]
      intro o ho
      exact (Subgroup.mem_centralizer_iff.mp hzC) o (hO_le_R ho)⟩, hz.2⟩
  refine ⟨CFSG.Quasithin.omegaOneCenterOf R, ?_, ?_, ?_, ?_⟩
  · exact CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot c.R_max.2.1 c.R_ne_bot
  · exact c.R_max.2.1.to_le (CFSG.Quasithin.A4.omegaOneCenterOf_le R)
  · exact CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf R
  · exact hcentral.trans ((Subgroup.centralizer_le (by
      intro z hz
      exact hZY hz)).trans (Subgroup.centralizer_le_normalizer _))

private theorem le_normalizer_centralizer_of_le_normalizer {Y X : Subgroup G}
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) :
    X ≤ Subgroup.normalizer (Subgroup.centralizer (Y : Set G) : Set G) :=
  hXY.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.centralizer_le_normalizer (Y : Set G))).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer (Y : Set G)))

private theorem commutator_centralizer_le {X Y : Subgroup G}
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) :
    ⁅Subgroup.centralizer (Y : Set G), X⁆ ≤ Subgroup.centralizer (Y : Set G) := by
  rw [Subgroup.commutator_comm]
  exact Subgroup.le_normalizer_iff_commutator_le_right.mp
    (le_normalizer_centralizer_of_le_normalizer hXY)

private theorem card_centralizer_conj_le {Y : Subgroup G} {a h : G}
    (hYmap : Y.map (MulAut.conj h).toMonoidHom = Y) :
    Nat.card ↥(Y ⊓ Subgroup.centralizer ({a} : Set G)) ≤
      Nat.card ↥(Y ⊓ Subgroup.centralizer ({h * a * h⁻¹} : Set G)) := by
  have hmap_le : (Y ⊓ Subgroup.centralizer ({a} : Set G)).map
      (MulAut.conj h).toMonoidHom ≤ Y ⊓ Subgroup.centralizer ({h * a * h⁻¹} : Set G) := by
    refine le_inf ?_ ?_
    · rw [Subgroup.map_inf _ _ _ (MulAut.conj h).injective, hYmap]
      exact inf_le_left
    · rw [Subgroup.map_inf _ _ _ (MulAut.conj h).injective, hYmap]
      refine inf_le_right.trans ?_
      have himg : (MulAut.conj h) '' ({a} : Set G) = ({h * a * h⁻¹} : Set G) := by
        rw [Set.image_singleton, MulAut.conj_apply]
      simpa [himg] using
        Subgroup.map_centralizer_le_centralizer_image ({a} : Set G) (MulAut.conj h).toMonoidHom
  have hle := Subgroup.card_le_of_le hmap_le
  rwa [Subgroup.card_map_of_injective (MulAut.conj h).injective] at hle

private theorem card_le_two_mul_centralizer_of_offender {R O Y A : Subgroup G} {a : G}
    (hA : CFSG.Quasithin.IsMaxElemAbelian R A) (hAR : A ≤ R) (hYR : Y ≤ R)
    (hYea : IsElemAbelian 2 Y) (hO_le_R : O ≤ R)
    (hO_cent : O ≤ Subgroup.centralizer (Y : Set G))
    (hO_normal : R ≤ Subgroup.normalizer (O : Set G)) (hrelO : O.relIndex R ≤ 2)
    (haA : a ∈ A) (haO : a ∉ O) :
    Nat.card Y ≤ 2 * Nat.card ↥(Y ⊓ Subgroup.centralizer ({a} : Set G)) := by
  have hAO_le : A ⊓ O ≤ A ⊓ Subgroup.centralizer (Y : Set G) :=
    le_inf inf_le_left (inf_le_right.trans hO_cent)
  haveI : (A ⊓ O).IsFiniteRelIndex A := Subgroup.isFiniteRelIndex_of_finiteIndex
  have hle1 : (A ⊓ Subgroup.centralizer (Y : Set G)).relIndex A ≤ (A ⊓ O).relIndex A :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero)
      (Subgroup.relIndex_dvd_of_le_left A hAO_le)
  have hAO_N : A ≤ Subgroup.normalizer (O : Set G) := hAR.trans hO_normal
  have hsecond := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
    (H := A) (K := O) hAO_N).2
  have hmul := Subgroup.relIndex_mul_relIndex O (A ⊔ O) R le_sup_right
    (sup_le hAR hO_le_R)
  haveI : O.IsFiniteRelIndex R := Subgroup.isFiniteRelIndex_of_finiteIndex
  have hleO : O.relIndex (A ⊔ O) ≤ O.relIndex R :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero)
      ⟨(A ⊔ O).relIndex R, hmul.symm⟩
  have hle2 : (A ⊓ O).relIndex A ≤ 2 := by
    rw [← hsecond]
    exact hleO.trans hrelO
  have hoff := offender_index_le_of_isMaxElemAbelian hA hYR hYea
  have hrelAY : (Y ⊓ Subgroup.centralizer (A : Set G)).relIndex Y ≤ 2 :=
    hoff.trans (hle1.trans hle2)
  have hcard1 := Subgroup.relIndex_mul_card
    (H := Y ⊓ Subgroup.centralizer (A : Set G)) (K := Y)
  have hinf : (Y ⊓ Subgroup.centralizer (A : Set G)) ⊓ Y =
      Y ⊓ Subgroup.centralizer (A : Set G) := inf_eq_left.mpr inf_le_left
  rw [hinf] at hcard1
  have hCA : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le (by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact haA)
  have hcard_le : Nat.card ↥(Y ⊓ Subgroup.centralizer (A : Set G)) ≤
      Nat.card ↥(Y ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.card_le_of_le (le_inf inf_le_left (inf_le_right.trans hCA))
  calc Nat.card Y = (Y ⊓ Subgroup.centralizer (A : Set G)).relIndex Y *
        Nat.card ↥(Y ⊓ Subgroup.centralizer (A : Set G)) := hcard1.symm
    _ ≤ 2 * Nat.card ↥(Y ⊓ Subgroup.centralizer ({a} : Set G)) :=
        Nat.mul_le_mul hrelAY hcard_le

private theorem exists_maxElemAbelian_not_le {R O : Subgroup G}
    (h : ¬ CFSG.Quasithin.thompsonJ R ≤ O) :
    ∃ A : Subgroup G, CFSG.Quasithin.IsMaxElemAbelian R A ∧ ¬ A ≤ O := by
  by_contra hall
  apply h
  rw [CFSG.Quasithin.thompsonJ]
  exact iSup₂_le fun A hA => by
    by_contra hAO
    exact hall ⟨A, hA, hAO⟩

private theorem CaseOneCtx.centralizer_join_inter_J_le_oTwoZStar
    {M H E Q J R T : Subgroup G} (c : CaseOneCtx G M H E Q J R T)
    (hnot : ¬ J ≤ Subgroup.centralizer (joinOmega J R : Set G)) :
    Subgroup.centralizer (joinOmega J R : Set G) ⊓ J ≤ oTwoZStar J := by
  have hX_NC : J ⊔ R ≤ Subgroup.normalizer
      (Subgroup.centralizer (joinOmega J R : Set G) : Set G) :=
    le_normalizer_centralizer_of_le_normalizer (join_le_normalizer_joinOmega J R)
  refine IsKComp.le_oTwoZStar_of_normal c.choice.isKComp inf_le_right ?_ ?_
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    exact (le_inf ((le_sup_left : J ≤ J ⊔ R).trans hX_NC) Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  · intro heq
    apply hnot
    intro j hj
    have : j ∈ Subgroup.centralizer (joinOmega J R : Set G) ⊓ J := heq.symm ▸ hj
    exact (Subgroup.mem_inf.mp this).1

private theorem CaseOneCtx.mem_ker_jBarAct_of_mem_centralizer
    {M H E Q J R T : Subgroup G} (c : CaseOneCtx G M H E Q J R T)
    (hNcy : Subgroup.centralizer (joinOmega J R : Set G) ⊓ J ≤ oTwoZStar J) :
    ∀ z : G, z ∈ (J ⊔ R) ⊓ Subgroup.centralizer (joinOmega J R : Set G) →
      ∀ hzN : z ∈ Subgroup.normalizer (J : Set G),
        (⟨z, hzN⟩ : ↥(Subgroup.normalizer (J : Set G))) ∈ (jBarAct J).ker := by
  have hcommC := commutator_centralizer_le (join_le_normalizer_joinOmega J R)
  have hXleN : J ⊔ R ≤ Subgroup.normalizer (J : Set G) :=
    sup_le Subgroup.le_normalizer c.R_le_normalizer_J
  intro z hz hzN
  obtain ⟨hzX, hzC⟩ := Subgroup.mem_inf.mp hz
  refine mem_ker_jBarAct_of_commutator_le (J := J) (x := ⟨z, hzN⟩) ?_
  intro g hg
  have hgX : g ∈ J ⊔ R := (le_sup_left : J ≤ J ⊔ R) hg
  have hcommC' : z * g * z⁻¹ * g⁻¹ ∈ Subgroup.centralizer (joinOmega J R : Set G) :=
    hcommC (Subgroup.commutator_mem_commutator hzC hgX)
  have hcommJ : z * g * z⁻¹ * g⁻¹ ∈ J :=
    (Subgroup.le_normalizer_iff_commutator_le_right.mp hXleN)
      (Subgroup.commutator_mem_commutator hzX hg)
  exact hNcy (Subgroup.mem_inf.mpr ⟨hcommC', hcommJ⟩)

private theorem CaseOneCtx.exists_pow_twelve_mem_centralizer_not_mem_ker
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M)
    {A : Subgroup G} (hA : CFSG.Quasithin.IsMaxElemAbelian R A) {a : G}
    (haA : a ∈ A) (haO : a ∉ CFSG.Open.pCoreOf 2 (J ⊔ R))
    (haN : a ∈ Subgroup.normalizer (J : Set G)) :
    ∃ g : ↥(Subgroup.normalizer (J : Set G)), (g : G) ∈ J ∧
      (a * (g : G) * a * (g : G)⁻¹) ^ 12 ∈
        Subgroup.centralizer (joinOmega J R : Set G) ∧
      (jBarAct J (⟨a, haN⟩ * g * ⟨a, haN⟩ * g⁻¹)) ^ 12 ≠ 1 := by
  have hjoin := c.joinStructure h142
  have hO_le_R : CFSG.Open.pCoreOf 2 (J ⊔ R) ≤ R := hjoin.2.1
  have hrelO : (CFSG.Open.pCoreOf 2 (J ⊔ R)).relIndex R ≤ 2 := hjoin.2.2.1
  have hiffO := hjoin.2.2.2
  have hO_cent := pCoreOf_join_le_centralizer_joinOmega J R
  have hXO : J ⊔ R ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (J ⊔ R) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _
  have hRO : R ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (J ⊔ R) : Set G) :=
    (le_sup_right : R ≤ J ⊔ R).trans hXO
  have hYR : joinOmega J R ≤ R :=
    (CFSG.Quasithin.A4.omegaOneCenterOf_le _).trans hO_le_R
  have hcard_a := card_le_two_mul_centralizer_of_offender hA hA.1 hYR
    (isElemAbelian_joinOmega J R) hO_le_R hO_cent hRO hrelO haA haO
  have hbne : jBarAct J ⟨a, haN⟩ ≠ 1 := by
    intro h1
    exact haO ((hiffO ⟨a, haN⟩ (hA.1 haA)).mpr h1)
  obtain ⟨g, hgJ, hg12⟩ := (c.jBarAct_R h142).2 ⟨a, haN⟩ (hA.1 haA) hbne
  have hhX : (g : G) ∈ J ⊔ R := (le_sup_left : J ≤ J ⊔ R) hgJ
  have hhY : (g : G) ∈ Subgroup.normalizer (joinOmega J R : Set G) :=
    join_le_normalizer_joinOmega J R hhX
  have haY : a ∈ Subgroup.normalizer (joinOmega J R : Set G) :=
    join_le_normalizer_joinOmega J R ((le_sup_right : R ≤ J ⊔ R) (hA.1 haA))
  have hfY : (g : G) * a * (g : G)⁻¹ ∈
      Subgroup.normalizer (joinOmega J R : Set G) :=
    (Subgroup.normalizer (joinOmega J R : Set G)).mul_mem
      ((Subgroup.normalizer (joinOmega J R : Set G)).mul_mem hhY haY)
      ((Subgroup.normalizer (joinOmega J R : Set G)).inv_mem hhY)
  have hYmap : (joinOmega J R).map (MulAut.conj (g : G)).toMonoidHom = joinOmega J R :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hhY
  have hcard_le_f := card_centralizer_conj_le (Y := joinOmega J R) (a := a) (h := (g : G)) hYmap
  have hcard_f : Nat.card (joinOmega J R) ≤ 2 * Nat.card ↥((joinOmega J R) ⊓
      Subgroup.centralizer ({(g : G) * a * (g : G)⁻¹} : Set G)) :=
    hcard_a.trans (Nat.mul_le_mul le_rfl hcard_le_f)
  have hpow := CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1.pow_twelve_mem_centralizer
    (isElemAbelian_joinOmega J R) haY hfY hcard_a hcard_f
  have hpow' : (a * (g : G) * a * (g : G)⁻¹) ^ 12 ∈
      Subgroup.centralizer (joinOmega J R : Set G) := by
    simpa [mul_assoc] using hpow
  exact ⟨g, hgJ, hpow', hg12⟩

private theorem CaseOneCtx.thompsonJ_le_pCoreOf_join_of_not_centralizes
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M)
    (hnot : ¬ J ≤ Subgroup.centralizer (joinOmega J R : Set G)) :
    CFSG.Quasithin.thompsonJ R ≤ CFSG.Open.pCoreOf 2 (J ⊔ R) := by
  by_contra hthom
  obtain ⟨A, hA, hAO⟩ := exists_maxElemAbelian_not_le hthom
  obtain ⟨a, haA, haO⟩ := Set.not_subset.mp hAO
  have hjoin := c.joinStructure h142
  have hXleN : J ⊔ R ≤ Subgroup.normalizer (J : Set G) :=
    sup_le Subgroup.le_normalizer c.R_le_normalizer_J
  have haN : a ∈ Subgroup.normalizer (J : Set G) := c.R_le_normalizer_J (hA.1 haA)
  obtain ⟨g, hgJ, hpow, hne⟩ :=
    c.exists_pow_twelve_mem_centralizer_not_mem_ker h142 hA haA haO haN
  have hNcy := c.centralizer_join_inter_J_le_oTwoZStar hnot
  have hker := c.mem_ker_jBarAct_of_mem_centralizer hNcy
  have hhX : (g : G) ∈ J ⊔ R := (le_sup_left : J ≤ J ⊔ R) hgJ
  have hwX : a * (g : G) * a * (g : G)⁻¹ ∈ J ⊔ R :=
    (J ⊔ R).mul_mem ((J ⊔ R).mul_mem ((J ⊔ R).mul_mem
      ((le_sup_right : R ≤ J ⊔ R) (hA.1 haA)) hhX)
      ((le_sup_right : R ≤ J ⊔ R) (hA.1 haA))) ((J ⊔ R).inv_mem hhX)
  have hwCX : (a * (g : G) * a * (g : G)⁻¹) ^ 12 ∈
      (J ⊔ R) ⊓ Subgroup.centralizer (joinOmega J R : Set G) :=
    Subgroup.mem_inf.mpr ⟨(J ⊔ R).pow_mem hwX 12, hpow⟩
  have hker12 : jBarAct J ⟨(a * (g : G) * a * (g : G)⁻¹) ^ 12,
      hXleN (Subgroup.mem_inf.mp hwCX).1⟩ = 1 := hker _ hwCX _
  have hw12 : (jBarAct J ⟨a * (g : G) * a * (g : G)⁻¹, hXleN hwX⟩) ^ 12 = 1 := by
    rw [← map_pow]
    simpa using hker12
  have hweq : jBarAct J ⟨a * (g : G) * a * (g : G)⁻¹, hXleN hwX⟩ =
      jBarAct J (⟨a, haN⟩ * g * ⟨a, haN⟩ * g⁻¹) := by
    apply congrArg (jBarAct J)
    apply Subtype.ext
    rfl
  rw [hweq] at hw12
  exact hne hw12

private theorem CaseOneCtx.exists_char_case_b
    {M H E Q J R T : Subgroup G} (c : CaseOneCtx G M H E Q J R T)
    (h142 : FourteenTwoCaseOneAt M)
    (hnot : ¬ J ≤ Subgroup.centralizer (joinOmega J R : Set G)) :
    ∃ C : Subgroup G, C ≠ ⊥ ∧ IsPGroup 2 C ∧
      Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (C : Set G) ∧
      J ≤ Subgroup.normalizer (C : Set G) := by
  have hthom := c.thompsonJ_le_pCoreOf_join_of_not_centralizes h142 hnot
  have hO_le_R : CFSG.Open.pCoreOf 2 (J ⊔ R) ≤ R := (c.joinStructure h142).2.1
  have hXO : J ⊔ R ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (J ⊔ R) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _
  refine ⟨CFSG.Quasithin.thompsonJ R, ?_, ?_, ?_, ?_⟩
  · exact CFSG.Quasithin.thompsonJ_ne_bot_of_isPGroup c.R_max.2.1 c.R_ne_bot
  · exact c.R_max.2.1.to_le (CFSG.Quasithin.thompsonJ_le_self R)
  · exact CFSG.Quasithin.normalizer_le_normalizer_thompsonJ R
  · have heq : CFSG.Quasithin.thompsonJ (CFSG.Open.pCoreOf 2 (J ⊔ R)) =
        CFSG.Quasithin.thompsonJ R :=
      CFSG.Quasithin.B6.thompsonJ_eq_of_le hthom hO_le_R
    have h : J ⊔ R ≤ Subgroup.normalizer
        (CFSG.Quasithin.thompsonJ (CFSG.Open.pCoreOf 2 (J ⊔ R)) : Set G) :=
      hXO.trans (CFSG.Quasithin.normalizer_le_normalizer_thompsonJ _)
    rw [heq] at h
    exact (le_sup_left : J ≤ J ⊔ R).trans h

theorem CaseOneCtx.exists_char
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M) :
    ∃ C : Subgroup G, C ≠ ⊥ ∧ IsPGroup 2 C ∧
      Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (C : Set G) ∧
      J ≤ Subgroup.normalizer (C : Set G) := by
  by_cases hcentral : J ≤ Subgroup.centralizer (joinOmega J R : Set G)
  · exact c.exists_char_case_a hcentral
  · exact c.exists_char_case_b h142 hcentral

theorem CaseOneCtx.normalizer_R_le
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M)
    (h143 : FourteenThreeCaseOneAt M) : Subgroup.normalizer (R : Set G) ≤ H := by
  obtain ⟨C, hCne, hC2, hNRC, hJC⟩ := c.exists_char h142
  have hNC2 : IsTwoLocal (Subgroup.normalizer (C : Set G)) := ⟨C, hCne, hC2, rfl⟩
  obtain ⟨N, hNmax, hNCN⟩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_le_maxTwoLocal
      (Subgroup.normalizer (C : Set G)) hNC2
  have hJN : J ≤ N := hJC.trans hNCN
  have hQN : Q ≤ N := c.R_max.2.2.1.trans (hNRC.trans hNCN)
  have hNH : N = H := h143 H E Q J c.choice c.typeA N hNmax hJN hQN
  exact hNRC.trans (hNH ▸ hNCN)

theorem CaseOneCtx.isMaxInvariantTwoIn_top
    {M H E Q J R T : Subgroup G} (c : CaseOneCtx G M H E Q J R T)
    (h142 : FourteenTwoCaseOneAt M) (h143 : FourteenThreeCaseOneAt M) :
    CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.IsMaxInvariantTwoIn Q R ⊤ := by
  refine ⟨le_top, c.R_max.2.1, c.R_max.2.2.1, ?_⟩
  intro S hSle hS2 hQS hRS
  rcases eq_or_lt_of_le hRS with heq | hlt
  · exact heq.symm
  · exfalso
    have hltN := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.lt_normalizer_inf_of_isPGroup
      hS2 hRS hlt
    have hQNS : Q ≤ Subgroup.normalizer
        ((Subgroup.normalizer (R : Set G) ⊓ S : Subgroup G) : Set G) := by
      intro q hq
      have hRmap : (Subgroup.normalizer (R : Set G)).map
          (MulAut.conj q).toMonoidHom = Subgroup.normalizer (R : Set G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp
          (Subgroup.le_normalizer (c.R_max.2.2.1 hq))
      have hSmap : S.map (MulAut.conj q).toMonoidHom = S :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQS hq)
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      change (Subgroup.normalizer (R : Set G) ⊓ S).map
        (MulAut.conj q).toMonoidHom = Subgroup.normalizer (R : Set G) ⊓ S
      rw [Subgroup.map_inf _ _ _ (MulAut.conj q).injective, hRmap, hSmap]
    have hHle : Subgroup.normalizer (R : Set G) ⊓ S ≤ H :=
      inf_le_left.trans (c.normalizer_R_le h142 h143)
    have h2 : IsPGroup 2 ↥(Subgroup.normalizer (R : Set G) ⊓ S) :=
      hS2.to_le inf_le_right
    have heq' := c.R_max.2.2.2 (Subgroup.normalizer (R : Set G) ⊓ S) hHle h2 hQNS hltN.le
    exact hltN.ne heq'.symm

private theorem CaseOneCtx.exists_invariant_sylow_sup_pPrimeCore_M_R
    {M H E Q J R T : Subgroup G} (c : CaseOneCtx G M H E Q J R T) :
    ∃ S : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 2 S
        (CFSG.inSubgroup (CFSG.pPrimeCore 3) M ⊔ R) ∧
      R ≤ S ∧ Q ≤ Subgroup.normalizer (S : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let D : Subgroup G := CFSG.inSubgroup (CFSG.pPrimeCore 3) M
  have hDM : D ≤ M := Subgroup.map_subtype_le _
  have hMD : M ≤ Subgroup.normalizer (D : Set G) := by
    intro m hm
    exact CFSG.ABGLocalTools.mem_normalizer_map_subtype_of_characteristic
      (M := M) (C := CFSG.pPrimeCore 3 ↥M) (d := m) (Subgroup.le_normalizer hm)
  have hQD : Q ≤ Subgroup.normalizer (D : Set G) :=
    (c.choice.Q_le_M c.nine).trans hMD
  have hQDR : Q ≤ Subgroup.normalizer ((D ⊔ R : Subgroup G) : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQD hq),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (c.R_max.2.2.1 hq)]
  have hD3' : ¬ 3 ∣ Nat.card D := by
    rw [show Nat.card D = Nat.card (CFSG.pPrimeCore 3 ↥M) from
      Subgroup.card_map_of_injective M.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hR3' : ¬ 3 ∣ Nat.card R :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup c.R_max.2.1 Nat.prime_three (by norm_num)
  have hRN_D : R ≤ Subgroup.normalizer (D : Set G) := c.R_le_M.trans hMD
  have hcardsup :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := R) (K := D) hRN_D
  have hcop : ¬ 3 ∣ Nat.card (D ⊔ R : Subgroup G) := by
    intro h3
    have h3' : 3 ∣ Nat.card (R ⊔ D : Subgroup G) := by simpa [sup_comm] using h3
    have hdvd : 3 ∣ Nat.card R * Nat.card D := by
      rw [← hcardsup]
      exact dvd_mul_of_dvd_left h3' _
    rcases (Nat.prime_three.dvd_mul).mp hdvd with h | h
    · exact hR3' h
    · exact hD3' h
  obtain ⟨S, hSsylow, hRS, hQS⟩ :=
    CFSG.ABGLocalTools.exists_invariant_isSylowOf_ge_of_coprime
      Nat.prime_three Nat.prime_two c.choice.sylow.isPGroup hQDR hcop
      (le_sup_right : R ≤ (D ⊔ R : Subgroup G)) c.R_max.2.1 c.R_max.2.2.1
  exact ⟨S, hSsylow, hRS, hQS⟩

theorem CaseOneCtx.isSylowOf_T_inf_D
    {M H E Q J R T : Subgroup G} (c : CaseOneCtx G M H E Q J R T)
    (h142 : FourteenTwoCaseOneAt M) (h143 : FourteenThreeCaseOneAt M) :
    CFSG.ABGLocalTools.IsSylowOf 2
      (T ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M)
      (CFSG.inSubgroup (CFSG.pPrimeCore 3) M) := by
  let D : Subgroup G := CFSG.inSubgroup (CFSG.pPrimeCore 3) M
  obtain ⟨S, hSsylow, hRS, hQS⟩ := c.exists_invariant_sylow_sup_pPrimeCore_M_R
  have hDM : D ≤ M := Subgroup.map_subtype_le _
  have hMD : M ≤ Subgroup.normalizer (D : Set G) := by
    intro m hm
    exact CFSG.ABGLocalTools.mem_normalizer_map_subtype_of_characteristic
      (M := M) (C := CFSG.pPrimeCore 3 ↥M) (d := m) (Subgroup.le_normalizer hm)
  have hSR : S = R :=
    (c.isMaxInvariantTwoIn_top h142 h143).2.2.2 S le_top hSsylow.isPGroup hQS hRS
  have hRsylow : CFSG.ABGLocalTools.IsSylowOf 2 R (D ⊔ R : Subgroup G) := hSR ▸ hSsylow
  have hKND : (D ⊔ R : Subgroup G) ≤ Subgroup.normalizer (D : Set G) :=
    (sup_le hDM c.R_le_M).trans hMD
  have hRD : CFSG.ABGLocalTools.IsSylowOf 2 (R ⊓ D) D :=
    hRsylow.inf_of_le_normalizer (le_sup_left : D ≤ (D ⊔ R : Subgroup G)) hKND
  have hleTD : R ⊓ D ≤ T ⊓ D :=
    le_inf (inf_le_left.trans c.R_le_T) inf_le_right
  have hTD2 : IsPGroup 2 ↥(T ⊓ D) := c.T_sylow.isPGroup.to_le inf_le_left
  have hTD : T ⊓ D = R ⊓ D := hRD.eq_of_le hleTD inf_le_right hTD2
  rw [hTD]
  exact hRD

theorem CaseOneCtx.fourteenSevenData
    {M H E Q J R T : Subgroup G} (c : CaseOneCtx G M H E Q J R T)
    (h142 : FourteenTwoCaseOneAt M) (h143 : FourteenThreeCaseOneAt M) :
    FourteenSevenData M H Q R T :=
  { normalizer_T_not_le := c.normalizer_T_not_le
    sylow_D := c.isSylowOf_T_inf_D h142 h143
    normalizer_R_le := c.normalizer_R_le h142 h143
    maxInv := c.isMaxInvariantTwoIn_top h142 h143 }

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
