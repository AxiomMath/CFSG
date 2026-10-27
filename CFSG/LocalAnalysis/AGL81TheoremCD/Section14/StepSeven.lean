module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KSylowTwo
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CoreTwoL34
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.LemmaF
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34Lift
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFifteenOne
import CFSG.LocalAnalysis.AGL81TheoremC.CoprimeGamma
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15O1218
import CFSG.Quasithin.Background.InternalSecB56
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBlockTransferHyp
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
import CFSG.Quasithin.Background.C58Push

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

@[expose] def KTwoComponentAt (M : Subgroup G) : Prop :=
  ∀ E H : Subgroup G, HypCGen G M 3 E H →
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsTwoPrimeComponentIn (kSub 3 M H) H

@[expose] def KSubLeKSubAt (M : Subgroup G) : Prop :=
  ∀ (E H N : Subgroup G), HypCGen G M 3 E H → E ≤ kSub 3 M H → N ∈ H2StarFam M E →
    kSub 3 M H ≤ N → kSub 3 M H ≤ kSub 3 M N

namespace HypCGen

variable {M : Subgroup G} {E H : Subgroup G}

theorem eq_three {q : ℕ} {E H : Subgroup G} (hpre : PreambleTypes M)
    (h : HypCGen G M q E H) : q = 3 :=
  eq_three_of_mem hpre h.mem_QSet h.mem

theorem mem_H2StarAll (h : HypCGen G M 3 E H) : H ∈ H2StarAll M :=
  ⟨3, E, h.mem_QSet, h.mem⟩

theorem isPerfect_kSub {M E H : Subgroup G} (hC3 : CaseThree M H) :
    Group.IsPerfect ↥(kSub 3 M H) := by
  have hcomp : CFSG.IsPComponent 3 ((kSub 3 M H).subgroupOf (kSub 3 M H)) := hC3.1.2
  haveI : Group.IsPerfect ↥((kSub 3 M H).subgroupOf (kSub 3 M H)) :=
    CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hcomp
  let e := Subgroup.subgroupOfEquivOfLe (le_refl (kSub 3 M H))
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

theorem kSub_eq_closure_odd (h : HypCGen G M 3 E H) (hTwo : KTwoComponentAt M) :
    kSub 3 M H = Subgroup.closure {x : G | x ∈ kSub 3 M H ∧ Odd (orderOf x)} :=
  (hTwo E H h).2.2.2

theorem isQuasisimple_kSub_quotient (h : HypCGen G M 3 E H) (hTwo : KTwoComponentAt M) :
    CFSG.IsQuasisimple (↥(kSub 3 M H) ⧸ CFSG.pCore 2 ↥(kSub 3 M H)) :=
  (hTwo E H h).2.2.1

theorem nonempty_mulEquiv_kSub_quotient_pCore_two
    (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    (hTwo : KTwoComponentAt M) :
    Nonempty ((↥(kSub 3 M H) ⧸ CFSG.pCore 2 ↥(kSub 3 M H)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) :=
  nonempty_mulEquiv_quotient_pCore_two (h.isQuasisimple_kSub_quotient hTwo)
    (HypCGen.nonempty_mulEquiv_threeStar hC3)

theorem isSylowOf_three_E (h : HypCGen G M 3 E H) (hC3 : CaseThree M H) (hEK : E ≤ kSub 3 M H) :
    CFSG.ABGLocalTools.IsSylowOf 3 E (kSub 3 M H) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨A, hA⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 (kSub 3 M H)
  have hA9 : Nat.card A = 9 :=
    card_eq_nine_of_isSylowOf (HypCGen.nonempty_mulEquiv_threeStar hC3) hA
  have hfac : 3 ^ (Nat.card (kSub 3 M H)).factorization 3 = 9 := by
    rw [← hA.card_eq, hA9]
  refine CFSG.ABGLocalTools.isSylowOf_of_card hEK ?_
  rw [h.card, hfac]
  norm_num

theorem invariant_two_le_M (h : HypCGen G M 3 E H) {R : Subgroup G} (hR : IsPGroup 2 R)
    (hER : E ≤ Subgroup.normalizer (R : Set G)) : R ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : ¬ 3 ∣ Nat.card R := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR
    rw [hn]
    intro hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
  have hcard : 3 ^ (1 + 1) ≤ Nat.card E := by
    rw [h.card]
  exact (CFSG.LocalAnalysis.AGL81TheoremC.le_glbCore_of_coprime h.elem hcard hcop hER).trans
    h.gamma

theorem pCoreOf_two_le_M (h : HypCGen G M 3 E H) : CFSG.Open.pCoreOf 2 H ≤ M :=
  h.invariant_two_le_M (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
    (h.E_le_H.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H))

private theorem le_isSylowOf_of_le_normalizer {H M O T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M)) (hOHM : O ≤ H ⊓ M)
    (hOp : IsPGroup 2 O) (hTnorm : T ≤ Subgroup.normalizer (O : Set G)) : O ≤ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsupP : IsPGroup 2 (O ⊔ T : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hOp hT.isPGroup hTnorm
  have hsupLe : (O ⊔ T : Subgroup G) ≤ H ⊓ M := sup_le hOHM hT.le
  have heq : (O ⊔ T : Subgroup G) = T := hT.eq_of_le le_sup_right hsupLe hsupP
  exact le_sup_left.trans heq.le

theorem pCoreOf_two_le_of_isSylowOf (h : HypCGen G M 3 E H) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M)) : CFSG.Open.pCoreOf 2 H ≤ T :=
  le_isSylowOf_of_le_normalizer hT
    (le_inf (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H) h.pCoreOf_two_le_M)
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
    (hT.le.trans (inf_le_left.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H)))

theorem isMaxTwoLocal_of_mem_H2StarFam (h : HypCGen G M 3 E H) {N : Subgroup G}
    (hN : N ∈ H2StarFam M E) : CFSG.Open.IsMaxTwoLocalSubgroup N := by
  haveI := h.cstar.simple
  have hEbot : E ≠ ⊥ := h.E_ne_bot
  have hNloc : IsTwoLocal N :=
    isTwoLocal_of_mem_H2StarFam h.cstar.nonab h.cstar.charTwo hEbot hN
  have hEN : E ≤ N := hN.1.2.1
  have hNM : ¬ N ≤ M := hN.1.2.2.1
  refine ⟨hNloc, fun K hK hNK => ?_⟩
  have hKmem : K ∈ H2Fam M E :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top h.cstar.nonab K hK,
      hEN.trans hNK, fun hKM => hNM (hNK.trans hKM), h.cstar.charTwo K hK⟩
  exact hN.2 K hKmem hNK

theorem pCoreOf_two_kSub_ne_bot_of_quasisimple (h : HypCGen G M 3 E H)
    (hq : CFSG.IsQuasisimple (↥(kSub 3 M H) ⧸ CFSG.pCore 2 ↥(kSub 3 M H)))
    (hHK : H ≤ Subgroup.normalizer (kSub 3 M H : Set G)) :
    CFSG.Open.pCoreOf 2 (kSub 3 M H) ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup G := kSub 3 M H
  have hKH : K ≤ H := kSub_le 3 M H
  have hHnorm : H ≤ Subgroup.normalizer (K : Set G) := hHK
  intro hbot
  have hpc : CFSG.pCore 2 ↥K = ⊥ := by
    have hmap : (CFSG.pCore 2 ↥K).map K.subtype = ⊥ := by
      simpa [K, CFSG.Open.pCoreOf] using hbot
    exact Subgroup.map_injective K.subtype_injective (by rw [Subgroup.map_bot]; exact hmap)
  have e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hpc).trans QuotientGroup.quotientBot
  have hqs : CFSG.IsQuasisimple ↥K :=
    CFSG.IsQuasisimple.of_mulEquiv e.symm hq
  have hchar : CFSG.QuasithinUnique.CharTwo H := h.cstar.charTwo H h.isTwoLocal
  have hleF : K ≤ CFSG.Open.quasithinGenFitting H :=
    CFSG.Quasithin.InternalSec.le_quasithinGenFitting_of_normal hKH
      (fun x hx k hk => (Subgroup.mem_normalizer_iff.mp (hHnorm hx) k).mp hk) hqs
  have hF : CFSG.Open.quasithinGenFitting H = CFSG.Open.pCoreOf 2 H :=
    (CFSG.Quasithin.quasithinGenFitting_eq_pCoreOf_iff H 2).mpr hchar
  have hleP : K ≤ CFSG.Open.pCoreOf 2 H := by
    rw [← hF]
    exact hleF
  have hKp : IsPGroup 2 K :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H).to_le hleP
  haveI : Group.IsPerfect ↥K := hqs.1
  haveI : Nontrivial ↥K := by
    have hsimple := hqs.2.1
    exact (QuotientGroup.mk'_surjective (Subgroup.center ↥K)).nontrivial
  haveI : Group.IsNilpotent ↥K := hKp.isNilpotent
  exact Group.IsPerfect.not_isNilpotent ↥K inferInstance

theorem eq_normalizer_kSub_of_quasisimple (h : HypCGen G M 3 E H)
    (hq : CFSG.IsQuasisimple (↥(kSub 3 M H) ⧸ CFSG.pCore 2 ↥(kSub 3 M H)))
    (hHK : H ≤ Subgroup.normalizer (kSub 3 M H : Set G)) :
    Subgroup.normalizer (kSub 3 M H : Set G) = H := by
  let K : Subgroup G := kSub 3 M H
  have hO2ne : CFSG.Open.pCoreOf 2 K ≠ ⊥ :=
    h.pCoreOf_two_kSub_ne_bot_of_quasisimple hq hHK
  have hKN : Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K
  have hloc : IsTwoLocal (Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G)) :=
    ⟨CFSG.Open.pCoreOf 2 K, hO2ne,
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 K, rfl⟩
  have hmax := h.isMaxTwoLocal_of_mem_H2StarFam h.mem
  have hNH : Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) = H :=
    hmax.2 _ hloc (hHK.trans hKN)
  refine le_antisymm ?_ hHK
  calc Subgroup.normalizer (K : Set G)
      ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) := hKN
    _ = H := hNH

theorem eq_normalizer_kSub (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    (hTwo : KTwoComponentAt M) (hK : KNormalAt M) :
    Subgroup.normalizer (kSub 3 M H : Set G) = H :=
  h.eq_normalizer_kSub_of_quasisimple (h.isQuasisimple_kSub_quotient hTwo) (hK 3 E H h)

theorem exists_char_normal_of_l34_sup_sylow
    (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    (hTwo : KTwoComponentAt M) (hK : KNormalAt M) (hEK : E ≤ kSub 3 M H) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M)) :
    ∃ D : Subgroup G, D ≠ ⊥ ∧ D ≤ T ∧ (D.subgroupOf T).Characteristic ∧
      kSub 3 M H ≤ Subgroup.normalizer (D : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup G := kSub 3 M H
  let X : Subgroup G := K ⊔ T
  have hKH : K ≤ H := kSub_le 3 M H
  have hTH : T ≤ H := hT.le.trans inf_le_left
  have hTX : T ≤ X := le_sup_right
  have hKX : K ≤ X := le_sup_left
  have hXH : X ≤ H := sup_le hKH hTH
  have hcharH : CFSG.QuasithinUnique.CharTwo H := h.cstar.charTwo H h.isTwoLocal
  have hcharX : CFSG.QuasithinUnique.CharTwo X :=
    CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hcharH hXH
      (h.pCoreOf_two_le_of_isSylowOf hT |>.trans le_sup_right)
  have hcharTop : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup ↥X) :=
    CFSG.QuasithinUnique.Setup.Lift.charTwo_top hcharX
  have hO2Xinv : E ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    (hEK.trans hKX).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X)
  have hO2XleT : CFSG.Open.pCoreOf 2 X ≤ T :=
    le_isSylowOf_of_le_normalizer hT
      (le_inf (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 X |>.trans hXH)
        (h.invariant_two_le_M
          (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X) hO2Xinv))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X)
      (hTX.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X))
  let K' : Subgroup ↥X := K.subgroupOf X
  let T' : Subgroup ↥X := T.subgroupOf X
  have hK'normal : K'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr (hXH.trans (hK 3 E H h))
  have hT'p : IsPGroup 2 T' := hT.isPGroup.comap_subtype
  have hK'T'sup : K' ⊔ T' = ⊤ := by
    have hsup := Subgroup.subgroupOf_sup hKX hTX
    rw [show K ⊔ T = X from rfl, Subgroup.subgroupOf_self] at hsup
    exact hsup.symm
  have hO2T' : CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥X) ≤ T' := by
    intro x hx
    have hxmap : (x : G) ∈ (CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥X)).map X.subtype :=
      Subgroup.mem_map_of_mem _ hx
    rw [CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_map_subtype 2 X ⊤,
      CFSG.QuasithinUnique.Setup.Lift.map_top_subtype] at hxmap
    exact hO2XleT hxmap
  have hK'odd : K' = Subgroup.closure {x : ↥X | x ∈ K' ∧ Odd (orderOf x)} := by
    apply Subgroup.map_injective X.subtype_injective
    have hKoddG : K = Subgroup.closure {y : G | y ∈ K ∧ Odd (orderOf y)} :=
      h.kSub_eq_closure_odd hTwo
    rw [Subgroup.map_subgroupOf_eq_of_le hKX, MonoidHom.map_closure, hKoddG]
    congr 1
    ext y
    constructor
    · rintro ⟨hyK, hyodd⟩
      exact ⟨⟨y, hKX hyK⟩, ⟨hyK, by simpa using hyodd⟩, rfl⟩
    · rintro ⟨x, ⟨hxK, hxodd⟩, rfl⟩
      exact ⟨hxK, by simpa using hxodd⟩
  have hK'L : Nonempty ((↥K' ⧸ CFSG.pCore 2 ↥K') ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) := by
    obtain ⟨e⟩ := h.nonempty_mulEquiv_kSub_quotient_pCore_two hC3 hTwo
    let eK : ↥K' ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKX
    have hcore : (CFSG.pCore 2 ↥K').map eK.toMonoidHom = CFSG.pCore 2 ↥K :=
      CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 eK
    exact ⟨(QuotientGroup.congr (CFSG.pCore 2 ↥K') (CFSG.pCore 2 ↥K) eK hcore).trans e⟩
  obtain ⟨D', hD'ne, hD'le, hD'char, hD'normal⟩ :=
    exists_char_normal_of_l34 hcharTop hT'p hO2T' hK'normal hK'T'sup hK'odd hK'L
  refine ⟨D'.map X.subtype, ?_, ?_, ?_, ?_⟩
  · intro hbot
    apply hD'ne
    rw [eq_bot_iff]
    intro x hx
    have hxmap : (x : G) ∈ D'.map X.subtype := Subgroup.mem_map_of_mem _ hx
    rw [hbot] at hxmap
    exact Subtype.ext (by simpa using hxmap)
  · have hmap : (D'.map X.subtype) ≤ T'.map X.subtype := Subgroup.map_mono hD'le
    rwa [Subgroup.map_subgroupOf_eq_of_le hTX] at hmap
  ·
    let eT : ↥T' ≃* ↥T := Subgroup.subgroupOfEquivOfLe hTX
    have hDsub : (D'.subgroupOf T').map eT.toMonoidHom =
        (D'.map X.subtype).subgroupOf T := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mp hx))
      · intro hy
        have hyD : (y : G) ∈ D'.map X.subtype := Subgroup.mem_subgroupOf.mp hy
        obtain ⟨x, hxD, hxy⟩ := Subgroup.mem_map.mp hyD
        have hxT : x ∈ T' := by
          rw [Subgroup.mem_subgroupOf]
          have hxy' : (x : G) = (y : G) := by simpa using hxy
          rw [hxy']
          exact y.2
        refine ⟨⟨x, hxT⟩, Subgroup.mem_subgroupOf.mpr hxD, ?_⟩
        apply Subtype.ext
        exact hxy
    have hchar := CFSG.Quasithin.C58.characteristic_map_mulEquiv hD'char eT
    rwa [hDsub] at hchar
  ·
    have hXnorm : X ≤ Subgroup.normalizer (D'.map X.subtype : Set G) :=
      CFSG.subgroup_le_normalizer_of_conj_mem (D'.map X.subtype) X (fun r d hd => by
        obtain ⟨d', hd', rfl⟩ := Subgroup.mem_map.mp hd
        exact Subgroup.mem_map_of_mem _ (hD'normal.conj_mem d' hd' r))
    exact hKX.trans hXnorm

theorem mem_H2StarFam_of_isMaxTwoLocal (h : HypCGen G M 3 E H) {K N : Subgroup G}
    (hEK : E ≤ K) (hKM : ¬ K ≤ M) (hN : CFSG.Open.IsMaxTwoLocalSubgroup N) (hKN : K ≤ N) :
    N ∈ H2StarFam M E := by
  haveI := h.cstar.simple
  have hEbot : E ≠ ⊥ := h.E_ne_bot
  have hNmem : N ∈ H2Fam M E :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top h.cstar.nonab N hN.1,
      hEK.trans hKN, fun hNM => hKM (hKN.trans hNM),
      h.cstar.charTwo N hN.1⟩
  refine ⟨hNmem, fun N' hN' hNN' => ?_⟩
  have hO2ne : CFSG.Open.pCoreOf 2 N' ≠ ⊥ := by
    intro hbot
    have hcharN' := hN'.2.2.2
    rw [hbot] at hcharN'
    have htop : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
      rw [Subgroup.centralizer_eq_top_iff_subset]
      intro x hx
      have hx1 : x = 1 := by simpa using hx
      simp [hx1]
    rw [htop, inf_top_eq] at hcharN'
    exact hEbot (le_bot_iff.mp (hN'.2.1.trans hcharN'))
  have hloc : IsTwoLocal (Subgroup.normalizer (CFSG.Open.pCoreOf 2 N' : Set G)) :=
    ⟨CFSG.Open.pCoreOf 2 N', hO2ne,
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 N', rfl⟩
  have hNle : N ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 N' : Set G) :=
    hNN'.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 N')
  have heq : Subgroup.normalizer (CFSG.Open.pCoreOf 2 N' : Set G) = N :=
    hN.2 _ hloc hNle
  exact le_antisymm
    ((CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 N').trans
      heq.le) hNN'

theorem eq_of_isMaxTwoLocal_of_le_kSub (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    (hTwo : KTwoComponentAt M) (hK : KNormalAt M) (hU : KSubLeKSubAt M)
    (hEK : E ≤ kSub 3 M H) (hKM : ¬ kSub 3 M H ≤ M)
    (hmaxE : ∀ H₁ ∈ H2StarFam M E, kSub 3 M H ≤ kSub 3 M H₁ →
      kSub 3 M H₁ = kSub 3 M H)
    {N : Subgroup G} (hN : CFSG.Open.IsMaxTwoLocalSubgroup N)
    (hKN : kSub 3 M H ≤ N) : N = H := by
  have hNstar : N ∈ H2StarFam M E := mem_H2StarFam_of_isMaxTwoLocal h hEK hKM hN hKN
  have hKL : kSub 3 M H ≤ kSub 3 M N := hU E H N h hEK hNstar hKN
  have heqK : kSub 3 M N = kSub 3 M H := hmaxE N hNstar hKL
  have hdataN : HypCGen G M 3 E N := { h with mem := hNstar }
  have hLnorm : N ≤ Subgroup.normalizer (kSub 3 M H : Set G) := by
    rw [← heqK]
    exact hK 3 E N hdataN
  have hNH : N ≤ H := hLnorm.trans (h.eq_normalizer_kSub hC3 hTwo hK).le
  exact (hN.2 H h.isTwoLocal hNH).symm

theorem normalizer_sylow_le_of_max
    (h3 : ∀ H ∈ H2StarAll M, CaseThree M H)
    (hTwo : KTwoComponentAt M) (hK : KNormalAt M) (hL : PLayerNotLeAt M)
    (hU : KSubLeKSubAt M) (h : HypCGen G M 3 E H) (hEK : E ≤ kSub 3 M H)
    (hmaxE : ∀ H₁ ∈ H2StarFam M E, kSub 3 M H ≤ kSub 3 M H₁ →
      kSub 3 M H₁ = kSub 3 M H) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M)) :
    Subgroup.normalizer (T : Set G) ≤ H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC3 : CaseThree M H := h3 H h.mem_H2StarAll
  obtain ⟨D, hDne, hDT, hDchar, hKD⟩ :=
    h.exists_char_normal_of_l34_sup_sylow hC3 hTwo hK hEK hT
  have hDp : IsPGroup 2 D := hT.isPGroup.to_le hDT
  have hDloc : IsTwoLocal (Subgroup.normalizer (D : Set G)) := ⟨D, hDne, hDp, rfl⟩
  obtain ⟨N, hNmax, hDN⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.O1218Proof.exists_maxTwoLocal_ge hDloc
  have hKM : ¬ kSub 3 M H ≤ M :=
    not_kSub_le_of_not_pLayerIn_le (p := 3) (hL 3 E H h)
  have hND : N = H :=
    h.eq_of_isMaxTwoLocal_of_le_kSub hC3 hTwo hK hU hEK hKM hmaxE hNmax (hKD.trans hDN)
  have hNT :=
    CFSG.section9_normalizer_le_normalizer_map_subtype_of_characteristic T (D.subgroupOf T)
  have hDTmap : ((D.subgroupOf T).map T.subtype : Subgroup G) = D :=
    Subgroup.map_subgroupOf_eq_of_le hDT
  rw [hDTmap] at hNT
  exact hNT.trans (hDN.trans hND.le)

end HypCGen

variable {M : Subgroup G}

theorem fourteenFifteenNormAt_of_kSubLe
    {M : Subgroup G} (hpre : PreambleTypes M)
    (h3 : ∀ H ∈ H2StarAll M, CaseThree M H) (hTwo : KTwoComponentAt M) (hK : KNormalAt M)
    (hL : PLayerNotLeAt M) (hU : KSubLeKSubAt M) : FourteenFifteenNormAt M := by
  intro q E H hdata hEK hmax T hT
  have hq3 : q = 3 := HypCGen.eq_three hpre hdata
  subst q
  exact HypCGen.normalizer_sylow_le_of_max h3 hTwo hK hL hU hdata hEK hmax hT

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
