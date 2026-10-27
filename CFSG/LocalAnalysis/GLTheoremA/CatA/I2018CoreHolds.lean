module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018CoreField
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1952
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2265
public import Certificates.Certificate2266
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate3951
public import Certificates.Certificate8032
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate8080
public import Certificates.Certificate8081
public import Certificates.Certificate8117
public import Certificates.Certificate10050
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate17002
public import Certificates.Certificate17951
public import Certificates.Certificate18000
public import Certificates.Certificate19953
import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3U48
import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3G2
import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3Bender
import CFSG.LocalAnalysis.GLTheoremA.CatA.TD4LeParab
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FD4SParity
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Center
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge
import CFSG.LocalAnalysis.SeitzReduction.CrossChar
import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct
import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
import CFSG.Blueprint.LieModelAPI
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Facts
import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
import CFSG.Models.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2018Core

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S10 (twoPart)

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)


private theorem two_pow_lt_twoPart {N n : ℕ} (hn : n ≠ 0) (h : 2 ^ (N + 1) ∣ n) : 2 ^ N < twoPart n := by
  have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn).1 h
  unfold twoPart
  calc 2 ^ N < 2 ^ (N + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    _ ≤ 2 ^ n.factorization 2 := Nat.pow_le_pow_right (by norm_num) hle

private theorem isPGroup_pCoreOf {S : Type} [Group S] (P : Subgroup S) : IsPGroup 2 (pCoreOf 2 P) :=
  CFSG.pCore_isPGroup.map P.subtype

private theorem le_normalizer_pCoreOf {S : Type} [Group S] (p : ℕ) (P : Subgroup S) :
    P ≤ Subgroup.normalizer (pCoreOf p P : Set S) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · rintro ⟨u₀, hu₀, rfl⟩
    exact ⟨⟨x, hx⟩ * u₀ * (⟨x, hx⟩ : ↥P)⁻¹, CFSG.pCore_normal.conj_mem u₀ hu₀ ⟨x, hx⟩, by simp⟩
  · rintro ⟨v₀, hv₀, hv⟩
    refine ⟨(⟨x, hx⟩ : ↥P)⁻¹ * v₀ * ⟨x, hx⟩, ?_, ?_⟩
    · have := CFSG.pCore_normal.conj_mem v₀ hv₀ (⟨x, hx⟩ : ↥P)⁻¹
      simpa using this
    · have hv' : (v₀ : S) = x * u * x⁻¹ := hv
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hv']
      group

private theorem fixSubgroup_one' {S : Type} [Group S] :
    CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (1 : MulAut S) = ⊤ := by
  ext x
  simp only [Subgroup.mem_top, iff_true]
  exact CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup.2 rfl

private theorem eq_top_of_glaPComponent_top {S : Type} [Group S] [Finite S] [IsSimpleGroup S] {J : Subgroup S}
    (hJ : GLAPComponent 3 ⊤ J) : J = ⊤ := by
  rcases CFSG.Open.IsSubnormal.eq_bot_or_top hJ.2.1 with h | h
  · exfalso
    have hQ := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ
    haveI := hQ.2.toNontrivial
    have hsub : Subsingleton (PQuot 3 J) := by
      subst h
      refine ⟨fun a b => ?_⟩
      induction a using QuotientGroup.induction_on with | H a => ?_
      induction b using QuotientGroup.induction_on with | H b => ?_
      rw [Subsingleton.elim a b]
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (PQuot 3 J ⧸ Subgroup.center (PQuot 3 J))
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    exact hxy (congrArg _ (Subsingleton.elim x y))
  · exact h

private theorem card_pSimple_dvd' {G : Type} [Group G] [Finite G] (J : Subgroup G) :
    Nat.card (PSimple 3 J) ∣ Nat.card J :=
  (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _)

private theorem surjective_pSimple {G : Type} [Group G] (J : Subgroup G) :
    ∃ f : ↥J →* PSimple 3 J, Function.Surjective f :=
  ⟨(QuotientGroup.mk' (Subgroup.center (PQuot 3 J))).comp (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)),
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)⟩

private theorem isList93_of_isU3eight {Q : Type} [Group Q] (h : catalogIs Q S9.isU3eight) :
    catalogIs Q (S9.isList93 3) := by
  obtain ⟨q, hv, hq8, he⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isU3eight h
  have hp2 := (primePower_eq_of_card_eq Nat.prime_two (by norm_num : 0 < 3) (hq8.trans (by norm_num))).1
  refine ⟨.lie ⟨.twistedA 2 q, hv⟩, Or.inr ⟨rfl, ?_⟩, he⟩
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (show S9.isU3char2 (.lie ⟨.twistedA 2 q, hv⟩) from ⟨hp2, by rw [hq8]⟩))))))))

section Certs


private theorem card_of_isU3eight {Q : Type} [Group Q] [Finite Q] (h : catalogIs Q S9.isU3eight) :
    Nat.card Q = 5515776 := by
  obtain ⟨q, hv, hq8, he⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isU3eight h
  rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.twistedA 2 q, hv⟩ Q he]
  show orderTwistedA 2 q.card = 5515776
  rw [hq8]
  decide

private theorem card_of_isL3four {Q : Type} [Group Q] [Finite Q] (h : catalogIs Q S9.isL3four) :
    Nat.card Q = 20160 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [S9.isL3four, onLie] at hi
  | alternating n hn => simp [S9.isL3four, onLie] at hi
  | sporadic s => simp [S9.isL3four, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨d, hv⟩ Q ⟨e⟩]
    cases d with
    | A n q =>
      rcases n with _ | _ | _ | n
      · simp [S9.isL3four, onLie] at hi
      · simp [S9.isL3four, onLie] at hi
      · have h4 : q.card = 4 := by simpa [S9.isL3four, onLie] using hi
        show orderA 2 q.card = 20160
        rw [h4]
        decide
      · simp [S9.isL3four, onLie] at hi
    | _ => simp [S9.isL3four, onLie] at hi

private theorem false_of_core3Group {S : Type} [Group S] [Finite S] (hC : I137C3.Core3Group S)
    {P T J : Subgroup S} (hTP : T ≤ pCoreOf 2 P) (hT : T ≠ ⊥) (hJP : J ≤ P)
    (hU : catalogIs (PSimple 3 J) S9.isU3eight) : False := by
  have hne : pCoreOf 2 P ≠ ⊥ := fun h => hT (le_bot_iff.1 (h ▸ hTP))
  have hL := hC (pCoreOf 2 P) J (isPGroup_pCoreOf P) hne (hJP.trans (le_normalizer_pCoreOf 2 P))
    (PSimple 3 J) (surjective_pSimple J) (isList93_of_isU3eight hU)
  have h1 := card_of_isU3eight hU
  have h2 := card_of_isL3four hL
  omega

private theorem card_le_of_ambiguousChev {S : Type} [Group S] [Finite S] (h : catalogIs S (ambiguousChev 2)) :
    Nat.card S ≤ 20160 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [ambiguousChev] at hi
  | sporadic s => simp [ambiguousChev] at hi
  | alternating n hn =>
    have hn' : n = 5 ∨ n = 6 ∨ n = 8 := by
      simp only [ambiguousChev] at hi
      omega
    rw [CFSG.LocalAnalysis.GLTheoremA.CatDistinct.card_alternating_of_iso hn e]
    rcases hn' with rfl | rfl | rfl <;> decide
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    have hord := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨d, hv⟩ S ⟨e⟩
    rw [hord]
    cases d with
    | A n q =>
      rcases n with _ | _ | n
      · simp [ambiguousChev] at hi
      · have h7 : q.card = 7 := by
          simp only [ambiguousChev] at hi
          omega
        show orderA 1 q.card ≤ 20160
        rw [h7]
        decide
      · simp [ambiguousChev] at hi
    | twistedA n q =>
      rcases n with _ | _ | _ | _ | n
      · simp [ambiguousChev] at hi
      · simp [ambiguousChev] at hi
      · have h3 : q.card = 3 := by
          simp only [ambiguousChev] at hi
          omega
        show orderTwistedA 2 q.card ≤ 20160
        rw [h3]
        decide
      · simp [ambiguousChev] at hi
      · simp [ambiguousChev] at hi
    | _ => simp [ambiguousChev] at hi

private theorem td4_eight_false {S : Type} [Group S] [Finite S] {q : PrimePower}
    (hv : (LieTypeIndex.trialityD4 q).Valid) (hq : q.p = 2) (hq3 : q.exponent = 3)
    (e : S ≃* ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) {P T J : Subgroup S}
    (hTP : T ≤ pCoreOf 2 P) (hT : T ≠ ⊥) (hJP : J ≤ P) (hJd : 5515776 ∣ Nat.card J) : False := by
  open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
  have hm : CFSG.Blueprint.LieModel S .trialityD4 0 2 3 := by
    have h := lieModel_specOf ⟨.trialityD4 q, hv⟩ (by simpa using hq) e
    simpa [specOf, hq3] using h
  have htw : CFSG.Blueprint.TwistedChevalleyModel S .D4 (2 ^ 3) := by
    rcases hm with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨M, _, _, σ, hM, hσ, ⟨eM⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two (by norm_num) htw
  have hM3 : Nat.card M = (2 ^ 3) ^ 3 := hM
  have hstd : TD4Le.Std 3 M σ := ⟨by norm_num, hM3, Or.inl hσ⟩
  set U := pCoreOf 2 P with hU
  have hUne : U ≠ ⊥ := fun h => hT (le_bot_iff.1 (h ▸ hTP))
  have hU'ne : U.map eM.toMonoidHom ≠ ⊥ := by
    rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ eM.injective]
  obtain ⟨g, Js, hJs, R, -, -, -, -, hNP⟩ :=
    TD4Le.borelTits_normalized σ hstd (U.map eM.toMonoidHom) hU'ne
      ((isPGroup_pCoreOf P).map eM.toMonoidHom)
  have hJN : (J.map eM.toMonoidHom).map (MulAut.conj g).toMonoidHom ≤
      (CFSG.LieType.Chevalley.graphFixedParabolic TwistTag.D4 M σ.toRingHom Js).subgroupOf
        (CFSG.LieType.Chevalley.graphFixedRootGroup TwistTag.D4 M σ.toRingHom) := by
    refine le_trans (Subgroup.map_mono ?_) hNP
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono (hJP.trans (le_normalizer_pCoreOf 2 P))
  have hPle := CFSG.LieType.Chevalley.graphFixedParabolic_le TwistTag.D4 M σ.toRingHom Js
  have hcardJ : Nat.card J ∣
      Nat.card (CFSG.LieType.Chevalley.graphFixedParabolic TwistTag.D4 M σ.toRingHom Js) := by
    have h1 := Subgroup.card_dvd_of_le hJN
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective eM.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv] at h1
    exact h1
  have hC := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_root_eq_borel_mul_D4 σ Nat.prime_two
    (by norm_num : 1 ≤ 3) hM3 hσ
  have hS := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.trialityD4 q, hv⟩ S ⟨e⟩
  have hq8 : q.card = 8 := by rw [PrimePower.card_def, hq, hq3]; norm_num
  have hSM : Nat.card S = Nat.card (CFSG.LieType.Chevalley.graphFixedRootGroup TwistTag.D4 M σ.toRingHom) :=
    Nat.card_congr eM.toEquiv
  have hB : Nat.card (CFSG.LieType.Chevalley.graphFixedRootBorel TwistTag.D4 M σ.toRingHom) =
      2 ^ 36 * 3577 := by
    have h1 : Nat.card S = orderTrialityD4 8 := by rw [hS]; show orderTrialityD4 q.card = _; rw [hq8]
    rw [hSM, hC] at h1
    have h2 : orderTrialityD4 8 = (2 ^ 36 * 3577) *
        ((1 + (2 ^ 3) ^ 3) * ((1 + (2 ^ 3) ^ 4 + (2 ^ 3) ^ 8) * (1 + 2 ^ 3))) := by decide
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h1
  rcases TD4Le.eq_empty_or_singleton_of_ne_univ hJs with rfl | ⟨a, rfl⟩
  · rw [CFSG.LieType.Chevalley.graphFixedParabolic_empty, hB] at hcardJ
    exact absurd (hJd.trans hcardJ) (by decide)
  · rw [CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_parabolic_singleton_D4 σ Nat.prime_two
      (by norm_num : 1 ≤ 3) hM3 hσ a, hB] at hcardJ
    have hd := hJd.trans hcardJ
    rcases TwistTag.D4.card_orbit a with h1 | h3
    · rw [h1] at hd
      exact absurd hd (by decide)
    · rw [h3] at hd
      exact absurd hd (by decide)

private theorem twoPart_card_of_lieModel {S : Type} [Group S] {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n f : ℕ}
    (hm : CFSG.Blueprint.LieModel S t n 2 f) :
    twoPart (@Nat.card S) = 2 ^ (CFSG.ComponentClassification.CatLeaf.lieSylowExponent t n * f) := by
  unfold twoPart
  rw [(CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput S t n 2 f hm.admissible hm).2.2]

private theorem bound_of_field {S : Type} [Group S] [Finite S] (d : ValidLieTypeIndex) (hd : d.1.characteristic = 2)
    (e : S ≃* d.Group) {P T J : Subgroup S} (hTP : T ≤ pCoreOf 2 P) (hT : T ≠ ⊥) (hJP : J ≤ P)
    (hU : catalogIs (PSimple 3 J) S9.isU3eight) (hbig : 5515776 < Nat.card S) (h19 : 19 ∣ Nat.card S)
    (h29 : 2 ^ 9 ∣ Nat.card S)
    (hf : (specOf d.1).2.2 ∣ 3 ∨
      ((specOf d.1).1 = .PSU ∧ (specOf d.1).2.1 = 3 ∧ (specOf d.1).2.2 = 9)) :
    ((specOf d.1).2.2 = 1 ∧ 2 ^ 6 < twoPart (Nat.card S)) ∨
      ((specOf d.1).2.2 = 3 ∧ 2 ^ 18 < twoPart (Nat.card S)) := by
  have hpos : Nat.card S ≠ 0 := Nat.card_pos.ne'
  have h2 := twoPart_card_of_lieModel (lieModel_specOf d hd e)
  have hcore : I137C3.Core3Group S → False := fun C => false_of_core3Group C hTP hT hJP hU
  have hord := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds d S ⟨e⟩
  obtain ⟨d, hv⟩ := d
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  rcases hf with h3 | ⟨hPSU, hn3, hf9⟩
  · rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h1 | h3'
    · exact Or.inl ⟨h1, two_pow_lt_twoPart hpos ((pow_dvd_pow 2 (by norm_num)).trans h29)⟩
    · refine Or.inr ⟨h3', ?_⟩
      rw [h2, h3']
      have hbigN : ∀ N : ℕ, 7 ≤ N → 2 ^ 18 < 2 ^ (N * 3) := fun N hN =>
        Nat.pow_lt_pow_right (by norm_num) (by omega)
      cases d with
      | A r q =>
        have hq : q.p = 2 := by simpa using hd
        have he3 : q.exponent = 3 := h3'
        have hq8 : q.card = 8 := by rw [PrimePower.card_def, hq, he3]; norm_num
        have hS : Nat.card S = orderA r 8 := by rw [hord]; show orderA r q.card = _; rw [hq8]
        rcases (show r = 1 ∨ r = 2 ∨ r = 3 ∨ 4 ≤ r by omega) with rfl | rfl | rfl | hr4
        · rw [hS] at hbig; exact absurd hbig (by decide)
        · rw [hS] at h19; exact absurd h19 (by decide)
        · rw [hS] at h19; exact absurd h19 (by decide)
        · refine hbigN _ ?_
          show 7 ≤ (r + 1) * (r + 1 - 1) / 2
          have : 20 ≤ (r + 1) * r := by nlinarith
          rw [Nat.add_sub_cancel]
          omega
      | twistedA r q =>
        have hq : q.p = 2 := by simpa using hd
        have he3 : q.exponent = 3 := h3'
        have hq8 : q.card = 8 := by rw [PrimePower.card_def, hq, he3]; norm_num
        rcases (show r = 2 ∨ r = 3 ∨ 4 ≤ r by omega) with rfl | rfl | hr4
        · have hS : Nat.card S = orderTwistedA 2 8 := by
            rw [hord]; show orderTwistedA 2 q.card = _; rw [hq8]
          rw [hS] at hbig; exact absurd hbig (by decide)
        · exact (hcore (I137C3.core3At_U4eight ⟨.twistedA 3 q, hv⟩ ⟨q, rfl, hq8⟩ S ⟨e⟩)).elim
        · refine hbigN _ ?_
          show 7 ≤ (r + 1) * (r + 1 - 1) / 2
          have : 20 ≤ (r + 1) * r := by nlinarith
          rw [Nat.add_sub_cancel]
          omega
      | B r q =>
        have hq : q.p = 2 := by simpa using hd
        have he3 : q.exponent = 3 := h3'
        have hq8 : q.card = 8 := by rw [PrimePower.card_def, hq, he3]; norm_num
        rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
        · have hS : Nat.card S = orderBC 2 8 := by rw [hord]; show orderBC 2 q.card = _; rw [hq8]
          rw [hS] at h19; exact absurd h19 (by decide)
        · refine hbigN _ ?_
          show 7 ≤ r ^ 2
          nlinarith
      | C r q =>
        have hq : q.p = 2 := by simpa using hd
        exact absurd hq hr.2
      | D r q =>
        refine hbigN _ ?_
        show 7 ≤ r * (r - 1)
        have : 4 ≤ r := hr
        have : 3 ≤ r - 1 := by omega
        nlinarith
      | twistedD r q =>
        refine hbigN _ ?_
        show 7 ≤ r * (r - 1)
        have : 4 ≤ r := hr
        have : 3 ≤ r - 1 := by omega
        nlinarith
      | E6 q => exact hbigN _ (by show 7 ≤ 36; norm_num)
      | E7 q => exact hbigN _ (by show 7 ≤ 63; norm_num)
      | E8 q => exact hbigN _ (by show 7 ≤ 120; norm_num)
      | F4 q => exact hbigN _ (by show 7 ≤ 24; norm_num)
      | G2 q =>
        have hq : q.p = 2 := by simpa using hd
        have he3 : q.exponent = 3 := h3'
        have hq8 : q.card = 8 := by rw [PrimePower.card_def, hq, he3]; norm_num
        exact (hcore (I137C3.core3At_G2eight ⟨.G2 q, hv⟩ ⟨q, rfl, hq8⟩ S ⟨e⟩)).elim
      | twistedE6 q => exact hbigN _ (by show 7 ≤ 36; norm_num)
      | trialityD4 q => exact hbigN _ (by show 7 ≤ 12; norm_num)
      | suzuki m =>
        have hm1 : m = 1 := by
          have : 2 * m + 1 = 3 := h3'
          omega
        subst hm1
        have hS : Nat.card S = orderSuzuki (2 ^ (2 * 1 + 1)) := hord
        rw [hS] at hbig; exact absurd hbig (by decide)
      | reeG2 m => exact absurd hd (by simp)
      | reeF4 a => exact hbigN _ (by show 7 ≤ 12; norm_num)
      | tits =>
        have : (1 : ℕ) = 3 := h3'
        omega
  ·
    exfalso
    cases d with
    | twistedA r q =>
      have hr2 : r = 2 := by
        have : r + 1 = 3 := hn3
        omega
      subst hr2
      have hq : q.p = 2 := by simpa using hd
      exact hcore (I137C3.core3At_U3two ⟨.twistedA 2 q, hv⟩ ⟨q, rfl, hq⟩ S ⟨e⟩)
    | A r q => exact absurd hPSU (by simp [specOf])
    | B r q => exact absurd hPSU (by simp [specOf])
    | C r q => exact absurd hPSU (by simp [specOf])
    | D r q => exact absurd hPSU (by simp [specOf])
    | twistedD r q => exact absurd hPSU (by simp [specOf])
    | E6 q => exact absurd hPSU (by simp [specOf])
    | E7 q => exact absurd hPSU (by simp [specOf])
    | E8 q => exact absurd hPSU (by simp [specOf])
    | F4 q => exact absurd hPSU (by simp [specOf])
    | G2 q => exact absurd hPSU (by simp [specOf])
    | twistedE6 q => exact absurd hPSU (by simp [specOf])
    | trialityD4 q => exact absurd hPSU (by simp [specOf])
    | suzuki m => exact absurd hPSU (by simp [specOf])
    | reeG2 m => exact absurd hPSU (by simp [specOf])
    | reeF4 a => exact absurd hPSU (by simp [specOf])
    | tits => exact absurd hPSU (by simp [specOf])

private theorem not_td4 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (d : ValidLieTypeIndex) (hd : d.1.characteristic = 2) (e : S ≃* d.Group)
    {α : MulAut S} (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) {P T J : Subgroup S} (hTP : T ≤ pCoreOf 2 P)
    (hT : T ≠ ⊥) (hJP : J ≤ P)
    (hJ : GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) J)
    (hU : catalogIs (PSimple 3 J) S9.isU3eight) (hJd : 5515776 ∣ Nat.card J) (h19 : 19 ∣ Nat.card S)
    (h29 : 2 ^ 9 ∣ Nat.card S) (q' : PrimePower) (hv' : (LieTypeIndex.trialityD4 q').Valid)
    (e' : S ≃* ValidLieTypeIndex.Group ⟨.trialityD4 q', hv'⟩) : False := by
  have hpos : Nat.card S ≠ 0 := Nat.card_pos.ne'
  have h9 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).1 h29
  by_cases hq2 : q'.p = 2
  · obtain ⟨-, -, -, -, hf⟩ :=
      field_bound hS hna ⟨.trialityD4 q', hv'⟩ (by simpa using hq2) e' hα3 hα1 hJ hU
    rcases hf with h3 | ⟨h, -⟩
    · have h3' : q'.exponent ∣ 3 := h3
      rcases (Nat.dvd_prime Nat.prime_three).1 h3' with h1 | h3''
      · have hq'2 : q'.card = 2 := by rw [PrimePower.card_def, hq2, h1]; norm_num
        have hS2 : Nat.card S = orderTrialityD4 2 := by
          rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.trialityD4 q', hv'⟩ S ⟨e'⟩]
          show orderTrialityD4 q'.card = _
          rw [hq'2]
        rw [hS2] at h19
        exact absurd h19 (by decide)
      · exact td4_eight_false hv' hq2 h3'' e' hTP hT hJP hJd
    · exact absurd h (by simp [specOf])
  ·
    obtain ⟨t, n, p, f, hp, hL⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.exists_lieModel_char ⟨.trialityD4 q', hv'⟩
    have hLX : CFSG.Models.LieModel S t n p f := CFSG.Models.LieModel.of_mulEquiv e'.symm hL
    have hBX : CFSG.Blueprint.LieModel S t n p f :=
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models hLX
    have hpq : p = q'.p := by simpa using hp
    have hodd : CFSG.Blueprint.OddLieType S :=
      ⟨t, n, p, f, hpq ▸ q'.prime_p, hpq ▸ hq2, hBX.admissible, hBX⟩
    have hm := lieModel_specOf d hd e
    have hfact := (CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput S _ _ 2 _
      hm.admissible hm).2.2
    rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType
        CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hm hodd with
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
    · rw [h1, h2, h3] at hfact
      simp only [CFSG.ComponentClassification.CatLeaf.lieSylowExponent] at hfact
      omega

theorem i2018ChevCore_holds : I2018.I2018ChevCore := by
  intro S _ _ hS hna hχ α hα3 P hP T hTP hT J hJ hJP hU
  haveI := hS
  have hU8 := card_of_isU3eight hU
  have hJd : 5515776 ∣ Nat.card J := hU8 ▸ card_pSimple_dvd' J
  have hJS : Nat.card J ∣ Nat.card S := Subgroup.card_subgroup_dvd_card J
  have h19 : 19 ∣ Nat.card S := (by norm_num : 19 ∣ 5515776).trans (hJd.trans hJS)
  have h29 : 2 ^ 9 ∣ Nat.card S := (by norm_num : 2 ^ 9 ∣ 5515776).trans (hJd.trans hJS)
  have hPlt : Nat.card P < Nat.card S :=
    lt_of_le_of_ne (Subgroup.card_le_card_group P)
      (fun h => hP ((Subgroup.card_eq_iff_eq_top P).1 h))
  have hbig : 5515776 < Nat.card S :=
    lt_of_le_of_lt (Nat.le_of_dvd Nat.card_pos (hJd.trans (Subgroup.card_dvd_of_le hJP))) hPlt
  have hα1 : α ≠ 1 := by
    rintro rfl
    rw [fixSubgroup_one'] at hJ
    exact hP (top_le_iff.1 ((eq_top_of_glaPComponent_top hJ) ▸ hJP))
  rcases hχ with ⟨i, hi, ⟨e⟩⟩ | hamb
  · cases i with
    | cyclic p hp => exact False.elim hi
    | alternating n hn => exact False.elim hi
    | sporadic s => exact False.elim hi
    | lie d =>
      have hd : d.1.characteristic = 2 := hi
      refine ⟨fun hT4 => ?_, ?_⟩
      · obtain ⟨i', hi', ⟨e'⟩⟩ := hT4
        cases i' with
        | cyclic p hp => exact False.elim hi'
        | alternating n hn => exact False.elim hi'
        | sporadic s => exact False.elim hi'
        | lie idx =>
          obtain ⟨d', hv'⟩ := idx
          cases d'
          case trialityD4 q' =>
            exact not_td4 hS hna d hd e hα3 hα1 hTP hT hJP hJ hU hJd h19 h29 q' hv' e'
          all_goals exact False.elim hi'
      · obtain ⟨lab, hΛ, hraw, hn, hf⟩ := field_bound hS hna d hd e hα3 hα1 hJ hU
        refine ⟨lab, hΛ, ?_, hraw⟩
        rw [hn]
        exact bound_of_field d hd e hTP hT hJP hU hbig h19 h29 hf
  · exact absurd (card_le_of_ambiguousChev hamb) (by omega)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.I2018Core

end
