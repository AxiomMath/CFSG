module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.StepSeven

import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.LemmaF
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBlockTransferHyp
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15O1218
import CFSG.Quasithin.Background.C58Push

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

namespace HypCGen

variable {M : Subgroup G} {A H : Subgroup G}

theorem exists_char_normal_of_l34_sup_pCoreOf
    (h : HypCGen G M 3 A H) (hC3 : CaseThree M H)
    (hTwo : KTwoComponentAt M) (hK : KNormalAt M) (hAK : A ≤ kSub 3 M H) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M)) :
    ∃ D : Subgroup G, D ≠ ⊥ ∧ D ≤ CFSG.Open.pCoreOf 2 (A ⊔ T) ∧
      (D.subgroupOf (CFSG.Open.pCoreOf 2 (A ⊔ T))).Characteristic ∧
      kSub 3 M H ≤ Subgroup.normalizer (D : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup G := kSub 3 M H
  let R : Subgroup G := CFSG.Open.pCoreOf 2 (A ⊔ T)
  let X : Subgroup G := K ⊔ R
  have hKH : K ≤ H := kSub_le 3 M H
  have hAH : A ≤ H := hAK.trans hKH
  have hTH : T ≤ H := hT.le.trans inf_le_left
  have hTM : T ≤ M := hT.le.trans inf_le_right
  have hATH : A ⊔ T ≤ H := sup_le hAH hTH
  have hRH : R ≤ H := (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 (A ⊔ T)).trans hATH
  have hKX : K ≤ X := le_sup_left
  have hRX : R ≤ X := le_sup_right
  have hXH : X ≤ H := sup_le hKH hRH
  have hRp : IsPGroup 2 R :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (A ⊔ T)
  have hcharH : CFSG.QuasithinUnique.CharTwo H := h.cstar.charTwo H h.isTwoLocal
  have hO2HleAT : CFSG.Open.pCoreOf 2 H ≤ A ⊔ T :=
    (h.pCoreOf_two_le_of_isSylowOf hT).trans le_sup_right
  have hATO2H : A ⊔ T ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 H : Set G) :=
    sup_le (hAH.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H))
      (hTH.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H))
  have hO2HleR : CFSG.Open.pCoreOf 2 H ≤ R :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hO2HleAT hATO2H
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
  have hcharX : CFSG.QuasithinUnique.CharTwo X :=
    CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hcharH hXH (hO2HleR.trans hRX)
  have hcharTop : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup ↥X) :=
    CFSG.QuasithinUnique.Setup.Lift.charTwo_top hcharX
  have hXO2 : X ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hTH.trans (hK 3 A H h)
  have hTR : T ≤ Subgroup.normalizer (R : Set G) :=
    le_sup_right.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (A ⊔ T))
  have hTX : T ≤ Subgroup.normalizer (X : Set G) :=
    (le_inf hTK hTR).trans (Subgroup.inf_normalizer_le_normalizer_sup K R)
  have hTO2X : T ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    hTX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have hAO2X : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    (hAK.trans hKX).trans hXO2
  have hATO2X : A ⊔ T ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    sup_le hAO2X hTO2X
  have hO2XleT : CFSG.Open.pCoreOf 2 X ≤ T := by
    have hO2XHM : CFSG.Open.pCoreOf 2 X ≤ H ⊓ M :=
      le_inf (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 X |>.trans hXH)
        (h.invariant_two_le_M
          (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X)
          (hAK.trans hKX |>.trans hXO2))
    have hsupP : IsPGroup 2 (CFSG.Open.pCoreOf 2 X ⊔ T : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left'
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X) hT.isPGroup hTO2X
    have hsupLe : (CFSG.Open.pCoreOf 2 X ⊔ T : Subgroup G) ≤ H ⊓ M := sup_le hO2XHM hT.le
    have heq : (CFSG.Open.pCoreOf 2 X ⊔ T : Subgroup G) = T :=
      hT.eq_of_le le_sup_right hsupLe hsupP
    exact le_sup_left.trans heq.le
  have hO2XleR : CFSG.Open.pCoreOf 2 X ≤ R :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hO2XleT.trans le_sup_right) hATO2X
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X)
  let K' : Subgroup ↥X := K.subgroupOf X
  let R' : Subgroup ↥X := R.subgroupOf X
  have hK'normal : K'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr (hXH.trans (hK 3 A H h))
  have hR'p : IsPGroup 2 R' := hRp.comap_subtype
  have hK'R'sup : K' ⊔ R' = ⊤ := by
    have hsup := Subgroup.subgroupOf_sup hKX hRX
    rw [show K ⊔ R = X from rfl, Subgroup.subgroupOf_self] at hsup
    exact hsup.symm
  have hO2R' : CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥X) ≤ R' := by
    intro x hx
    have hxmap : (x : G) ∈ (CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥X)).map X.subtype :=
      Subgroup.mem_map_of_mem _ hx
    rw [CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_map_subtype 2 X ⊤,
      CFSG.QuasithinUnique.Setup.Lift.map_top_subtype] at hxmap
    exact hO2XleR hxmap
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
    exists_char_normal_of_l34 hcharTop hR'p hO2R' hK'normal hK'R'sup hK'odd hK'L
  refine ⟨D'.map X.subtype, ?_, ?_, ?_, ?_⟩
  · intro hbot
    apply hD'ne
    rw [eq_bot_iff]
    intro x hx
    have hxmap : (x : G) ∈ D'.map X.subtype := Subgroup.mem_map_of_mem _ hx
    rw [hbot] at hxmap
    exact Subtype.ext (by simpa using hxmap)
  · have hmap : (D'.map X.subtype) ≤ R'.map X.subtype := Subgroup.map_mono hD'le
    rwa [Subgroup.map_subgroupOf_eq_of_le hRX] at hmap
  ·
    let eR : ↥R' ≃* ↥R := Subgroup.subgroupOfEquivOfLe hRX
    have hDsub : (D'.subgroupOf R').map eR.toMonoidHom =
        (D'.map X.subtype).subgroupOf R := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mp hx))
      · intro hy
        have hyD : (y : G) ∈ D'.map X.subtype := Subgroup.mem_subgroupOf.mp hy
        obtain ⟨x, hxD, hxy⟩ := Subgroup.mem_map.mp hyD
        have hxR : x ∈ R' := by
          rw [Subgroup.mem_subgroupOf]
          have hxy' : (x : G) = (y : G) := by simpa using hxy
          rw [hxy']
          exact y.2
        refine ⟨⟨x, hxR⟩, Subgroup.mem_subgroupOf.mpr hxD, ?_⟩
        apply Subtype.ext
        exact hxy
    have hchar := CFSG.Quasithin.C58.characteristic_map_mulEquiv hD'char eR
    rwa [hDsub] at hchar
  ·
    have hXnorm : X ≤ Subgroup.normalizer (D'.map X.subtype : Set G) :=
      CFSG.subgroup_le_normalizer_of_conj_mem (D'.map X.subtype) X (fun r d hd => by
        obtain ⟨d', hd', rfl⟩ := Subgroup.mem_map.mp hd
        exact Subgroup.mem_map_of_mem _ (hD'normal.conj_mem d' hd' r))
    exact hKX.trans hXnorm

theorem normalizer_pCoreOf_sup_le
    (h : HypCGen G M 3 A H) (hC3 : CaseThree M H) (hTwo : KTwoComponentAt M)
    (hK : KNormalAt M) (hL : PLayerNotLeAt M) (hU : KSubLeKSubAt M) (hAK : A ≤ kSub 3 M H)
    (hmax : ∀ H₁ ∈ H2StarFam M A, kSub 3 M H ≤ kSub 3 M H₁ → kSub 3 M H₁ = kSub 3 M H)
    {T : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M)) :
    Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) ≤ H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R : Subgroup G := CFSG.Open.pCoreOf 2 (A ⊔ T)
  obtain ⟨D, hDne, hDR, hDchar, hKD⟩ :=
    h.exists_char_normal_of_l34_sup_pCoreOf hC3 hTwo hK hAK hT
  have hDp : IsPGroup 2 D :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (A ⊔ T)).to_le hDR
  have hDloc : IsTwoLocal (Subgroup.normalizer (D : Set G)) := ⟨D, hDne, hDp, rfl⟩
  obtain ⟨N, hNmax, hDN⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.O1218Proof.exists_maxTwoLocal_ge hDloc
  have hKM : ¬ kSub 3 M H ≤ M :=
    not_kSub_le_of_not_pLayerIn_le (p := 3) (hL 3 A H h)
  have hND : N = H :=
    h.eq_of_isMaxTwoLocal_of_le_kSub hC3 hTwo hK hU hAK hKM hmax hNmax (hKD.trans hDN)
  have hNT :=
    CFSG.section9_normalizer_le_normalizer_map_subtype_of_characteristic R (D.subgroupOf R)
  have hDRmap : ((D.subgroupOf R).map R.subtype : Subgroup G) = D :=
    Subgroup.map_subgroupOf_eq_of_le hDR
  rw [hDRmap] at hNT
  exact hNT.trans (hDN.trans hND.le)

end HypCGen

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
