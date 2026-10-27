module

public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedFamily
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitGeneral
import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedTransport
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitL219A
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
import CFSG.ClassicalInvolution.Q3.TL4MF163Psl
import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSep
import CFSG.GH74.GLS.C3.Layer1.Th2P72cR13
import CFSG.GroupTheory.InnerCentralizerProjection
import CFSG.GroupTheory.PerfectCentralExtensionUnique
import CFSG.Quasithin.SteinbergCCRankOneSplitting
import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3AutImage
import CFSG.LocalAnalysis.ComponentClassification.GSThmB7NPMatch
import CFSG.Goldschmidt75.B1Steps

public section

namespace CFSG.ComponentClassification.FooteMarked

open CFSG Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_of_isKleinFour {B : Subgroup G} (hB : IsKleinFour ↥B) : IsPGroup 2 B :=
  CFSG.Goldschmidt75.isPGroup_of_isKleinFour hB

theorem orderOf_eq_two_of_isKleinFour {B : Subgroup G} (hB : IsKleinFour ↥B) {b : G}
    (hb : b ∈ B) (hb1 : b ≠ 1) : orderOf b = 2 :=
  CFSG.Goldschmidt75.orderOf_eq_two_of_isKleinFour hB hb hb1

theorem exists_ne_one_of_isKleinFour {B : Subgroup G} (hB : IsKleinFour ↥B) : ∃ b ∈ B, b ≠ 1 := by
  obtain ⟨b, hb, hb1, -⟩ := CFSG.Goldschmidt75.exists_mem_ne_of_isKleinFour hB 1
  exact ⟨b, hb, hb1⟩

theorem fixedShadow_le_fixedShadowAt (K : Subgroup G) {U : Subgroup G} {b : G} (hb : b ∈ U) :
    fixedShadow K U ≤ fixedShadowAt K b := by
  rw [← fixedShadow_zpowers]
  refine le_fixedShadow_of_perfect (fixedShadow_perfect K U) ?_
  refine (fixedShadow_le_inf K U).trans (inf_le_inf_left K ?_)
  exact Subgroup.centralizer_le (Subgroup.zpowers_le.mpr hb)

theorem eq_of_sup_oddCoreIn_eq_of_le_normalizer {K P : Subgroup G} (hK : Group.IsPerfect ↥K)
    (hPK : P ⊔ FooteLit.oddCoreIn K = K)
    (hO : FooteLit.oddCoreIn K ≤ normalizer (P : Set G)) : P = K := by
  exact le_antisymm (hPK ▸ le_sup_left)
    (CFSG.ComponentClassification.HarrisLit.L219.le_of_le_sup_of_odd
      (P := K) (X := P) (N := FooteLit.oddCoreIn K) hK (FooteLit.odd_card_oddCoreIn K) hO hPK.ge)

theorem isQuasisimple_of_oddCoreIn_le_centralizer {J : Subgroup G} (hJ : Group.IsPerfect ↥J)
    (hJs : IsSimpleGroup (↥J ⧸ pPrimeCore 2 ↥J))
    (hJc : FooteLit.oddCoreIn J ≤ centralizer (J : Set G)) : CFSG.IsQuasisimple ↥J := by
  refine CFSG.GH74.GLS.Th2.Obs.isQuasisimple_of_pPrimeCore_le_center hJ hJs ?_
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  have hxJ : (x : G) ∈ FooteLit.oddCoreIn J := Subgroup.mem_map_of_mem J.subtype hx
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hJc hxJ) (y : G) y.2)

theorem exists_isKleinFour_mem_of_orderOf_eq_two {K : Subgroup G}
    (hK : ∃ V : Subgroup G, V ≤ K ∧ IsKleinFour ↥V) {b : G} (hbK : b ∈ K)
    (hb : orderOf b = 2) : ∃ E : Subgroup G, E ≤ K ∧ IsKleinFour ↥E ∧ b ∈ E := by
  obtain ⟨V, hVK, hV⟩ := hK
  have hp2 : 2 ≤ CFSG.Open.pRank 2 K :=
    CFSG.SectionRank.le_pRank (p := 2) (H := K) (E := V) (by norm_num) hVK
      (CFSG.ComponentClassification.Sol76.Sig.isElemAbelian_of_isKleinFour hV)
      (k := 2) (by rw [hV.card_four]; norm_num)
  exact CFSG.ComponentClassification.Sol76.Sig.exists_isKleinFour_mem hp2 hbK hb

theorem exists_isKleinFour_of_footeFamilyType {L : Subgroup G} (hL : FooteLit.FooteFamilyType L) :
    ∃ V : Subgroup (↥L ⧸ Open.fusionZStar L), IsKleinFour ↥V := by
  rcases hL with h | h
  · obtain ⟨e⟩ := h
    have h2 : 2 ≤ CFSG.pRank 2 (↥L ⧸ Open.fusionZStar L) := by
      rw [CFSG.pRank_congr_of_mulEquiv e 2]
      exact CFSG.ComponentClassification.UnbalancedGS.RankSmallSources.two_le_pRank_alternating_seven
    exact CFSG.ComponentClassification.Sol76.exists_isKleinFour_of_two_le_pRank h2
  · obtain ⟨p, f, hp, hp2, hf, hp5, hlm⟩ := h
    obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ :=
      CFSG.ClassicalInvolution.Q3.TL4.MF163.psl2_of_lieModel hlm
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hchar : CharP F p :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hF
    have hF2 : ringChar F ≠ 2 := by
      rw [ringChar.eq F p]
      exact hp2
    have h2 : 2 ≤ CFSG.pRank 2 (↥L ⧸ Open.fusionZStar L) := by
      rw [CFSG.pRank_congr_of_mulEquiv e 2]
      exact CFSG.ComponentClassification.UnbalancedGS.RankSmallSources.two_le_pRank_psl_two hF2
    exact CFSG.ComponentClassification.Sol76.exists_isKleinFour_of_two_le_pRank h2

private theorem oddCoreIn_eq_map (K : Subgroup G) :
    FooteLit.oddCoreIn K = (pPrimeCore 2 ↥K).map K.subtype := rfl

private theorem odd_card_pPrimeCore (K : Subgroup G) : Odd (Nat.card (pPrimeCore 2 ↥K)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥K))

private theorem le_oddCoreIn (K : Subgroup G) : FooteLit.oddCoreIn K ≤ K := by
  rw [oddCoreIn_eq_map]
  exact Subgroup.map_subtype_le _

private theorem subgroupOf_oddCoreIn (K : Subgroup G) :
    (FooteLit.oddCoreIn K).subgroupOf K = pPrimeCore 2 ↥K := by
  refine Subgroup.map_subtype_inj.mp ?_
  rw [Subgroup.subgroupOf_map_subtype, ← oddCoreIn_eq_map]
  exact inf_eq_left.mpr (le_oddCoreIn K)

private theorem subgroupOf_sup_eq_top_of_sup_oddCoreIn_eq {K P : Subgroup G} (hPK : P ≤ K)
    (h : P ⊔ FooteLit.oddCoreIn K = K) : P.subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤ := by
  have h1 : (P ⊔ FooteLit.oddCoreIn K).subgroupOf K = (⊤ : Subgroup ↥K) := by
    rw [h, Subgroup.subgroupOf_self]
  rwa [Subgroup.subgroupOf_sup hPK (le_oddCoreIn K), subgroupOf_oddCoreIn] at h1

theorem exists_isKleinFour_le_of_sup_oddCoreIn {T : Type} [Group T] {K X : Subgroup G}
    (hXK : X ≤ K) (hX : X ⊔ FooteLit.oddCoreIn K = K) (e : ↥K ⧸ pPrimeCore 2 ↥K ≃* T)
    (hT : ∃ V : Subgroup T, IsKleinFour ↥V) : ∃ V : Subgroup G, V ≤ X ∧ IsKleinFour ↥V := by
  obtain ⟨V, hV⟩ := hT
  haveI : Finite T := Finite.of_surjective e e.surjective
  have hEA : IsElementaryAbelian 2 ↥V :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by rw [hV.exponent_two] }
  have hpT : 2 ≤ CFSG.pRank 2 T :=
    CFSG.ComponentClassification.UnbalancedGS.RankSmallSources.two_le_pRank_of_four hEA
      hV.card_four
  have hpQ : 2 ≤ CFSG.pRank 2 (↥K ⧸ pPrimeCore 2 ↥K) := by
    rw [CFSG.pRank_congr_of_mulEquiv e 2]
    exact hpT
  have hKsup : X.subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤ :=
    subgroupOf_sup_eq_top_of_sup_oddCoreIn_eq hXK hX
  have hI : ¬ 2 ∣ Nat.card (X.subgroupOf K ⊓ pPrimeCore 2 ↥K : Subgroup ↥K) := by
    intro h2
    have hdvd : 2 ∣ Nat.card (pPrimeCore 2 ↥K) :=
      h2.trans (Subgroup.card_dvd_of_le inf_le_right)
    exact (odd_card_pPrimeCore K).not_two_dvd_nat hdvd
  have hpXK : 2 ≤ CFSG.pRank 2 ↥(X.subgroupOf K) := by
    rw [← CFSG.Quasithin.SteinbergCC.pRank_quotient_eq_of_sup_eq_top (p := 2) Nat.prime_two
      hKsup hI]
    exact hpQ
  have hpX : 2 ≤ CFSG.pRank 2 ↥X := by
    rw [← CFSG.pRank_congr_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hXK) 2]
    exact hpXK
  obtain ⟨W, hW⟩ := CFSG.ComponentClassification.Sol76.exists_isKleinFour_of_two_le_pRank hpX
  exact ⟨W.map X.subtype, Subgroup.map_subtype_le W,
    CFSG.Quasithin.Fan86.Sigma3.isKleinFour_of_mulEquiv
      (W.equivMapOfInjective X.subtype X.subtype_injective) hW⟩

theorem mem_centralizer_of_mem_coreActionKernel {K P : Subgroup G} {β : G} (hPK : P ≤ K)
    (hP : Group.IsPerfect ↥P) (hPc : FooteLit.oddCoreIn P ≤ centralizer (P : Set G))
    (hβP : β ∈ normalizer (P : Set G)) (hβK : β ∈ UnbalancedLayer.coreActionKernel K) :
    β ∈ centralizer (P : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hβKn, hβKo⟩ := UnbalancedLayer.mem_coreActionKernel.mp hβK
  have hβOn : β ∈ normalizer (FooteLit.oddCoreIn K : Set G) :=
    FooteLit.mem_normalizer_oddCoreIn hβKn
  have hPN : P ≤ normalizer ((P ⊓ FooteLit.oddCoreIn K : Subgroup G) : Set G) := by
    intro p hp
    have h1 : p ∈ normalizer (P : Set G) := Subgroup.le_normalizer hp
    have h2 : p ∈ normalizer (FooteLit.oddCoreIn K : Set G) :=
      FooteLit.mem_normalizer_oddCoreIn (Subgroup.le_normalizer (hPK hp))
    rw [Subgroup.mem_normalizer_iff] at h1 h2
    refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr (h1 x) (h2 x)
  have hsub_le : (P ⊓ FooteLit.oddCoreIn K).subgroupOf P ≤ pPrimeCore 2 ↥P := by
    haveI : ((P ⊓ FooteLit.oddCoreIn K).subgroupOf P).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hPN
    have hodd : Nat.Coprime 2 (Nat.card ((P ⊓ FooteLit.oddCoreIn K).subgroupOf P)) := by
      have hcard : Nat.card ((P ⊓ FooteLit.oddCoreIn K).subgroupOf P) =
          Nat.card (P ⊓ FooteLit.oddCoreIn K : Subgroup G) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
      rw [hcard]
      exact Nat.coprime_two_left.mpr
        ((FooteLit.odd_card_oddCoreIn K).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right))
    exact le_sSup ⟨inferInstance, hodd⟩
  refine CFSG.mem_centralizer_of_commutator_mem_center hP hβP fun j hj => ?_
  have hxO : β * j * β⁻¹ * j⁻¹ ∈ FooteLit.oddCoreIn K := by
    have hB : j * β⁻¹ * j⁻¹ * β ∈ (pPrimeCore 2 ↥K).map K.subtype := by
      simpa using hβKo j⁻¹ (hPK (P.inv_mem hj))
    have hB' : j * β⁻¹ * j⁻¹ * β ∈ FooteLit.oddCoreIn K := by
      rw [oddCoreIn_eq_map]
      exact hB
    have hconj : β * (j * β⁻¹ * j⁻¹ * β) * β⁻¹ ∈ FooteLit.oddCoreIn K :=
      (Subgroup.mem_normalizer_iff.mp hβOn (j * β⁻¹ * j⁻¹ * β)).mp hB'
    rwa [show β * (j * β⁻¹ * j⁻¹ * β) * β⁻¹ = β * j * β⁻¹ * j⁻¹ by group] at hconj
  have hxj : β * j * β⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hβP j).mp hj
  have hxP : β * j * β⁻¹ * j⁻¹ ∈ P := P.mul_mem hxj (P.inv_mem hj)
  have hxin : β * j * β⁻¹ * j⁻¹ ∈ P ⊓ FooteLit.oddCoreIn K := ⟨hxP, hxO⟩
  have hxO' : (⟨β * j * β⁻¹ * j⁻¹, hxP⟩ : ↥P) ∈ pPrimeCore 2 ↥P :=
    hsub_le (Subgroup.mem_subgroupOf.mpr hxin)
  have hxOG : β * j * β⁻¹ * j⁻¹ ∈ FooteLit.oddCoreIn P := by
    rw [oddCoreIn_eq_map]
    exact Subgroup.mem_map_of_mem P.subtype hxO'
  have hxcent : β * j * β⁻¹ * j⁻¹ ∈ centralizer (P : Set G) := hPc hxOG
  have hxcenter : (⟨β * j * β⁻¹ * j⁻¹, hxP⟩ : ↥P) ∈ Subgroup.center ↥P := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxcent (y : G) y.2)
  exact Subgroup.mem_map.mpr ⟨⟨β * j * β⁻¹ * j⁻¹, hxP⟩, hxcenter, rfl⟩

theorem le_of_forall_isKleinFour_le {K X : Subgroup G} (hK : CFSG.IsQuasisimple ↥K)
    (hKs : IsSimpleGroup (↥K ⧸ pPrimeCore 2 ↥K))
    (h4 : ∃ V : Subgroup G, V ≤ K ∧ IsKleinFour ↥V)
    (hX : ∀ V : Subgroup G, V ≤ K → IsKleinFour ↥V → V ≤ X) : K ≤ X := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W : Subgroup G := ⨆ V : {V : Subgroup G // V ≤ K ∧ IsKleinFour ↥V}, (V : Subgroup G)
    with hWdef
  have hWK : W ≤ K := by
    rw [hWdef]
    exact iSup_le fun V => V.2.1
  have hWX : W ≤ X := by
    rw [hWdef]
    exact iSup_le fun V => hX V V.2.1 V.2.2
  have hWnorm : K ≤ normalizer (W : Set G) := by
    intro k hk
    refine CFSG.ComponentClassification.AS76b.mem_normalizer_of_map_conj_le ?_
    rw [hWdef, Subgroup.map_iSup (MulAut.conj k).toMonoidHom]
    refine iSup_le fun V => ?_
    have hVK : (V : Subgroup G).map (MulAut.conj k).toMonoidHom ≤ K := by
      rintro x ⟨v, hv, rfl⟩
      simpa [MulAut.conj_apply] using K.mul_mem (K.mul_mem hk (V.2.1 hv)) (K.inv_mem hk)
    have hV4 : IsKleinFour ↥((V : Subgroup G).map (MulAut.conj k).toMonoidHom) :=
      CFSG.Quasithin.Fan86.Sigma3.isKleinFour_of_mulEquiv
        ((V : Subgroup G).equivMapOfInjective (MulAut.conj k).toMonoidHom
          (MulAut.conj k).injective) V.2.2
    exact le_iSup (fun W : {W : Subgroup G // W ≤ K ∧ IsKleinFour ↥W} => (W : Subgroup G))
      ⟨_, hVK, hV4⟩
  have hWsubN : (W.subgroupOf K).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hWnorm
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hK (N := W.subgroupOf K) hWsubN with
    h | h
  · have hKW : K ≤ W := by
      intro x hx
      have hx' : (⟨x, hx⟩ : ↥K) ∈ W.subgroupOf K := by
        rw [h]
        exact Subgroup.mem_top _
      simpa using Subgroup.mem_subgroupOf.mp hx'
    exact hKW.trans hWX
  · exfalso
    obtain ⟨V, hVK, hV4⟩ := h4
    have hVleW : V ≤ W := by
      rw [hWdef]
      exact le_iSup (fun V : {V : Subgroup G // V ≤ K ∧ IsKleinFour ↥V} => (V : Subgroup G))
        ⟨V, hVK, hV4⟩
    have hcenter : Subgroup.center ↥K ≤ pPrimeCore 2 ↥K := by
      haveI : Group.IsPerfect ↥K := hK.1
      have hcenter_q : Subgroup.center (↥K ⧸ pPrimeCore 2 ↥K) = ⊥ := by
        rcases hKs.eq_bot_or_eq_top_of_normal (Subgroup.center (↥K ⧸ pPrimeCore 2 ↥K)) with
          hz | hz
        · exact hz
        · exfalso
          haveI : IsMulCommutative (↥K ⧸ pPrimeCore 2 ↥K) := center_eq_top_iff.mp hz
          exact Group.IsPerfect.not_isMulCommutative (↥K ⧸ pPrimeCore 2 ↥K) inferInstance
      intro x hx
      have hxQ : (QuotientGroup.mk x : ↥K ⧸ pPrimeCore 2 ↥K) ∈
          Subgroup.center (↥K ⧸ pPrimeCore 2 ↥K) := by
        refine Subgroup.mem_center_iff.mpr fun y => ?_
        obtain ⟨y0, rfl⟩ := QuotientGroup.mk_surjective y
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
          Subgroup.mem_center_iff.mp hx y0]
      rw [hcenter_q, Subgroup.mem_bot] at hxQ
      exact (QuotientGroup.eq_one_iff x).mp hxQ
    have hVsubW : V.subgroupOf K ≤ W.subgroupOf K := fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hVleW (Subgroup.mem_subgroupOf.mp hx))
    have hVleO : V.subgroupOf K ≤ pPrimeCore 2 ↥K := hVsubW.trans (h.trans hcenter)
    have hcardV : Nat.card (V.subgroupOf K) = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv]
      exact hV4.card_four
    have hdvd : 4 ∣ Nat.card (pPrimeCore 2 ↥K) :=
      hcardV ▸ Subgroup.card_dvd_of_le hVleO
    exact (odd_card_pPrimeCore K).not_two_dvd_nat (dvd_trans (by norm_num : 2 ∣ 4) hdvd)

private theorem sup_oddCoreIn_eq_of_le_normalizer_of_isSimpleGroup {C J : Subgroup G}
    (hCJ : C ≤ J) (hJN : J ≤ normalizer (C : Set G))
    (hJs : IsSimpleGroup (↥J ⧸ pPrimeCore 2 ↥J)) (hnot : ¬ C ≤ FooteLit.oddCoreIn J) :
    C ⊔ FooteLit.oddCoreIn J = J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOC : (C.subgroupOf J).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hJN
  let q : ↥J →* ↥J ⧸ pPrimeCore 2 ↥J := QuotientGroup.mk' _
  have hqker : q.ker = pPrimeCore 2 ↥J := QuotientGroup.ker_mk' _
  have hnot' : ¬ C.subgroupOf J ≤ pPrimeCore 2 ↥J := by
    intro hle
    apply hnot
    intro x hx
    have hx' : (⟨x, hCJ hx⟩ : ↥J) ∈ C.subgroupOf J := Subgroup.mem_subgroupOf.mpr hx
    have hx'' : (⟨x, hCJ hx⟩ : ↥J) ∈ pPrimeCore 2 ↥J := hle hx'
    rw [← subgroupOf_oddCoreIn J] at hx''
    simpa using Subgroup.mem_subgroupOf.mp hx''
  have hmapN : ((C.subgroupOf J).map q).Normal :=
    hOC.map q (QuotientGroup.mk'_surjective _)
  have hsup : C.subgroupOf J ⊔ pPrimeCore 2 ↥J = ⊤ := by
    haveI : ((C.subgroupOf J).map q).Normal := hmapN
    rcases hJs.eq_bot_or_eq_top_of_normal ((C.subgroupOf J).map q) with h | h
    · exfalso
      apply hnot'
      have hbot := (Subgroup.map_eq_bot_iff (C.subgroupOf J)).mp h
      rwa [hqker] at hbot
    · refine eq_top_iff.mpr fun y _ => ?_
      have hy : q y ∈ (C.subgroupOf J).map q := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨c, hc, hcq⟩ := Subgroup.mem_map.mp hy
      have hmem : c⁻¹ * y ∈ q.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hcq, inv_mul_cancel]
      rw [hqker] at hmem
      have hyy : y = c * (c⁻¹ * y) := by group
      rw [hyy]
      exact (C.subgroupOf J ⊔ pPrimeCore 2 ↥J).mul_mem (Subgroup.mem_sup_left hc)
        (Subgroup.mem_sup_right hmem)
  have h1 : (C ⊔ FooteLit.oddCoreIn J).subgroupOf J = (⊤ : Subgroup ↥J) := by
    rw [Subgroup.subgroupOf_sup hCJ (le_oddCoreIn J), subgroupOf_oddCoreIn, hsup]
  have h2 : J ≤ C ⊔ FooteLit.oddCoreIn J := by
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥J) ∈ (C ⊔ FooteLit.oddCoreIn J).subgroupOf J := by
      rw [h1]
      exact Subgroup.mem_top _
    simpa using Subgroup.mem_subgroupOf.mp hx'
  exact le_antisymm (sup_le hCJ (le_oddCoreIn J)) h2

theorem eq_and_le_centralizer_oddCoreIn {b : G} {J P V : Subgroup G}
    (hJ : FooteLit.IsTwoComponentIn J (centralizer ({b} : Set G)))
    (hJs : IsSimpleGroup (↥J ⧸ pPrimeCore 2 ↥J)) (hPJ : P ⊔ FooteLit.oddCoreIn J = J)
    (hP : Group.IsPerfect ↥P) (hVP : V ≤ P) (hV : IsKleinFour ↥V)
    (hVc : V ≤ centralizer (FooteLit.oddCoreIn (centralizer ({b} : Set G)) : Set G)) :
    P = J ∧ J ≤ centralizer (FooteLit.oddCoreIn (centralizer ({b} : Set G)) : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPJle : P ≤ J := by
    rw [← hPJ]
    exact le_sup_left
  have hJnormOb : J ≤ normalizer (FooteLit.oddCoreIn (centralizer ({b} : Set G)) : Set G) :=
    hJ.1.trans ((Subgroup.le_normalizer (H := centralizer ({b} : Set G))).trans
      (fun _ hx => FooteLit.mem_normalizer_oddCoreIn hx))
  have hJnormCentOb :
      J ≤ normalizer (centralizer (FooteLit.oddCoreIn (centralizer ({b} : Set G)) : Set G) :
        Set G) :=
    hJnormOb.trans (CFSG.Goldschmidt75.normalizer_le_normalizer_centralizer
      (FooteLit.oddCoreIn (centralizer ({b} : Set G))))
  have hJN : J ≤ normalizer ((J ⊓ centralizer
      (FooteLit.oddCoreIn (centralizer ({b} : Set G)) : Set G) : Subgroup G) : Set G) := by
    intro j hj
    have h1 : j ∈ normalizer (J : Set G) := Subgroup.le_normalizer hj
    have h2 : j ∈ normalizer (centralizer
        (FooteLit.oddCoreIn (centralizer ({b} : Set G)) : Set G)) := hJnormCentOb hj
    rw [Subgroup.mem_normalizer_iff] at h1 h2
    refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr (h1 x) (h2 x)
  have hVC : V ≤ J ⊓ centralizer
      (FooteLit.oddCoreIn (centralizer ({b} : Set G)) : Set G) :=
    le_inf (hVP.trans hPJle) hVc
  have hnot : ¬ (J ⊓ centralizer
      (FooteLit.oddCoreIn (centralizer ({b} : Set G)) : Set G)) ≤ FooteLit.oddCoreIn J := by
    intro hle
    have hVO : V ≤ FooteLit.oddCoreIn J := hVC.trans hle
    have hdvd : 4 ∣ Nat.card (FooteLit.oddCoreIn J) := by
      simpa [hV.card_four] using Subgroup.card_dvd_of_le hVO
    exact (FooteLit.odd_card_oddCoreIn J).not_two_dvd_nat (dvd_trans (by norm_num : 2 ∣ 4) hdvd)
  have hCsup : (J ⊓ centralizer
      (FooteLit.oddCoreIn (centralizer ({b} : Set G)) : Set G)) ⊔ FooteLit.oddCoreIn J = J :=
    sup_oddCoreIn_eq_of_le_normalizer_of_isSimpleGroup inf_le_left hJN hJs hnot
  have hperfect : Group.IsPerfect ↥J :=
    CFSG.ComponentClassification.GSThmB.B5a.isPerfect_of_isPComponent_subgroupOf hJ.1 hJ.2
  have hJleC : J ≤ J ⊓ centralizer
      (FooteLit.oddCoreIn (centralizer ({b} : Set G)) : Set G) :=
    CFSG.ComponentClassification.HarrisLit.L219.le_of_le_sup_of_odd hperfect
      (FooteLit.odd_card_oddCoreIn J) (le_oddCoreIn J |>.trans hJN) hCsup.ge
  have hJc : J ≤ centralizer (FooteLit.oddCoreIn (centralizer ({b} : Set G)) : Set G) :=
    fun x hx => (Subgroup.mem_inf.mp (hJleC hx)).2
  refine ⟨?_, hJc⟩
  have hOJle : FooteLit.oddCoreIn J ≤ FooteLit.oddCoreIn (centralizer ({b} : Set G)) :=
    CFSG.ComponentClassification.GSThmB.Seven.oddCoreIn_le_of_isPComponent hJ.1 hJ.2
  have hOJcent : FooteLit.oddCoreIn J ≤ centralizer (J : Set G) := by
    have h1 : J ≤ centralizer (FooteLit.oddCoreIn J : Set G) :=
      hJc.trans (Subgroup.centralizer_le hOJle)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (h1 hy) x hx).symm
  have hOZ : pPrimeCore 2 ↥J ≤ Subgroup.center ↥J := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hxJ : (x : G) ∈ FooteLit.oddCoreIn J := Subgroup.mem_map_of_mem J.subtype hx
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hOJcent hxJ) (y : G) y.2)
  have hsup : P.subgroupOf J ⊔ pPrimeCore 2 ↥J = ⊤ :=
    subgroupOf_sup_eq_top_of_sup_oddCoreIn_eq hPJle hPJ
  haveI : Group.IsPerfect ↥J := hperfect
  have hPtop : P.subgroupOf J = ⊤ :=
    CFSG.GroupTheory.eq_top_of_sup_le_center_of_isPerfect hOZ hsup
  have hJP : J ≤ P := by
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥J) ∈ P.subgroupOf J := by
      rw [hPtop]
      exact Subgroup.mem_top _
    simpa using Subgroup.mem_subgroupOf.mp hx'
  exact le_antisymm hPJle hJP

end CFSG.ComponentClassification.FooteMarked
