module

public import CFSG.GH74.GLS.C3.Layer1.BkA7Facts
import CFSG.GroupTheory.LocalCores.ComponentOddCommutator
import CFSG.GH74.GLS.C3.Layer1.Th2P88bY
public import CFSG.GH74.GLS.C3.Layer1.Th2IV26

public section

namespace CFSG.GH74.GLS.Th2.P812A7

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open CFSG.GH74.GLS.Th2.P85
open scoped commutatorElement

variable {G : Type} [Group G]

theorem cmk_le_cmbar [Finite G] {K L M : Subgroup G} (hLM : L ≤ M) (hsub : IsSubnormalIn L M)
    (hLeq : L = pPrimeCoreOf 2 L ⊔ K) : CMK M L ≤ CMbar M K := by
  have hOLO : pPrimeCoreOf 2 L ≤ pPrimeCoreOf 2 M := pPrimeCoreOf_le_of_subnormal hsub
  have hKO := sup_pPrimeCoreOf_eq hsub hLeq
  have hNO : ∀ g ∈ M, g ∈ normalizer (pPrimeCoreOf 2 M : Set G) := fun g hg =>
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hg)
  intro c hc
  unfold CMbar
  rw [hKO]
  obtain ⟨hcM, hcN1, -, hcomm⟩ := hc
  refine ⟨hcM, mem_normalizer_sup hcN1 (hNO c hcM), hNO c hcM, ?_⟩
  refine comm_mem_sup (O := pPrimeCoreOf 2 M) (A := L) (B := pPrimeCoreOf 2 M) ?_ ?_ ?_ ?_
  · exact fun l hl => hNO l (hLM hl)
  · exact fun o ho => Subgroup.le_normalizer ho
  · exact fun a ha => hOLO (hcomm a ha)
  · intro b hb
    have : ⁅b, c⁆ = b * (c * b⁻¹ * c⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact (pPrimeCoreOf 2 M).mul_mem hb
      ((Subgroup.mem_normalizer_iff.1 (hNO c hcM) _).1 ((pPrimeCoreOf 2 M).inv_mem hb))

theorem cmbar_le_normalizer [Finite G] {K L M : Subgroup G}
    (hcomp : IsPCompIn 2 M L) (hsub : IsSubnormalIn L M)
    (hLeq : L = pPrimeCoreOf 2 L ⊔ K) :
    CMbar M K ≤ normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKL : K ≤ L := by rw [hLeq]; exact le_sup_right
  have hKM : K ≤ M := hKL.trans hcomp.1
  have hOM : pPrimeCoreOf 2 M ≤ M := Subgroup.map_subtype_le _
  have hKOM : K ⊔ pPrimeCoreOf 2 M ≤ M := sup_le hKM hOM
  let O : Subgroup ↥M := pPrimeCore 2 ↥M
  let π : ↥M →* ↥M ⧸ O := QuotientGroup.mk' O
  have hsubO : (pPrimeCoreOf 2 M).subgroupOf M = O := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hOM]
    rfl
  have hbot : ((pPrimeCoreOf 2 M).subgroupOf M).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk', hsubO]
  have hsupMap : ((K ⊔ pPrimeCoreOf 2 M).subgroupOf M).map π =
      (K.subgroupOf M).map π := by
    rw [Subgroup.subgroupOf_sup hKM hOM, Subgroup.map_sup, hbot, sup_bot_eq]
  have hmap : (L.subgroupOf M).map π = (K.subgroupOf M).map π := by
    apply CFSG.ComponentClassification.GSLit.map_mk_eq_of_sup_pPrimeCore hcomp.1 hcomp.2
    rw [sup_comm]
    exact hLeq.symm
  intro c hc
  have hcM : c ∈ M := hc.1
  have hcN : (⟨c, hcM⟩ : ↥M) ∈
      normalizer (((K ⊔ pPrimeCoreOf 2 M).subgroupOf M) : Set ↥M) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hKOM]
    exact hc.2.1
  have himage : π ⟨c, hcM⟩ ∈ normalizer (((K.subgroupOf M).map π) : Set (↥M ⧸ O)) := by
    have h := Subgroup.le_normalizer_map
      (H := ((K ⊔ pPrimeCoreOf 2 M).subgroupOf M)) π
      (Subgroup.mem_map_of_mem π hcN)
    rwa [hsupMap] at h
  have himageL : π ⟨c, hcM⟩ ∈ normalizer (((L.subgroupOf M).map π) : Set (↥M ⧸ O)) := by
    rw [hmap]
    exact himage
  have hcNM : (⟨c, hcM⟩ : ↥M) ∈ normalizer ((L.subgroupOf M) : Set ↥M) :=
    CFSG.ComponentClassification.UnbalancedLayer.mem_normalizer_of_map hcomp.2 himageL
  rw [← Subgroup.subgroupOf_normalizer_eq hcomp.1] at hcNM
  exact hcNM

theorem cmbar_eq_cmk_of_isPCompIn [Finite G] {K L M : Subgroup G}
    (hcomp : IsPCompIn 2 M L) (hsub : IsSubnormalIn L M)
    (hLeq : L = pPrimeCoreOf 2 L ⊔ K) :
    CMbar M K = CMK M L := by
  have hLM : L ≤ M := hcomp.1
  have hOLO : pPrimeCoreOf 2 L ≤ pPrimeCoreOf 2 M := pPrimeCoreOf_le_of_subnormal hsub
  have hKO := sup_pPrimeCoreOf_eq hsub hLeq
  have hNL : CMbar M K ≤ normalizer (L : Set G) :=
    cmbar_le_normalizer hcomp hsub hLeq
  have hOLeq : pPrimeCoreOf 2 L = pPrimeCoreOf 2 M ⊓ L := by
    apply le_antisymm
    · exact le_inf hOLO (Subgroup.map_subtype_le _)
    · exact inf_le_pPrimeCoreOf hLM
  apply le_antisymm
  · intro c hc
    have hcM : c ∈ M := hc.1
    have hcOM : c ∈ normalizer (pPrimeCoreOf 2 M : Set G) := hc.2.2.1
    have hcNL : c ∈ normalizer (L : Set G) := hNL hc
    have hcOL : c ∈ normalizer (pPrimeCoreOf 2 L : Set G) := by
      rw [hOLeq]
      exact mem_normalizer_inf hcOM hcNL
    unfold CMK
    refine ⟨hcM, hcNL, hcOL, fun l hl => ?_⟩
    have hl' : l ∈ K ⊔ pPrimeCoreOf 2 M := by
      rw [hKO]
      exact Subgroup.mem_sup_left hl
    have h1 : ⁅l, c⁆ ∈ pPrimeCoreOf 2 M := hc.2.2.2 l hl'
    have h2 : ⁅l, c⁆ ∈ L := by
      have hcl : c * l⁻¹ * c⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.1 hcNL l⁻¹).1 (L.inv_mem hl)
      have e : ⁅l, c⁆ = l * (c * l⁻¹ * c⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact L.mul_mem hl hcl
    exact inf_le_pPrimeCoreOf hLM ⟨h1, h2⟩
  · exact cmk_le_cmbar hLM hsub hLeq

theorem isSylowOf_cmk_of_cmbar [Finite G] {K L M Q : Subgroup G}
    (hcomp : IsPCompIn 2 M L) (hsub : IsSubnormalIn L M)
    (hLeq : L = pPrimeCoreOf 2 L ⊔ K)
    (hQ : IsSylowOf 2 Q (CMbar M K)) :
    IsSylowOf 2 Q (CMK M L) :=
  (cmbar_eq_cmk_of_isPCompIn hcomp hsub hLeq) ▸ hQ

theorem centralizer_le_M_of_sylow_cmbar [Finite G] {K L M Q : Subgroup G}
    (hcomp : IsPCompIn 2 M L) (hsub : IsSubnormalIn L M)
    (hLeq : L = pPrimeCoreOf 2 L ⊔ K)
    (hQ : IsSylowOf 2 Q (CMbar M K)) (hgam : gammaK 2 Q 1 ≤ M) :
    ∀ t ∈ CMK M L, orderOf t = 2 → centralizer ({t} : Set G) ≤ M :=
  CFSG.GH74.GLS.C3.Layer1.U1a.centralizer_le_of_gammaK
    (isSylowOf_cmk_of_cmbar hcomp hsub hLeq hQ) hgam

theorem L_normal_of_sylow_card_four [Finite G] {K T M L Q : Subgroup G} (hTM : T ≤ M)
    (hT2 : IsPGroup 2 ↥T) (hP8 : Nat.card ↥(T ⊓ K) = 8) (hKL : K ≤ L)
    (hLcomp : IsPCompIn 2 M L) (hsub : IsSubnormalIn L M) (hLeq : L = pPrimeCoreOf 2 L ⊔ K)
    (hQ : IsSylowOf 2 Q (CMbar M K)) (hQ4 : Nat.card ↥Q = 4) :
    ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L := by
  have hQmk : IsSylowOf 2 Q (CMK M L) :=
    isSylowOf_cmk_of_cmbar hLcomp hsub hLeq hQ
  refine CFSG.GH74.GLS.normal_of_card_sylow_cSec_lt (Q := Q) hLcomp
    (inf_le_right.trans hKL) (hT2.to_le inf_le_left) ?_ ?_
  · simpa [CFSG.GH74.GLS.CMK] using hQmk
  · rw [hQ4, hP8]
    norm_num

theorem Q_normal_in_S [Finite G] {K T M L S Q : Subgroup G} (hQT : Q ≤ T) (hTS : T ≤ S) (hSM : S ≤ M)
    (hS2 : IsPGroup 2 ↥S) (hLM : L ≤ M) (hnorm : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hsub : IsSubnormalIn L M) (hLeq : L = pPrimeCoreOf 2 L ⊔ K)
    (hQ : IsSylowOf 2 Q (CMbar M K)) : ∀ s ∈ S, ∀ q ∈ Q, s * q * s⁻¹ ∈ Q := by
  intro s hs q hq
  have hcm : CMbar M K = CMK M L := cmbar_eq_cmk hLM hnorm hsub hLeq
  have hqC : q ∈ CMbar M K := hQ.le hq
  have h1 : s * q * s⁻¹ ∈ CMbar M K := by
    rw [hcm] at hqC ⊢
    exact cmk_normal hnorm s (hSM hs) q hqC
  have h2 : s * q * s⁻¹ ∈ S := S.mul_mem (S.mul_mem hs (hTS (hQT hq))) (S.inv_mem hs)
  have hle : Q ≤ S ⊓ CMbar M K := le_inf (hQT.trans hTS) hQ.le
  have heq : S ⊓ CMbar M K = Q := hQ.eq_of_le hle inf_le_right (hS2.to_le inf_le_left)
  rw [← heq]
  exact ⟨h2, h1⟩

theorem s_le_M_r3b [Finite G] (h82 : B_thm2_l82) (hG : C3Hyp G) {x y : G} {K T S M B : Subgroup G}
    (h2 : Th2M2 x y K T S M .r3b B) : S ≤ M := by
  intro s hs
  have hb := (h82 G hG x y K T S M .r3b B h2).2.1
  have hrk : Th2Row.r3b.level.n ≤ pRank 2 ↥(Th2Row.r3b.Tstar x K T S) :=
    Th2Tstar.le_pRank_Tstar h2.mem h2.isE.2.2
  have hN' : normalizer ((Th2Row.r3b.Tstar x K T S : Subgroup G) : Set G) ≤
      gammaK 2 (Th2Row.r3b.Tstar x K T S) Th2Row.r3b.level.n := by
    unfold gammaK
    exact le_iSup₂_of_le (Th2Row.r3b.Tstar x K T S) le_rfl (le_iSup_of_le hrk le_rfl)
  exact hb (hN' (Th2Tstar.mem_normalizer_Tstar_r3b hs))

theorem false_of_r3b [Finite G]
    {x y : G} {K T S M B L : Subgroup G} (h2 : Th2M2 x y K T S M .r3b B)
    (hL : IsMinSubnormalIn K M L) (hLcomp : IsPCompIn 2 M L) (hLeq : L = pPrimeCoreOf 2 L ⊔ K)
    (hQ : IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K)) (hSM : S ≤ M) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := h2.std
  obtain ⟨h7, hQ4, hTS⟩ := h2.row
  obtain ⟨e7⟩ := h7
  have hT2 : IsPGroup 2 ↥T := hstd.T_pGroup
  have hS2 : IsPGroup 2 ↥S := hstd.sylowS.isPGroup
  have hTM : T ≤ M := hstd.T_le_S.trans hSM
  have hP8 : Nat.card ↥(T ⊓ K) = 8 :=
    (CFSG.GH74.GLS.C3.Layer1.Bk.isD8_of_inf_alt7 hT2 hstd.sylow_P e7).card_eq
  have hLnorm := L_normal_of_sylow_card_four hTM hT2 hP8 hL.1 hLcomp hL.2.1 hLeq hQ hQ4
  have hQS := Q_normal_in_S inf_le_left hstd.T_le_S hSM hS2 hL.2.1.1 hLnorm hL.2.1 hLeq hQ
  have hQ1 : (T ⊓ CxK x K) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hQ4
    omega
  obtain ⟨w, hwQ, hw1, hwc⟩ := CFSG.GH74.GLS.C3.Layer1.Bk.exists_central_of_normal hS2 hQS (inf_le_left.trans hstd.T_le_S) hQ1
  have hodvd : orderOf w ∣ 2 ^ 2 := by
    have := Subgroup.orderOf_dvd_natCard (T ⊓ CxK x K) hwQ
    rwa [hQ4, show (4 : ℕ) = 2 ^ 2 by norm_num] at this
  have hw1' : orderOf w ≠ 1 := fun h0 => hw1 (orderOf_eq_one_iff.1 h0)
  have h2dvd : 2 ∣ orderOf w := by
    obtain ⟨i, hi, hwi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hodvd
    rcases i with _ | i
    · exact absurd (by simpa using hwi) hw1'
    · rw [hwi]
      exact dvd_pow_self 2 (Nat.succ_ne_zero i)
  have hu2 : orderOf (w ^ (orderOf w / 2)) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos w).ne' h2dvd
  have huQ : w ^ (orderOf w / 2) ∈ T ⊓ CxK x K := Subgroup.pow_mem _ hwQ _
  have hucS : ∀ s ∈ S, s * w ^ (orderOf w / 2) = w ^ (orderOf w / 2) * s := fun s hs =>
    (Commute.pow_right (show Commute s w from hwc s hs) _).eq
  have hsyl := Th2.PumpTerm.isSylow_T_of_A7_card_Q_four hstd e7 hQ4 huQ
    (fun t ht => (hucS t (hstd.T_le_S ht)).symm) hu2
  have hSC : S ≤ centralizer ({w ^ (orderOf w / 2)} : Set G) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.2 (hucS s hs)
  have heq : S = T := hsyl.eq_of_le hstd.T_le_S hSC hS2
  exact (lt_irrefl _) (heq ▸ hTS)

theorem oddCore_K_le_of_isPCompIn [Finite G] {M K : Subgroup G} (hK : IsPCompIn 2 M K) :
    pPrimeCoreOf 2 K ≤ pPrimeCoreOf 2 M := by
  obtain ⟨K', _hcomp, hsub, _hmap, _hmin⟩ := hK.2
  exact CFSG.GH74.GLS.Th2.pPrimeCoreOf_le_of_subnormal ⟨hK.1, hsub⟩

theorem odd_card_imgM [Finite G] {M B : Subgroup G} (hBM : B ≤ M) (hBodd : Odd (Nat.card ↥B)) :
    Odd (Nat.card ↥(imgM M B)) := by
  have h1 : Nat.card ↥(imgM M B) ∣ Nat.card ↥(B.subgroupOf M) :=
    Subgroup.card_map_dvd _ _
  have h2 : Nat.card ↥(B.subgroupOf M) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv
  exact hBodd.of_dvd_nat (h2 ▸ h1)

theorem imgM_eq_of_cover [Finite G] {M K K0 : Subgroup G} (hK : IsPCompIn 2 M K) (hK0K : K0 ≤ K)
    (hcover : ∀ k ∈ K, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 K, k = k0 * o) :
    imgM M K = imgM M K0 := by
  have hKq : IsQuasisimple ↥(imgM M K) := by
    obtain ⟨S0, hcomp0, _hsub0, hmap0, _hmin0⟩ := hK.2
    have hmap0' : imgM M K = S0 := by
      simpa [imgM, TwoThin.barMk] using hmap0
    rw [hmap0']
    exact hcomp0.1
  exact (CFSG.GH74.GLS.Th2.IV26.imgM_eq_of_cover hK.1 hK0K hcover hKq).symm

theorem mem_CMK_of_isPCompIn_cover [Finite G] {M I K K0 : Subgroup G} {r : G}
    (hK : IsPCompIn 2 M K) (hK0K : K0 ≤ K) (hK0I : K0 ≤ I)
    (hcover : ∀ k ∈ K, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 K, k = k0 * o)
    (hrM : r ∈ M) (hrI : r ∈ centralizerSection I (pPrimeCoreOf 2 I)) :
    r ∈ CMK M K := by
  have hKM : K ≤ M := hK.1
  have hK0M : K0 ≤ M := hK0K.trans hKM
  have hOKM : pPrimeCoreOf 2 K ≤ pPrimeCoreOf 2 M := oddCore_K_le_of_isPCompIn hK
  have hS_eq : imgM M K = imgM M K0 := imgM_eq_of_cover hK hK0K hcover
  let S : Subgroup (Mb M) := imgM M K
  let U : Subgroup (Mb M) := imgM M (pPrimeCoreOf 2 I ⊓ M)
  let rbar : Mb M := TwoThin.barMk ↥M (⟨r, hrM⟩ : ↥M)
  have hScomp : IsComponent S := by
    obtain ⟨S0, hcomp0, _hsub0, hmap0, _hmin0⟩ := hK.2
    have hmap0' : imgM M K = S0 := by
      simpa [imgM, TwoThin.barMk] using hmap0
    change IsComponent (imgM M K)
    rw [hmap0']
    exact hcomp0
  have hBodd : Odd (Nat.card ↥(pPrimeCoreOf 2 I ⊓ M)) :=
    (TwoThin.card_pPrimeCoreOf_odd I).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hUodd : Odd (Nat.card ↥U) := by
    change Odd (Nat.card ↥(imgM M (pPrimeCoreOf 2 I ⊓ M)))
    exact odd_card_imgM inf_le_right hBodd
  have hK0norm : imgM M K0 ≤ normalizer (U : Set (Mb M)) := by
    intro w hw
    obtain ⟨k0, hk0, rfl⟩ := mem_imgM_iff.1 hw
    have hk0M : (k0 : G) ∈ M := hK0M hk0
    have hk0O : (k0 : G) ∈ normalizer ((pPrimeCoreOf 2 I ⊓ M : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf (H := pPrimeCoreOf 2 I) (K := M)
        ⟨TwoThin.mem_normalizer_pPrimeCoreOf
            (Subgroup.le_normalizer (hK0I hk0)), Subgroup.le_normalizer hk0M⟩
    exact CFSG.GH74.GLS.Th2.P88b.barMk_mem_normalizer_imgM hk0M hk0O
  have hSU : S ≤ normalizer (U : Set (Mb M)) := by
    change imgM M K ≤ normalizer (U : Set (Mb M))
    rw [hS_eq]
    exact hK0norm
  have hrO : r ∈ normalizer ((pPrimeCoreOf 2 I ⊓ M : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf (H := pPrimeCoreOf 2 I) (K := M)
      ⟨hrI.2.1, Subgroup.le_normalizer hrM⟩
  have hrU : rbar ∈ normalizer (U : Set (Mb M)) :=
    CFSG.GH74.GLS.Th2.P88b.barMk_mem_normalizer_imgM hrM hrO
  have hcomm : ∀ s ∈ S, ⁅s, rbar⁆ ∈ U := by
    intro s hs
    have hs0 : s ∈ imgM M K0 := by
      change s ∈ imgM M K at hs
      rw [hS_eq] at hs
      exact hs
    obtain ⟨k0, hk0, rfl⟩ := mem_imgM_iff.1 hs0
    have hk0M : (k0 : G) ∈ M := hK0M hk0
    have hk0I : (k0 : G) ∈ I := hK0I hk0
    have hcommI : ⁅(k0 : G), r⁆ ∈ pPrimeCoreOf 2 I := hrI.2.2 (k0 : G) hk0I
    have hcommM : ⁅(k0 : G), r⁆ ∈ M := by
      rw [commutatorElement_def]
      exact M.mul_mem (x := ((k0 : G) * r) * (k0 : G)⁻¹) (y := r⁻¹)
        (M.mul_mem (x := (k0 : G) * r) (y := (k0 : G)⁻¹)
          (M.mul_mem (x := (k0 : G)) (y := r) hk0M hrM) (M.inv_mem hk0M))
        (M.inv_mem hrM)
    change ⁅TwoThin.barMk ↥M k0, rbar⁆ ∈ imgM M (pPrimeCoreOf 2 I ⊓ M)
    refine mem_imgM_iff.2 ⟨⟨⁅(k0 : G), r⁆, hcommM⟩, ⟨hcommI, hcommM⟩, ?_⟩
    have hsub : (⟨⁅(k0 : G), r⁆, hcommM⟩ : ↥M) =
        ⁅(⟨(k0 : G), hk0M⟩ : ↥M), (⟨r, hrM⟩ : ↥M)⁆ := Subtype.ext rfl
    rw [hsub, map_commutatorElement]
  have hcentS : rbar ∈ centralizer (S : Set (Mb M)) :=
    CFSG.LocalCores.mem_centralizer_of_commutator_mem_odd hScomp hUodd hSU hrU hcomm
  have hcommO : ∀ k ∈ K, ⁅k, r⁆ ∈ pPrimeCoreOf 2 M := by
    intro k hk
    have hkM : k ∈ M := hKM hk
    have hs : TwoThin.barMk ↥M (⟨k, hkM⟩ : ↥M) ∈ S := by
      change TwoThin.barMk ↥M (⟨k, hkM⟩ : ↥M) ∈ imgM M K
      exact mem_imgM_iff.2 ⟨⟨k, hkM⟩, hk, rfl⟩
    have hcentral := Subgroup.mem_centralizer_iff.1 hcentS (TwoThin.barMk ↥M (⟨k, hkM⟩ : ↥M)) hs
    have hcomm1 : ⁅TwoThin.barMk ↥M (⟨k, hkM⟩ : ↥M), rbar⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact hcentral
    have hcommM : ⁅k, r⁆ ∈ M := by
      rw [commutatorElement_def]
      exact M.mul_mem (x := (k * r) * k⁻¹) (y := r⁻¹)
        (M.mul_mem (x := k * r) (y := k⁻¹)
          (M.mul_mem (x := k) (y := r) hkM hrM) (M.inv_mem hkM))
        (M.inv_mem hrM)
    have hsub : (⟨⁅k, r⁆, hcommM⟩ : ↥M) = ⁅(⟨k, hkM⟩ : ↥M), (⟨r, hrM⟩ : ↥M)⁆ :=
      Subtype.ext rfl
    have hbar1 : TwoThin.barMk ↥M (⟨⁅k, r⁆, hcommM⟩ : ↥M) = 1 := by
      rw [hsub, map_commutatorElement]
      simpa [rbar] using hcomm1
    exact (barMk_eq_one_iff_mem_pPrimeCoreOf _).1 hbar1
  have hcmbar : r ∈ CMbar M K :=
    CFSG.GH74.GLS.Th2.HY.mem_CMbar_of_comm hKM hrM hcommO
  have hsub : IsSubnormalIn K M := by
    obtain ⟨K', _hcomp', hsub', _hmap', _hmin'⟩ := hK.2
    exact ⟨hKM, hsub'⟩
  have hLeq : K = pPrimeCoreOf 2 K ⊔ K :=
    (sup_eq_right.mpr (TwoThin.pPrimeCoreOf_le K)).symm
  have hcm : CMbar M K = CMK M K :=
    CFSG.GH74.GLS.Th2.P812A7.cmbar_eq_cmk_of_isPCompIn hK hsub hLeq
  rwa [hcm] at hcmbar

end CFSG.GH74.GLS.Th2.P812A7

namespace CFSG.GH74.GLS.Th2.P812A7

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P812

variable {G : Type} [Group G]

theorem IsDSub.isFourSub {K P D : Subgroup G} (h : IsDSub K P D) : IsFourSub P D :=
  ⟨h.1, h.2.2.1, h.2.2.2.1⟩

end CFSG.GH74.GLS.Th2.P812A7

