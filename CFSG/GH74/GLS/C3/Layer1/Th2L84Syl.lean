module

public import CFSG.GH74.GLS.C3.Layer1.Th2PumpTerm
public import CFSG.GH74.GLS.C3.Layer1.Th2L84
public import CFSG.GH74.GLS.C3.Layer1.Th2Main
public import CFSG.GH74.GLS.TwoThin.Rank
import CFSG.GroupTheory.LocalCores.ComponentOddCommutator
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma21i
public import CFSG.GH74.GLS.C3.Layer1.Th2L83GenCore
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic4
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic5
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic6
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic7
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic8
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic9

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2
open scoped commutatorElement

@[expose] def B_thm2_l84_le : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S M : Subgroup G) (ρ : Th2Row)
    (B : Subgroup G), Th2M2 x y K T S M ρ B → K ≤ M → ¬ CFSG.IsQuasisimple ↥K →
      ∀ q ∈ T ⊓ CxK x K, ∀ k ∈ K, ⁅k, q⁆ ∈ pPrimeCoreOf 2 M

end CFSG.GH74.GLS

namespace CFSG.GH74.GLS.Th2.L84Syl

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open scoped commutatorElement

section Cent

open CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.C3.Layer1.PumpRigid
  CFSG.GH74.GLS.Stage1.Thm3.Sec4

variable {G : Type} [Group G] [Finite G]

theorem mem_CxK_of_bar_cover {u : G} {K M J Λ : Subgroup G}
    (hJc : IsPCompIn 2 (centralizer ({u} : Set G)) J)
    (hKM : K ≤ M) (hΛK : Λ ≤ K) (hvert : bar u Λ = bar u J)
    {r : G} (hrY : r ∈ centralizer ({u} : Set G)) (hr : r ∈ CMbar M K) :
    r ∈ CxK u J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t := sbar r hrY with ht
  set Ñ : Subgroup ↥(centralizer ({u} : Set G)) := (pPrimeCoreOf 2 M ⊓ (centralizer ({u} : Set G))).subgroupOf (centralizer ({u} : Set G)) with hÑ
  set N : Subgroup (TwoThin.barQ ↥(centralizer ({u} : Set G))) := Ñ.map (TwoThin.barMk ↥(centralizer ({u} : Set G))) with hN
  have hNcop : Nat.Coprime 2 (Nat.card ↥N) := by
    have h1 : Nat.card ↥N ∣ Nat.card ↥Ñ := Subgroup.card_map_dvd Ñ _
    have h2 : Nat.card ↥Ñ = Nat.card ↥(pPrimeCoreOf 2 M ⊓ (centralizer ({u} : Set G)) : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have h3 : Nat.card ↥(pPrimeCoreOf 2 M ⊓ (centralizer ({u} : Set G)) : Subgroup G) ∣ Nat.card ↥(pPrimeCoreOf 2 M) :=
      Subgroup.card_dvd_of_le inf_le_left
    have h4 : Nat.card ↥(pPrimeCoreOf 2 M) = Nat.card ↥(pPrimeCore 2 ↥M) :=
      Subgroup.card_map_of_injective M.subtype_injective
    have hc : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 ↥M)) := CFSG.pPrimeCore_coprime_card
    rw [h2] at h1
    rw [h4] at h3
    exact Nat.Coprime.coprime_dvd_right (h1.trans h3) hc
  have hSN : ∀ s ∈ bar u J, ∀ n ∈ N, s * n * s⁻¹ ∈ N := by
    intro s hs n hn
    rw [← hvert] at hs
    obtain ⟨m, hm, rfl⟩ := hs
    obtain ⟨ñ, hñ, rfl⟩ := hn
    refine ⟨m * ñ * m⁻¹, ?_, by simp [map_mul, map_inv]⟩
    have hmΛ : (m : G) ∈ Λ := Subgroup.mem_subgroupOf.mp hm
    have hmM : (m : G) ∈ M := hKM (hΛK hmΛ)
    have hñO : (ñ : G) ∈ pPrimeCoreOf 2 M ∧ (ñ : G) ∈ (centralizer ({u} : Set G)) :=
      Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.mp hñ)
    show m * ñ * m⁻¹ ∈ Ñ
    rw [hÑ, Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.2 ⟨?_, (m * ñ * m⁻¹).2⟩
    have := (Subgroup.mem_normalizer_iff.1
      (TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hmM)) (ñ : G)).1 hñO.1
    simpa using this
  have hSnormalizes : bar u J ≤ normalizer (N : Set _) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact hSN s hs n
    · intro hn
      have h := hSN s⁻¹ ((bar u J).inv_mem hs) (s * n * s⁻¹) hn
      simpa [mul_assoc] using h
  have hÑeq : Ñ = (pPrimeCoreOf 2 M).comap (centralizer ({u} : Set G)).subtype := by
    ext z
    simp [hÑ, Subgroup.mem_subgroupOf, Subgroup.mem_comap, z.2]
  have hrÑ : (⟨r, hrY⟩ : ↥(centralizer ({u} : Set G))) ∈ normalizer (Ñ : Set _) := by
    rw [hÑeq]
    exact Subgroup.le_normalizer_comap _
      (TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hr.1))
  have htN : t ∈ normalizer (N : Set _) :=
    Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ hrÑ)
  have hcommN : ∀ w ∈ bar u J, ⁅w, t⁆ ∈ N := by
    intro w hw
    have hw' : w ∈ bar u Λ := by rw [hvert]; exact hw
    obtain ⟨m, hm, rfl⟩ := hw'
    have hmΛ : (m : G) ∈ Λ := Subgroup.mem_subgroupOf.mp hm
    have hmK : (m : G) ∈ K := hΛK hmΛ
    have hmY : (m : G) ∈ (centralizer ({u} : Set G)) := m.2
    set w := TwoThin.barMk ↥(centralizer ({u} : Set G)) m with hwdef
    have hwS : w ∈ bar u J := by rw [← hvert]; exact ⟨m, hm, rfl⟩
    have hc : ⁅(m : G), r⁆ ∈ pPrimeCoreOf 2 M :=
      hr.2.2.2 (m : G) (Subgroup.mem_sup_left hmK)
    have hcY : ⁅(m : G), r⁆ ∈ (centralizer ({u} : Set G)) := by
      have h1 : (m : G) * r * (m : G)⁻¹ * r⁻¹ ∈ (centralizer ({u} : Set G)) :=
        (centralizer ({u} : Set G)).mul_mem ((centralizer ({u} : Set G)).mul_mem ((centralizer ({u} : Set G)).mul_mem hmY hrY) ((centralizer ({u} : Set G)).inv_mem hmY)) ((centralizer ({u} : Set G)).inv_mem hrY)
      simpa [commutatorElement_def] using h1
    have heq : (⟨⁅(m : G), r⁆, hcY⟩ : ↥(centralizer ({u} : Set G))) = m * ⟨r, hrY⟩ * m⁻¹ * ⟨r, hrY⟩⁻¹ :=
      Subtype.ext (by simp [commutatorElement_def])
    have hcN : w * t * w⁻¹ * t⁻¹ ∈ N := by
      refine ⟨⟨⁅(m : G), r⁆, hcY⟩, ?_, ?_⟩
      · show (⟨⁅(m : G), r⁆, hcY⟩ : ↥(centralizer ({u} : Set G))) ∈ Ñ
        rw [hÑ, Subgroup.mem_subgroupOf]
        exact ⟨hc, hcY⟩
      · rw [heq, hwdef, ht]
        simp [sbar, map_mul, map_inv]
    simpa only [commutatorElement_def] using hcN
  have htS : t ∈ centralizer (bar u J : Set _) :=
    CFSG.LocalCores.mem_centralizer_of_commutator_mem_odd
      (isComponent_bar hJc) (Nat.Coprime.odd_of_left hNcop) hSnormalizes htN hcommN
  refine mem_CxK_of_centralizes hJc hrY (fun w hw => ?_)
  have hwt : w * t = t * w := Subgroup.mem_centralizer_iff.mp htS w hw
  change t * w * t⁻¹ = w
  rw [← hwt]
  group

theorem mem_CxK_at_point {x : G} {K M : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (hKM : K ≤ M)
    {r : G} (hrx : r ∈ centralizer ({x} : Set G)) (hr : r ∈ CMbar M K) :
    r ∈ CxK x K := mem_CxK_of_bar_cover hK hKM le_rfl rfl hrx hr

theorem mem_CxK_of_cmbar {x u : G} {K M K_u : Subgroup G} (hKM : K ≤ M)
    (hltu : PumpUpLT 2 x K u K_u) (e : kBar K_u ≃* kBar K)
    (hxKu : x ∈ normalizer (K_u : Set G))
    {r : G} (hrY : r ∈ centralizer ({u} : Set G)) (hr : r ∈ CMbar M K) :
    r ∈ CxK u K_u := by
  have hxY : x ∈ centralizer ({u} : Set G) := TwoThin.mem_centralizer_symm hltu.2.2.1
  obtain ⟨Λ, hΛ, -, -, -, -, hcases⟩ := rigid_step hltu hxY (Nat.card_congr e.toEquiv).le
  have hvert : bar u Λ = bar u K_u := (hcases.resolve_right (fun h => h.1 hxKu)).2
  exact mem_CxK_of_bar_cover hltu.2.1.2.2 hKM (fun a ha => (hΛ.le ha).1) hvert hrY hr

end Cent

section Main

variable {G : Type} [Group G] [Finite G]

theorem exists_involution_mem_center {R : Subgroup G} (hR : IsPGroup 2 ↥R) {x : G} (hxR : x ∈ R)
    (hx1 : x ≠ 1) : ∃ u ∈ R, orderOf u = 2 ∧ ∀ r ∈ R, u * r = r * u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial ↥R := ⟨⟨⟨x, hxR⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩⟩
  have := hR.center_nontrivial
  have hC : IsPGroup 2 ↥(center ↥R) := hR.of_injective (center ↥R).subtype (center ↥R).subtype_injective
  obtain ⟨n, hn⟩ := hC.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h1 : 1 < Nat.card ↥(center ↥R) := Finite.one_lt_card
    rw [hn] at h1
    simp at h1
  have hdvd : 2 ∣ Nat.card ↥(center ↥R) := by rw [hn]; exact dvd_pow_self 2 hn0
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  refine ⟨((a : ↥R) : G), (a : ↥R).2, ?_, fun r hr => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact ha
  · have := Subgroup.mem_center_iff.1 a.2 ⟨r, hr⟩
    exact (congrArg Subtype.val this).symm

omit [Finite G] in
theorem le_cmbar_of_comm {x : G} {K T M : Subgroup G} (hTM : T ⊓ CxK x K ≤ M) (hKM : K ≤ M)
    (hcomm : ∀ q ∈ T ⊓ CxK x K, ∀ k ∈ K, ⁅k, q⁆ ∈ pPrimeCoreOf 2 M) :
    T ⊓ CxK x K ≤ CMbar M K := by
  intro q hq
  have hqM : q ∈ M := hTM hq
  have hqN : q ∈ normalizer (K : Set G) := (Subgroup.mem_inf.1 hq.2).2.1
  have hNO : q ∈ normalizer (pPrimeCoreOf 2 M : Set G) :=
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hqM)
  refine Subgroup.mem_inf.2 ⟨hqM, mem_normalizer_sup hqN hNO, hNO, fun k hk => ?_⟩
  refine Th2.comm_mem_sup (O := pPrimeCoreOf 2 M) (A := K) (B := pPrimeCoreOf 2 M) (c := q)
    (fun a ha => TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer (hKM ha)))
    (fun b hb => Subgroup.le_normalizer hb) (fun a ha => hcomm q hq a ha) (fun b hb => ?_) k hk
  have : ⁅b, q⁆ = b * (q * b⁻¹ * q⁻¹) := by simp only [commutatorElement_def]; group
  rw [this]
  exact (pPrimeCoreOf 2 M).mul_mem hb
    ((Subgroup.mem_normalizer_iff.1 hNO _).1 ((pPrimeCoreOf 2 M).inv_mem hb))

theorem sylow_cmbar_of_le {x y : G}
    {K T S M : Subgroup G} (h : Th2Std x y K T S) (hKM : K ≤ M)
    (hle : T ⊓ CxK x K ≤ CMbar M K)
    (hrank : ∀ u ∈ T ⊓ CxK x K, orderOf u = 2 →
      3 ≤ pRank 2 ↥(centralizer ({u} : Set G))) : IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hterm : IsTwoTerminal x K := h.v2ss.isV2Triple.2.1
  have hxo : orderOf x = 2 := h.orderOf_x
  have hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K := h.comp
  have hQsyl : IsSylowOf 2 (T ⊓ CxK x K) (CxK x K) := h.sylow_Q
  have hxQ : x ∈ T ⊓ CxK x K := ⟨h.x_mem_T, h.x_mem_CxK⟩
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hxo
    omega
  obtain ⟨R, hRsyl, hQR⟩ : ∃ R : Subgroup G, IsSylowOf 2 R (CMbar M K) ∧ T ⊓ CxK x K ≤ R := by
    have hQp : IsPGroup 2 ↥((T ⊓ CxK x K).subgroupOf (CMbar M K)) :=
      hQsyl.isPGroup.comap_subtype
    obtain ⟨P, hP⟩ := hQp.exists_le_sylow
    refine ⟨(P : Subgroup ↥(CMbar M K)).map (CMbar M K).subtype, ⟨P, rfl⟩, fun q hq => ?_⟩
    exact ⟨⟨q, hle hq⟩, hP (Subgroup.mem_subgroupOf.2 hq), rfl⟩
  suffices hRQ : R ≤ T ⊓ CxK x K from by
    have : R = T ⊓ CxK x K := le_antisymm hRQ hQR
    rw [← this]
    exact hRsyl
  have hRp : IsPGroup 2 ↥R := hRsyl.isPGroup
  have hRx : ∀ c ∈ R, c ∈ centralizer ({x} : Set G) → c ∈ CxK x K := by
    intro c hcR hcx
    exact mem_CxK_at_point hKc hKM hcx (hRsyl.le hcR)
  have hCRQ : R ⊓ centralizer ({x} : Set G) = T ⊓ CxK x K :=
    hQsyl.eq_of_le (le_inf hQR (hQsyl.le.trans inf_le_left)) (fun c hc => hRx c hc.1 hc.2)
      hRp.to_inf_left
  obtain ⟨u, huR, hu2, huc⟩ := exists_involution_mem_center hRp (hQR hxQ) hx1
  have hux : u ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 (huc x (hQR hxQ))
  have huQ : u ∈ T ⊓ CxK x K := by
    rw [← hCRQ]
    exact ⟨huR, hux⟩
  have huQc : ∀ q ∈ T ⊓ CxK x K, u * q = q * u := fun q hq => huc q (hQR hq)
  have hR3 : 3 ≤ pRank 2 ↥(centralizer ({u} : Set G)) :=
    hrank u huQ hu2
  obtain ⟨K_u, hltu⟩ := TwoThin.exists_pumpup_of_involution hxo hu2 hKc hux huQ.2.2 hterm.1 hR3
  obtain ⟨hxKu, ⟨e⟩⟩ := hterm.2.1 u K_u hltu
  have hQu : IsSylowOf 2 (T ⊓ CxK x K) (CxK u K_u) :=
    hterm.2.2 (T ⊓ CxK x K) hQsyl u K_u hltu huQ huQc
  have hRle : R ≤ CxK u K_u := fun r hr =>
    mem_CxK_of_cmbar hKM hltu e hxKu
      (mem_centralizer_singleton_iff.2 (huc r hr).symm) (hRsyl.le hr)
  exact (hQu.eq_of_le hQR hRle hRp).le

theorem b_thm2_l84_syl_of (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) (h82 : B_thm2_l82)
    (hle : B_thm2_l84_le) : B_thm2_l84_syl := by
  intro G _ _ hG x y K T S M hchoice hKM
  have h := hchoice.std
  refine sylow_cmbar_of_le h hKM ?_ (fun u _ hu =>
    TwoThin.rankThreeCentralizers G hG.kproper.1 hG.kproper.2.1
      (by rw [hG.pRank_eq_four]; omega) u hu)
  rcases hchoice with h1 | ⟨ρ, B, h2⟩
  ·
    have hQK : T ⊓ CxK x K ≤ centralizer (K : Set G) := h1.sylowQ.le
    refine le_cmbar_of_comm (fun q hq => h1.le_M (Subgroup.centralizer_le_normalizer _ (hQK hq)))
      hKM (fun q hq k hk => ?_)
    have hc : k * q = q * k := Subgroup.mem_centralizer_iff.1 (hQK hq) k hk
    rw [commutatorElement_eq_one_iff_mul_comm.2 hc]
    exact one_mem _
  ·
    have hTM : T ≤ M := t_le_M_of_M2 hL34 h82 hG h2
    refine le_cmbar_of_comm (fun q hq => hTM hq.1) hKM (fun q hq k hk => ?_)
    by_cases hqs : CFSG.IsQuasisimple ↥K
    · have hc : q * k = k * q := commute_of_mem_cSec hqs (Subgroup.mem_inf.1 hq.2).2 k hk
      rw [commutatorElement_eq_one_iff_mul_comm.2 hc.symm]
      exact one_mem _
    · exact hle G hG x y K T S M ρ B h2 hKM hqs q hq k hk

end Main

end CFSG.GH74.GLS.Th2.L84Syl
