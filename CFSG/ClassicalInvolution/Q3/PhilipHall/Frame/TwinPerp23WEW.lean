module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23WLab
public import CFSG.ClassicalInvolution.Q3.Q3AMTriB01

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement




namespace W

open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Asc77.Thompson

section EW

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem eq_one_of_pgroup_odd {K : Type*} [Group K] {V N : Subgroup K} (hV : IsPGroup 2 V)
    (hN : Odd (Nat.card N)) {v : K} (hvV : v ∈ V) (hvN : v ∈ N) : v = 1 := by
  obtain ⟨n, hn⟩ := hV ⟨v, hvV⟩
  have h1 : orderOf v ∣ 2 ^ n := by
    apply orderOf_dvd_of_pow_eq_one
    simpa using congrArg Subtype.val hn
  have h2 : orderOf v ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hvN
  have hcop : Nat.Coprime (2 ^ n) (Nat.card N) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hN)
  have : orderOf v ∣ 1 := by
    have := Nat.dvd_gcd h1 h2
    rwa [hcop.gcd_eq_one] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)

theorem natCard_conjSub_W (g : G) (A : Subgroup G) : Nat.card ↥(conjSub g A) = Nat.card ↥A :=
  (Nat.card_congr (Subgroup.equivMapOfInjective A (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).toEquiv).symm


@[expose] noncomputable def wImg (Ω : Set (Subgroup G)) (c : G) (Wg : Subgroup G) :
    Subgroup (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) :=
  ((Wg.subgroupOf (Subgroup.centralizer ({c} : Set G))).subgroupOf (coreHull Ω c)).map
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)))

theorem wset_normal {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} (hΦ : HypOmegaGen Φ)
    {V : Subgroup X} (hV : WSet Φ = {V}) : V.Normal := by
  have hW : V ∈ WSet Φ := by rw [hV]; rfl
  refine ⟨fun n hn g => ?_⟩
  have h := conj_mem_conjSub (n := g) hn
  have h2 := WSet.conj hΦ.conjInvariant hW g
  rw [hV] at h2
  have h3 : conjSub g V = V := h2
  rwa [h3] at h

theorem hnorm_of_wImg (hΩ : HypOmegaGen Ω)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {Wg : Subgroup G} (hWE : Wg ≤ rLayer Ω c)
    (hn : (wImg Ω c Wg).Normal) :
    ∀ r ∈ rLayer Ω c, ∀ w ∈ Wg, ∃ w' ∈ Wg, (r * w * r⁻¹)⁻¹ * w' ∈ oddCoreOf (coreLayer Ω c) := by
  intro r hr w hw
  have hLC : rLayer Ω c ≤ coreLayer Ω c := rLayer_le_coreLayer hΩ h2 hc2
  obtain ⟨hCr, hHr⟩ := mem_C_H_of_mem_coreLayer (hLC hr)
  obtain ⟨hCw, hHw⟩ := mem_C_H_of_mem_coreLayer (hLC (hWE hw))
  set ar : ↥(coreHull Ω c) := ⟨⟨r, hCr⟩, hHr⟩ with har
  set aw : ↥(coreHull Ω c) := ⟨⟨w, hCw⟩, hHw⟩ with haw
  have hmem : (QuotientGroup.mk aw : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) ∈
      wImg Ω c Wg := ⟨aw, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hw), rfl⟩
  have hconj := hn.conj_mem _ hmem (QuotientGroup.mk ar)
  obtain ⟨b, hb, hbe⟩ := hconj
  have hb' : ((b : ↥(Subgroup.centralizer ({c} : Set G))) : G) ∈ Wg :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hb)
  refine ⟨((b : ↥(Subgroup.centralizer ({c} : Set G))) : G), hb', ?_⟩
  have heq : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))) b =
      (QuotientGroup.mk ar : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) *
        QuotientGroup.mk aw * (QuotientGroup.mk ar)⁻¹ := hbe
  have heq' : (QuotientGroup.mk b : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) =
      QuotientGroup.mk (ar * aw * ar⁻¹) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact heq
  have hN := QuotientGroup.eq.mp heq'.symm
  have := mem_oddCoreOf_coreLayer hΩ hc2 hN
  simpa [har, haw, mul_assoc] using this

theorem ecase1_of_hnorm (hΩ : HypOmegaGen Ω)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {Wg : Subgroup G} (hW2 : IsPGroup 2 Wg)
    (hWE : Wg ≤ rLayer Ω c)
    (hnorm : ∀ r ∈ rLayer Ω c, ∀ w ∈ Wg, ∃ w' ∈ Wg,
      (r * w * r⁻¹)⁻¹ * w' ∈ oddCoreOf (coreLayer Ω c)) :
    rLayer Ω c ≤ oddCoreOf (rLayer Ω c) ⊔ (rLayer Ω c ⊓ Subgroup.normalizer (Wg : Set G)) := by
  classical
  set E := rLayer Ω c with hE
  set O := oddCoreOf E with hO
  have hOodd : Odd (Nat.card O) := oddCoreOf_odd_natCard E
  have hOE : O ≤ E := oddCoreOf_le_self E
  have hEN : E ≤ Subgroup.normalizer (O : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact Q3AM.conj_mem_oddCoreOf_of_mem_tri hy hx
    · intro hx
      have := Q3AM.conj_mem_oddCoreOf_of_mem_tri (Y := E) (Subgroup.inv_mem E hy) hx
      simpa [mul_assoc] using this
  have hco := Subgroup.coe_mul_of_left_le_normalizer_right Wg O (fun w hw => hEN (hWE hw))
  have hSyl : IsSylow2In Wg (Wg ⊔ O) := by
    refine ⟨le_sup_left, hW2, fun V' hV'Y hV'2 hWV' => ?_⟩
    refine le_antisymm (fun v hv => ?_) hWV'
    have hv' : v ∈ ((Wg ⊔ O : Subgroup G) : Set G) := hV'Y hv
    rw [hco] at hv'
    obtain ⟨w, hw, q, hq, rfl⟩ := hv'
    have hqV : q ∈ V' := by
      have := V'.mul_mem (V'.inv_mem (hWV' hw)) hv
      simpa using this
    have hq1 : q = 1 :=
      eq_one_of_pgroup_odd hV'2 hOodd hqV hq
    show w * q ∈ Wg
    rw [hq1, mul_one]
    exact hw
  intro r hr
  have hrY : conjSub r Wg ≤ Wg ⊔ O := by
    rintro _ ⟨w, hw, rfl⟩
    have e1 : (MulAut.conj r).toMonoidHom w = r * w * r⁻¹ := rfl
    rw [e1]
    obtain ⟨w', hw', hn⟩ := hnorm r hr w hw
    have hzE : (r * w * r⁻¹)⁻¹ * w' ∈ E :=
      E.mul_mem (E.inv_mem (E.mul_mem (E.mul_mem hr (hWE hw)) (E.inv_mem hr))) (hWE hw')
    have hzO : (r * w * r⁻¹)⁻¹ * w' ∈ O := inf_oddCoreOf_coreLayer_le hΩ h2 hc2 ⟨hn, hzE⟩
    have : r * w * r⁻¹ = w' * ((r * w * r⁻¹)⁻¹ * w')⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hw') (Subgroup.mem_sup_right (O.inv_mem hzO))
  obtain ⟨y, hyY, hle⟩ := CFSG.ClassicalInvolution.Asc77.exists_conj_of_isSylow2In hSyl
    (isPGroup_conjSub r hW2) hrY
  have heq : conjSub r Wg = conjSub y Wg :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [natCard_conjSub_W, natCard_conjSub_W])
  have hm : y⁻¹ * r ∈ Subgroup.normalizer (Wg : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, heq, conjSub_inv_conjSub]
  have hyE : y ∈ E := by
    have : Wg ⊔ O ≤ E := sup_le hWE hOE
    exact this hyY
  have hmE : y⁻¹ * r ∈ E := E.mul_mem (E.inv_mem hyE) hr
  have hy' : y ∈ ((Wg ⊔ O : Subgroup G) : Set G) := hyY
  rw [hco] at hy'
  obtain ⟨w₀, hw₀, q, hq, rfl⟩ := hy'
  have hr_eq : r = (w₀ * q * w₀⁻¹) * (w₀ * ((w₀ * q)⁻¹ * r)) := by group
  have h1 : w₀ * q * w₀⁻¹ ∈ O := Q3AM.conj_mem_oddCoreOf_of_mem_tri (hWE hw₀) hq
  have h2' : w₀ * ((w₀ * q)⁻¹ * r) ∈ E ⊓ Subgroup.normalizer (Wg : Set G) :=
    ⟨E.mul_mem (hWE hw₀) hmE,
      Subgroup.mul_mem _ (Subgroup.le_normalizer hw₀) hm⟩
  rw [hr_eq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2')

end EW

section P23

noncomputable abbrev wImage {Y : Type} [Group Y] [Finite Y] (R : Subgroup Y)
    (Wg : Subgroup Y) (e : Y) : Subgroup (SecQ R e) :=
  wImg (Om R) e Wg

@[expose] def P23E4WImg (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' Wg : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' Wg u e g → ¬ SecNoExit R e →
      (∃ V : Subgroup (SecQ R e), WSet (TwinDisc.secFam (Om R) e) = {V}) →
      Wg ≤ rLayer (Om R) e ∧ ∀ V : Subgroup (SecQ R e), WSet (TwinDisc.secFam (Om R) e) = {V} →
        wImage R Wg e = V

theorem p23E4W_of_img {n : ℕ} (hI : P23E4WImg n) : P23E4W n := by
  intro hcit hP Y _ _ R S t K' Wg u e g hc hno hWc
  obtain ⟨hWE, himg⟩ := hI hcit hP Y R S t K' Wg u e g hc hno hWc
  obtain ⟨V, hV⟩ := hWc
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hc2 : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc.data.he2
  have hS := p23_q8Section hc.std.perp hc.data.he2
  have hvn : V.Normal := wset_normal hS.hyp hV
  have hwn : (wImage R Wg e).Normal := by rw [himg V hV]; exact hvn
  have hW2 : IsPGroup 2 Wg := isPGroup_of_mem_WSet hc.std.hW
  exact ecase1_of_hnorm hΩ h2 hc2 hW2 hWE (hnorm_of_wImg hΩ h2 hc2 hWE hwn)

end P23

end W

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
