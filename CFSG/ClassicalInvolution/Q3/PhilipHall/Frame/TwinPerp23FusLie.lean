module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23FusSetup
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf7Distinct
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23FusLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23FusSec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Fus

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement


section Img

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem map_syl_eq_secImg (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {J Q : Subgroup G}
    (hJ : J ∈ tqMembers3 Ω c) (hQ : IsSylow2In Q J) (hQc : Q ≤ Subgroup.centralizer ({c} : Set G))
    (h2 : IsPGroup 2 ↥(secImg Ω c J)) :
    (((Q.subgroupOf (Subgroup.centralizer ({c} : Set G))).subgroupOf (coreHull Ω c)).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)))) = secImg Ω c J := by
  classical
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set H := coreHull Ω c with hH
  set N := classicalInvolutionOddCore ↥H with hN
  set Ct : Subgroup ↥H := ((TwinADescent.coreAt c J).subgroupOf C).subgroupOf H with hCt
  set Tt : Subgroup ↥H := (Q.subgroupOf C).subgroupOf H with hTt'
  have hTs : IsSylow2In Q (TwinADescent.coreAt c J) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hJ.2).mpr ⟨hQ, hQc⟩
  have hTt := (hTs.subgroupOf (TwinADescent.coreAt_le_centralizer c J)).subgroupOf
    (le_coreHull hJ)
  have hBeq : secImg Ω c J = Ct.map (QuotientGroup.mk' N) := rfl
  let g : ↥Ct →* ↥(secImg Ω c J) :=
    ((QuotientGroup.mk' N).comp Ct.subtype).codRestrict (secImg Ω c J) (fun x => ⟨x, x.2, rfl⟩)
  have hgs : Function.Surjective g := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hmap := map_sylow_eq_of_isPGroup g hgs h2 (Uniform.sylowOfIsSylow2In hTt)
  apply le_antisymm
  · rw [hBeq]
    exact Subgroup.map_mono hTt.1
  · intro y hy
    have hy' : (⟨y, hy⟩ : ↥(secImg Ω c J)) ∈
        ((Uniform.sylowOfIsSylow2In hTt : Subgroup ↥Ct)).map g := by
      rw [hmap]; trivial
    obtain ⟨s, hs0, hsg⟩ := hy'
    have hs : (s : ↥Ct) ∈ Tt.subgroupOf Ct := by
      rw [← Uniform.coe_sylowOfIsSylow2In hTt]; exact hs0
    exact ⟨((s : ↥Ct) : ↥H), Subgroup.mem_subgroupOf.mp hs, congrArg Subtype.val hsg⟩

theorem exists_of_mem_secImg_syl (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {J Q : Subgroup G}
    (hJ : J ∈ tqMembers3 Ω c) (hQ : IsSylow2In Q J) (hQc : Q ≤ Subgroup.centralizer ({c} : Set G))
    (h2 : IsPGroup 2 ↥(secImg Ω c J))
    {y : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)} (hy : y ∈ secImg Ω c J) :
    ∃ a : ↥(coreHull Ω c), (((a : ↥(Subgroup.centralizer ({c} : Set G))) : G) ∈ Q) ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)) a = y := by
  rw [← map_syl_eq_secImg hc2 hJ hQ hQc h2] at hy
  obtain ⟨a, ha, rfl⟩ := hy
  exact ⟨a, Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp ha), rfl⟩

end Img

section Lie

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem lie_fusion_at (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) (h : PerpHypS n Y R S t)
    {c : Y} {J J' Q Q' : Subgroup Y} {w : Y} (hT : LayerTwins Y R c J J' Q Q' w)
    (hno : SecNoExit R c) :
    ∃ x : Y, x ∈ Subgroup.centralizer ({c} : Set Y) ∧ Odd (orderOf x) ∧
      (∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ (∀ b ∈ Q', x * b = b * x) ∧ (∃ q ∈ Q, x * q ≠ q * x) ∧
      ∀ q ∈ Q, q ^ 2 ≠ 1 → x * q * x⁻¹ ≠ q ∧ x * q * x⁻¹ ≠ q⁻¹ := by
  classical
  have hC := CoreData.of_S h.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hc2' : IsPGroup 2 (Subgroup.zpowers c) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hT.hc2
  have hS := p23_q8Section h hT.hc2
  have hlt := secQ_card_lt h hT.hc1
  obtain ⟨h2all, -, -⟩ := TwinDisc.lifts_of_noExit hP hlt hS hno
  obtain ⟨htC, htY, hzz1⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2' hT.hJ hT.hw
  obtain ⟨htC', htY', hzz2⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2' hT.hJ' hT.hw'
  have hne12 := TwinPerpV3.secImg_ne_of_twin hΩ hc2' hT.hJ hT.hJ' hT.hne hT.hw hT.hw'
  obtain ⟨xb, hxbodd, hxbN, hxbC, ⟨j, hj, hxbj⟩, hxbmove⟩ := lie_fusion_section hcit hP hlt hS hno
    (TwinDisc.secImg_mem_secFam hT.hJ) (TwinDisc.secImg_mem_secFam hT.hJ') hne12 hzz1 hzz2
  set C := Subgroup.centralizer ({c} : Set Y) with hCdef
  set H := TwinDisc.coreHull (Om R) c with hHdef
  set N := classicalInvolutionOddCore ↥H with hNdef
  set π := QuotientGroup.mk' N with hπ
  set A : Subgroup ↥H := (Q.subgroupOf C).subgroupOf H with hAdef
  set B : Subgroup ↥H := (Q'.subgroupOf C).subgroupOf H with hBdef
  have hAmap : A.map π = TwinDisc.secImg (Om R) c J :=
    map_syl_eq_secImg hc2' hT.hJ hT.hQ hT.hQc (h2all _ (TwinDisc.secImg_mem_secFam hT.hJ))
  have hBmap : B.map π = TwinDisc.secImg (Om R) c J' :=
    map_syl_eq_secImg hc2' hT.hJ' hT.hQ' hT.hQ'c (h2all _ (TwinDisc.secImg_mem_secFam hT.hJ'))
  have hNodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥H
  have hA2 : IsPGroup 2 ↥A :=
    (hT.hQ.2.1.comap_of_injective C.subtype C.subtype_injective).comap_of_injective
      H.subtype H.subtype_injective
  have hB2 : IsPGroup 2 ↥B :=
    (hT.hQ'.2.1.comap_of_injective C.subtype C.subtype_injective).comap_of_injective
      H.subtype H.subtype_injective
  have hAQ : ∀ a ∈ A, (((a : ↥H) : ↥C) : Y) ∈ Q := fun a ha =>
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp ha)
  have hBQ : ∀ b ∈ B, (((b : ↥H) : ↥C) : Y) ∈ Q' := fun b hb =>
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hb)
  have hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    Subtype.ext (Subtype.ext (hT.hcomm _ (hAQ a ha) _ (hBQ b hb)))
  have hxA : xb ∈ Subgroup.normalizer ((A.map π : Subgroup (↥H ⧸ N)) : Set (↥H ⧸ N)) := by
    rw [hAmap]; exact hxbN
  have hxB : ∀ b ∈ B, xb * π b = π b * xb := fun b hb =>
    hxbC (π b) (hBmap ▸ ⟨b, hb, rfl⟩)
  obtain ⟨x₂, hx₂odd, hx₂π, hx₂A, hx₂B⟩ :=
    lift_odd_normalizing N hNodd hA2 hB2 hAB hxbodd hxA hxB
  have hTs : IsSylow2In Q (TwinADescent.coreAt c J) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2' hT.hJ.2).mpr ⟨hT.hQ, hT.hQc⟩
  have hqA : ∀ q ∈ Q, ∃ a ∈ A, (((a : ↥H) : ↥C) : Y) = q := by
    intro q hq
    have hqC : q ∈ C := hT.hQc hq
    have hqH : (⟨q, hqC⟩ : ↥C) ∈ H :=
      le_coreHull hT.hJ (Subgroup.mem_subgroupOf.mpr (hTs.1 hq))
    exact ⟨⟨⟨q, hqC⟩, hqH⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hq), rfl⟩
  have hAN : A ⊓ N = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd N hA2 le_rfl
      (hNodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
  refine ⟨(((x₂ : ↥H) : ↥C) : Y), ((x₂ : ↥H) : ↥C).2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hx₂odd
  · intro q hq
    obtain ⟨a, ha, rfl⟩ := hqA q hq
    exact hAQ _ (hx₂A a ha)
  · intro b hb
    obtain ⟨b', hb', rfl⟩ : ∃ b' ∈ B, (((b' : ↥H) : ↥C) : Y) = b := by
      have hbC : b ∈ C := hT.hQ'c hb
      have hTs' : IsSylow2In Q' (TwinADescent.coreAt c J') :=
        (TwinADescent.isSylow2In_coreAt_iff hc2' hT.hJ'.2).mpr ⟨hT.hQ', hT.hQ'c⟩
      have hbH : (⟨b, hbC⟩ : ↥C) ∈ H :=
        le_coreHull hT.hJ' (Subgroup.mem_subgroupOf.mpr (hTs'.1 hb))
      exact ⟨⟨⟨b, hbC⟩, hbH⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hb), rfl⟩
    exact congrArg (fun z : ↥H => (((z : ↥H) : ↥C) : Y)) (hx₂B b' hb')
  · by_contra hcon
    push Not at hcon
    obtain ⟨a, ha, rfl⟩ : ∃ a ∈ A, π a = j := by
      have : j ∈ A.map π := hAmap ▸ hj
      obtain ⟨a, ha, haj⟩ := this
      exact ⟨a, ha, haj⟩
    apply hxbj
    have h1 : (((x₂ : ↥H) : ↥C) : Y) * (((a : ↥H) : ↥C) : Y) =
        (((a : ↥H) : ↥C) : Y) * (((x₂ : ↥H) : ↥C) : Y) := hcon _ (hAQ a ha)
    have h2 : x₂ * a = a * x₂ := Subtype.ext (Subtype.ext h1)
    rw [← hx₂π, ← map_mul, ← map_mul, h2]
  · intro q hq hq2
    obtain ⟨a, ha, rfl⟩ := hqA q hq
    have hja : π a ∈ TwinDisc.secImg (Om R) c J := hAmap ▸ ⟨a, ha, rfl⟩
    have hj2 : (π a) ^ 2 ≠ 1 := by
      intro h
      apply hq2
      have hπa2 : π (a ^ 2) = 1 := by rw [map_pow]; exact h
      have h1 : a ^ 2 ∈ A ⊓ N := ⟨A.pow_mem ha 2, (QuotientGroup.eq_one_iff _).mp hπa2⟩
      rw [hAN, Subgroup.mem_bot] at h1
      have h2 := congrArg (fun z : ↥H => (((z : ↥H) : ↥C) : Y)) h1
      simpa [pow_two] using h2
    obtain ⟨hm1, hm2⟩ := hxbmove _ hja hj2
    constructor
    · intro h
      apply hm1
      have h1 : x₂ * a * x₂⁻¹ = a := Subtype.ext (Subtype.ext h)
      rw [← hx₂π, ← map_inv, ← map_mul, ← map_mul, h1]
    · intro h
      apply hm2
      have h1 : x₂ * a * x₂⁻¹ = a⁻¹ := Subtype.ext (Subtype.ext h)
      rw [← hx₂π, ← map_inv, ← map_mul, ← map_mul, h1, map_inv]

end Lie

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Fus
