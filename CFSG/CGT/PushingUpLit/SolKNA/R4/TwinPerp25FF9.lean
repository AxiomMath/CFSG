module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF8
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF5
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF7

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent (coreAt)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2 (imgX)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin (TwinT4Hyp)
open scoped commutatorElement

section Final


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {S₁ : Sylow 2 Y} {R₁ R₂ : Subgroup Y} {t₁ u₁ u₂ : Y}

theorem mem_zStarOf_ff_of_inO2 (hr : 5 ≤ r) (hP : PerpHypR r n Y R S t)
    (hyp : T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t
      t₁ u₁ u₂)
    (h11 : (S₁ : Subgroup Y) ⊓ Subgroup.centralizer ((R₁ ⊔ R₂ : Subgroup Y) : Set Y) =
      Subgroup.zpowers t) {b : Y} (hbS : b ∈ (S₁ : Subgroup Y)) (hb2 : b * b = 1)
    (hF₁ : IsFAut R₁ b) (htC : t ∈ Subgroup.centralizer ({b} : Set Y))
    (hin : TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(Subgroup.centralizer ({b} : Set Y))) (⟨t, htC⟩ : Subgroup.centralizer ({b} : Set Y)))) :
    t ∈ zStarOf (Subgroup.centralizer ({b} : Set Y)) := by
  classical
  have hr4 : 4 ≤ r := by omega
  have hbase := fBase_of_isFAut hr4 hP hyp hbS hF₁
  have hs := hyp.std.setting
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hs.stand.hyp
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := hs.stand.mem
  have h2 : ∀ M ∈ CoreAssembly.conjClass (tightCore R),
      IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hP.core.datum.twoGroup)
  have hq := fBase_quat hr4 hP hyp hbS hF₁
  have hA := aEmpty_fFam hr4 hP hyp h11 hbS hb2 hF₁
  have hT4 : TwinT4Hyp (r - 1) (CentBar b) (famF b (tightCore R) ⊤) :=
    twinT4Hyp_famF hbase h2 hq hA ⊤
  set C : Subgroup Y := Subgroup.centralizer ({b} : Set Y) with hC
  rw [C25W.mem_zStarOf_iff]
  refine ⟨htC, fun y hy => ?_⟩
  set c : Y := y⁻¹ with hc
  have hcC : c ∈ C := C.inv_mem hy
  set s : Y := c * t * c⁻¹ with hsdef
  have hsC : s ∈ C := C.mul_mem (C.mul_mem hcC htC) (C.inv_mem hcC)
  have e : t⁻¹ * y⁻¹ * t * y = t⁻¹ * s := by simp only [hsdef, hc]; group
  rw [e]
  by_contra hcon
  obtain ⟨Q, hQn, hQ2, hzQ⟩ := tightInO2_top hin
  have hsQ : centBarMk b hsC ∈ Q := by
    have h1 := hQn.conj_mem _ hzQ (QuotientGroup.mk' (classicalInvolutionOddCore (CentTop b))
      (topMk ⟨c, hcC⟩))
    have e1 : centBarMk b hsC = QuotientGroup.mk' (classicalInvolutionOddCore (CentTop b))
        (topMk ⟨c, hcC⟩) * QuotientGroup.mk' (classicalInvolutionOddCore (CentTop b))
        (topMk ⟨t, htC⟩) * (QuotientGroup.mk' (classicalInvolutionOddCore (CentTop b))
        (topMk ⟨c, hcC⟩))⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e1]
    exact h1
  obtain ⟨hJc, hzc, hzcm⟩ := hbase.memberData hcC
  have hJ₀ : imgX b ⊤ (tightCore R) ∈ famF b (tightCore R) ⊤ := by
    have := imgX_mem_famF (K := tightCore R) (c := 1) (b := b) (Subgroup.one_mem _) le_top
    rwa [conjSub_eq_self_of_mem (Subgroup.one_mem _)] at this
  have hL : imgX b ⊤ (conjSub c (tightCore R)) ∈ famF b (tightCore R) ⊤ :=
    imgX_mem_famF hcC le_top
  have hu₁ := isUniqueInvolution_imgF hT4 hJ₀ hbase.inv_core htC
  have hv₁ := isUniqueInvolution_imgF hT4 hL
    (isUniqueInvolution_mono hzc (TwinADescent.coreAt_le_left b _) hzcm) hsC
  have hnorm : centBarMk b hsC ∈ Subgroup.normalizer
      ((imgX b ⊤ (tightCore R) : Subgroup (CentBar b)) : Set (CentBar b)) := by
    by_contra hnm
    have := hT4.le_three_of_not_mem_normalizer hJ₀ hL hu₁ hv₁ ⟨Q, hQn, hQ2, hzQ⟩
      ⟨Q, hQn, hQ2, hsQ⟩ hnm
    omega
  obtain ⟨X, hXle, hX2, hX4⟩ := hT4.exists_le_centralizer hJ₀ hL hu₁ hv₁ hQn hQ2 hzQ hsQ hnorm
  obtain ⟨x, hxX, hx4⟩ :=
    exists_orderOf_four_of_uniqueInvolution hu₁ (hXle.trans inf_le_left) hX2 hX4
  have hxJ := (hXle hxX).1
  have hxc := (hXle hxX).2
  obtain ⟨m, hmL, hm4, hmx⟩ := exists_order_four_lift
    (N := classicalInvolutionOddCore (CentTop b))
    (CFSG.ComponentClassification.OddCore.odd_card (CentTop b))
    (L := (((coreAt b (tightCore R)).subgroupOf C).subgroupOf
      (⊤ : Subgroup ↥C))) hxJ hx4
  have hmc : centBarMk b hsC * QuotientGroup.mk' (classicalInvolutionOddCore (CentTop b)) m =
      QuotientGroup.mk' (classicalInvolutionOddCore (CentTop b)) m * centBarMk b hsC := by
    rw [hmx]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hxc).symm
  set N : Subgroup (CentTop b) := classicalInvolutionOddCore (CentTop b) with hN
  set π : CentTop b →* CentBar b := QuotientGroup.mk' N with hπ
  set sT : CentTop b := topMk (⟨s, hsC⟩ : ↥C) with hsT_def
  have hm2 : IsPGroup 2 (Subgroup.zpowers m) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hm4]; norm_num)
  have hsT : sT * sT = 1 :=
    Subtype.ext (Subtype.ext (by
      have : s * s = 1 := hzc.sq
      exact this))
  have hnorm' : ∀ g : CentTop b, g ∈ Subgroup.normalizer (N : Set (CentTop b)) := fun g => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact ⟨fun hh => (inferInstance : N.Normal).conj_mem h hh g, fun hh => by
      have := (inferInstance : N.Normal).conj_mem _ hh g⁻¹
      simpa [mul_assoc] using this⟩
  have hcomm : ∀ r' ∈ Subgroup.zpowers m, ⁅sT, r'⁆ ∈ N := by
    intro r' hr'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr'
    have h1 : π ⁅sT, m ^ k⁆ = 1 := by
      rw [map_commutatorElement, map_zpow]
      have hc' : Commute (π sT) (π m) := hmc
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hc'.zpow_right k).eq
    exact (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨n, hnN, hn⟩ := T7L.exists_conj_centralizes (N := N) (R := Subgroup.zpowers m) hsT
    (CFSG.ComponentClassification.OddCore.odd_card (CentTop b)) hm2 (fun g _ => hnorm' g)
    (hnorm' _) hcomm
  have hm'c : sT * (n * m * n⁻¹) = (n * m * n⁻¹) * sT :=
    (Subgroup.mem_centralizer_singleton_iff.mp
      (hn (conj_mem_conjSub (Subgroup.mem_zpowers m)))).symm
  set ñ : Y := (((n : CentTop b) : ↥C) : Y) with hñ
  set x₀ : Y := (((m : CentTop b) : ↥C) : Y) with hx
  have hx₁c : s * (ñ * x₀ * ñ⁻¹) = (ñ * x₀ * ñ⁻¹) * s := by
    have := congrArg (fun t : CentTop b => ((t : ↥C) : Y)) hm'c
    simpa [hsT_def, hñ, hx] using this
  have hxK : x₀ ∈ tightCore R :=
    TwinADescent.coreAt_le_left b _
      (Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hmL))
  have hx₁mem : ñ * x₀ * ñ⁻¹ ∈ conjSub ñ (tightCore R) := conj_mem_conjSub hxK
  have hx₁ord : orderOf (ñ * x₀ * ñ⁻¹) = 4 := by
    have h1 := MulEquiv.orderOf_eq (MulAut.conj ñ) x₀
    simp only [MulAut.conj_apply] at h1
    rw [h1, hx, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hm4]
  have hñ' : ñ ∈ oddCoreOf C := Subgroup.mem_map.mpr ⟨(n : ↥C), mem_oddCore_of_top hnN, rfl⟩
  have hya : s ≠ ñ * t * ñ⁻¹ := by
    intro heq
    apply hcon
    have h1 := Balance.conj_mem_oddCoreIn (X := C) (x := t⁻¹) (C.inv_mem htC) hñ'
    have h2 := (oddCoreOf C).mul_mem h1 ((oddCoreOf C).inv_mem hñ')
    have e2 : t⁻¹ * (ñ * t * ñ⁻¹) = t⁻¹ * ñ * t⁻¹⁻¹ * ñ⁻¹ := by group
    rw [heq, e2]
    exact h2
  have hJΩ : conjSub ñ (tightCore R) ∈ CoreAssembly.conjClass (tightCore R) :=
    hΩ.conjInvariant ñ _ hK
  exact not_commute_ord4 hyp hJΩ (hbase.inv.conj ñ) (y := c) hya hx₁mem hx₁ord hx₁c

end Final

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
