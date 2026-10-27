module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25SixFam
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinInO2Cent

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement

section Main

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent (coreAt)
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot trivialOnQuot_conjSub)
open CFSG.ClassicalInvolution.T7F25.Asc77 (Hyp23Setting)

variable {Y : Type} [Group Y] [Finite Y]

theorem mem_zStarOf_of_inO2 {r : ℕ} (hr : 4 ≤ r) {Ω : Set (Subgroup Y)} {K K' W : Subgroup Y}
    {z : Y} (hs : Hyp23Setting Ω K K' z) (hW : W ∈ WSet Ω)
    (hE4 : ∀ W' ∈ WSet Ω, MuIsoE4 Ω W')
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup Y, IsSylow2In P M →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (hA : ∀ M ∈ Ω, AEmpty Ω M) {a : Y} (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haK : a ∈ trivialOnQuot K) (hzC : z ∈ Subgroup.centralizer ({a} : Set Y))
    (hin : TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(Subgroup.centralizer ({a} : Set Y))) (⟨z, hzC⟩ : Subgroup.centralizer ({a} : Set Y)))) :
    z ∈ zStarOf (Subgroup.centralizer ({a} : Set Y)) := by
  classical
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hz : IsUniqueInvolution K z := hs.hz
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_mul_self_eq_one ha2 ha1
  set C := Subgroup.centralizer ({a} : Set Y) with hC
  rw [C25W.mem_zStarOf_iff]
  refine ⟨hzC, fun y hy => ?_⟩
  set c : Y := y⁻¹ with hc
  have hcC : c ∈ C := C.inv_mem hy
  set s : Y := c * z * c⁻¹ with hsdef
  have hsC : s ∈ C := C.mul_mem (C.mul_mem hcC hzC) (C.inv_mem hcC)
  have e : z⁻¹ * y⁻¹ * z * y = z⁻¹ * s := by simp only [hsdef, hc]; group
  rw [e]
  by_contra hcon
  have hKtq : K ∈ tqMembers3 Ω a := ⟨hK, haK⟩
  have hacomm : c * a * c⁻¹ = a := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hcC
    calc c * a * c⁻¹ = a * c * c⁻¹ := by rw [← this]
      _ = a := by group
  have hKctq : conjSub c K ∈ tqMembers3 Ω a := by
    refine ⟨hΩ.conjInvariant c K hK, ?_⟩
    have := trivialOnQuot_conjSub haK c
    rwa [hacomm] at this
  have hzs : IsUniqueInvolution (conjSub c K) s := hz.conj c
  obtain ⟨Q, hQn, hQ2, hzQ⟩ := tightInO2_top hin
  have hsQ : centBarMk a hsC ∈ Q := by
    have h1 := hQn.conj_mem _ hzQ (QuotientGroup.mk' (classicalInvolutionOddCore (CentTop a))
      (topMk ⟨c, hcC⟩))
    have e1 : centBarMk a hsC = QuotientGroup.mk' (classicalInvolutionOddCore (CentTop a))
        (topMk ⟨c, hcC⟩) * QuotientGroup.mk' (classicalInvolutionOddCore (CentTop a))
        (topMk ⟨z, hzC⟩) * (QuotientGroup.mk' (classicalInvolutionOddCore (CentTop a))
        (topMk ⟨c, hcC⟩))⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e1]
    exact h1
  obtain ⟨m, hmcore, hm4, hmc⟩ := exists_order_four_cent hr hΩ hc2 h2 hq hA hKtq hKctq hz hzs hzC
    hsC hQn hQ2 hzQ hsQ
  set N : Subgroup (CentTop a) := classicalInvolutionOddCore (CentTop a) with hN
  set π : CentTop a →* CentBar a := QuotientGroup.mk' N with hπ
  set sT : CentTop a := topMk (⟨s, hsC⟩ : ↥C) with hsT_def
  have hm2 : IsPGroup 2 (Subgroup.zpowers m) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hm4]; norm_num)
  have hsT : sT * sT = 1 :=
    Subtype.ext (Subtype.ext (by
      have : s * s = 1 := hzs.sq
      exact this))
  have hnorm : ∀ g : CentTop a, g ∈ Subgroup.normalizer (N : Set (CentTop a)) := fun g => by
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
  obtain ⟨n, hnN, hn⟩ := CFSG.ClassicalInvolution.Asc77.T7L.exists_conj_centralizes (N := N)
    (R := Subgroup.zpowers m) hsT (CFSG.ComponentClassification.OddCore.odd_card (CentTop a)) hm2
    (fun g _ => hnorm g) (hnorm _) hcomm
  have hm'c : sT * (n * m * n⁻¹) = (n * m * n⁻¹) * sT :=
    (Subgroup.mem_centralizer_singleton_iff.mp
      (hn (conj_mem_conjSub (Subgroup.mem_zpowers m)))).symm
  set ñ : Y := (((n : CentTop a) : ↥C) : Y) with hñ
  set x : Y := (((m : CentTop a) : ↥C) : Y) with hx
  have hx₁c : s * (ñ * x * ñ⁻¹) = (ñ * x * ñ⁻¹) * s := by
    have := congrArg (fun t : CentTop a => ((t : ↥C) : Y)) hm'c
    simpa [hsT_def, hñ, hx] using this
  have hxK : x ∈ K := TwinADescent.coreAt_le_left a K hmcore
  have hx₁mem : ñ * x * ñ⁻¹ ∈ conjSub ñ K := conj_mem_conjSub hxK
  have hx₁ord : orderOf (ñ * x * ñ⁻¹) = 4 := by
    have h1 := MulEquiv.orderOf_eq (MulAut.conj ñ) x
    simp only [MulAut.conj_apply] at h1
    rw [h1, hx, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hm4]
  have hñ' : ñ ∈ oddCoreOf C := Subgroup.mem_map.mpr ⟨(n : ↥C), mem_oddCore_of_top hnN, rfl⟩
  have hya : s ≠ ñ * z * ñ⁻¹ := by
    intro heq
    apply hcon
    have h1 := Balance.conj_mem_oddCoreIn (X := C) (x := z⁻¹) (C.inv_mem hzC) hñ'
    have h2 := (oddCoreOf C).mul_mem h1 ((oddCoreOf C).inv_mem hñ')
    have e2 : z⁻¹ * (ñ * z * ñ⁻¹) = z⁻¹ * ñ * z⁻¹⁻¹ * ñ⁻¹ := by group
    rw [heq, e2]
    exact h2
  have hJΩ : conjSub ñ K ∈ Ω := hΩ.conjInvariant ñ K hK
  exact CFSG.ClassicalInvolution.T7F25.Asc77.T7ER.not_commute_of_conj hs hW hE4 hJΩ (hz.conj ñ)
    (y := c) hya hx₁mem hx₁ord hx₁c

end Main


section Standing

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)


variable {Y : Type} [Group Y] [Finite Y]

theorem mem_centralizerModOdd_of_trivialOnQuot {K : Subgroup Y} {a : Y}
    (h : a ∈ trivialOnQuot K) : a ∈ centralizerModOdd ⊤ K := by
  refine ⟨Subgroup.mem_top a, h.1, ?_, h.2⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => Balance.Bootstrap.conj_mem_oddCoreIn_of_mem_normalizer h.1 hy, fun hy => ?_⟩
  have h1 := Balance.Bootstrap.conj_mem_oddCoreIn_of_mem_normalizer
    (Subgroup.inv_mem _ h.1 : a⁻¹ ∈ Subgroup.normalizer (K : Set Y)) hy
  have e : a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y := by group
  rw [e] at h1
  exact h1

theorem TwinStdR.quat_sylow {r n : ℕ} {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    (h : TwinStdR r n Y R S t) (hRc : tightCore R = R) :
    ∀ M ∈ CoreAssembly.conjClass R, ∀ P : Subgroup Y, IsSylow2In P M →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))) := by
  obtain ⟨P₀, hP₀, ⟨e⟩⟩ : ∃ P : Subgroup Y, IsSylow2In P (tightCore R) ∧
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))) :=
    ⟨_, h.datum.sylow_core, ⟨(Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype
      R.subtype_injective).symm.trans h.quat.some⟩⟩
  rw [hRc] at hP₀
  rintro _ ⟨g, rfl⟩
  apply TwinDisc.forall_sylow_iso_of_exists
  exact ⟨conjSub g P₀, hP₀.conj g, ⟨(Subgroup.equivMapOfInjective P₀ (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm.trans e⟩⟩

theorem c25_6R_of_thm4 {r n : ℕ} (hr : 4 ≤ r) (h4 : Thm4RTwinBelow r n)
    (hT : Thm1RTwinInO2 r n) : C25_6R r n := by
  intro Y _ _ R S t h K' W S₁ R₁ R₂ t₁ u₁ u₂ hyp t' _ _ _ _ _ a ha2 ha1 haA _
  classical
  have hStd : TwinStdR r n Y R S t :=
    ⟨h.core.card, h.core.simple, h.core.nonab, h.core.datum, h.core.quat, h.core.gen,
      h.core.oddFree, h.core.hyp, h.core.aEmpty, h.core.twin⟩
  obtain ⟨S₀, hStd₀⟩ := hStd.core
  have hRc : tightCore (tightCore R) = tightCore R := TwinEdge.tightCore_idem R
  have hs : T7F25.Asc77.Hyp23Setting (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' t :=
    hyp.std.setting
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hs.stand.hyp
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := hs.stand.mem
  have h2 : ∀ M ∈ CoreAssembly.conjClass (tightCore R),
      IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass hStd₀.datum.twoGroup
  have hq := hStd₀.quat_sylow hRc
  have hA := h.aEmpty_all
  have hZ : Subgroup.center Y = ⊥ := h.center_eq_bot
  have haS : a ∈ (S₁ : Subgroup Y) := haA.1
  have haR : ∀ x ∈ R₁ ⊔ R₂, x * a = a * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp haA.2 x hx
  have hK'Ω : K' ∈ CoreAssembly.conjClass (tightCore R) := hs.hK'.1
  have hR₁ : IsSylow2In R₁ (tightCore R) :=
    T7F25.Asc77.T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hyp.hR.1 hyp.hR.2.1
  have hR₂ : IsSylow2In R₂ K' :=
    T7F25.Asc77.T7C.isSylow2In_of_mem_RSet_of_le hΩ hK'Ω hyp.hR'.1 hyp.hR'.2.1
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_mul_self_eq_one ha2 ha1
  have haK : a ∈ trivialOnQuot (tightCore R) :=
    TwinADescent3.mem_tq_of_sylCent hΩ h2 hK ⟨R₁, hR₁, fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (haR x (Subgroup.mem_sup_left hx))⟩
  have haK' : a ∈ trivialOnQuot K' :=
    TwinADescent3.mem_tq_of_sylCent hΩ h2 hK'Ω ⟨R₂, hR₂, fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (haR x (Subgroup.mem_sup_right hx))⟩
  have htc : t ∈ Subgroup.centralizer ({a} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hyp.hzS a haS).symm
  have hin := inO2_cent_of_twin_R h4 hT hStd₀ hRc hZ ha2 ha1
    (mem_centralizerModOdd_of_trivialOnQuot haK) htc (K' := K')
    (by rw [hRc]; exact hs.hK') (by rw [hRc]; exact hs.hne) haK'
  exact mem_zStarOf_of_inO2 hr hs hyp.hW hyp.hE4 h2 hq hA ha2 ha1 haK htc hin

theorem c25_6R_of_below {r n : ℕ} (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4RTwinBelow r n)
    (hB : Thm1RTwinBelowR r n) : C25_6R r n :=
  c25_6R_of_thm4 hr h4 (thm1RTwinInO2_of_below hr hNo hB)

end Standing
end CFSG.CGT.PushingUpLit.SolKNA.R4
