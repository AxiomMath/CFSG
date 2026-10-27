module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FSW
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinFusion

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

section SW2


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {S₁ : Sylow 2 Y} {R₁ R₂ : Subgroup Y} {t₁ u₁ u₂ : Y}

theorem exists_order_four_of_quat {P : Subgroup Y} (h : IsQuatSub P) : ∃ w ∈ P, orderOf w = 4 := by
  obtain ⟨k, hk, ⟨e⟩⟩ := h
  refine ⟨((e.symm (QuaternionGroup.xa 0) : ↥P) : Y), (e.symm _).2, ?_⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_xa]

theorem swap_of_conj (hr : 4 ≤ r) (hP : PerpHypR r n Y R S t)
    (hyp : T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t
      t₁ u₁ u₂)
    (h11 : (S₁ : Subgroup Y) ⊓ Subgroup.centralizer ((R₁ ⊔ R₂ : Subgroup Y) : Set Y) =
      Subgroup.zpowers t) {b : Y} (hbS : b ∈ (S₁ : Subgroup Y)) (hb2 : b * b = 1)
    (hF₁ : IsFAut R₁ b) {s : Y} (hsC : s * t = t * s) (hsb : s * b = b * s) (hs2 : s * s = 1)
    (hst : s ≠ t) (hconj : ∃ y : Y, y * t * y⁻¹ = s) : conjSub s (tightCore R) = K' := by
  classical
  obtain ⟨t', hT⟩ := T7F25.Asc77.T7T.exists_hyp25T hyp
  obtain ⟨o, ho, hob, hos⟩ := adjust_to_S₁ hr hP hyp h11 hbS hsC hsb hs2
  set C : Subgroup Y := Subgroup.centralizer ({t} : Set Y) with hC
  have hoC : o ∈ C := Balance.oddCoreIn_le C ho
  have hoodd : Odd (orderOf o) :=
    Odd.of_dvd_nat (Balance.odd_card_oddCoreIn C) (Subgroup.orderOf_dvd_natCard _ ho)
  obtain ⟨hoK, hoK'⟩ := odd_fixes_twins hP hyp hoC hoodd
  obtain ⟨hoiK, hoiK'⟩ := odd_fixes_twins hP hyp (C.inv_mem hoC) (by rwa [orderOf_inv])
  have hotc : o * t = t * o := Subgroup.mem_centralizer_singleton_iff.mp hoC
  have hs's : o * s * o⁻¹ * (o * s * o⁻¹) = 1 := by
    calc o * s * o⁻¹ * (o * s * o⁻¹) = o * (s * s) * o⁻¹ := by group
      _ = 1 := by rw [hs2]; group
  have hs'ne : o * s * o⁻¹ ≠ t := by
    intro h
    apply hst
    have e : s = o⁻¹ * (o * s * o⁻¹) * o := by group
    rw [e, h]
    calc o⁻¹ * t * o = o⁻¹ * (t * o) := by group
      _ = o⁻¹ * (o * t) := by rw [hotc]
      _ = t := by group
  obtain ⟨y₀, hy₀⟩ := hconj
  have hs'conj : ∃ y : Y, y * t * y⁻¹ = o * s * o⁻¹ :=
    ⟨o * y₀, by rw [← hy₀]; group⟩
  have hs'b : o * s * o⁻¹ * b = b * (o * s * o⁻¹) := by
    calc o * s * o⁻¹ * b = o * s * (o⁻¹ * b) := by group
      _ = o * s * (b * o⁻¹) := by rw [(Commute.inv_left (show Commute o b from hob)).eq]
      _ = o * (s * b) * o⁻¹ := by group
      _ = o * (b * s) * o⁻¹ := by rw [hsb]
      _ = (o * b) * s * o⁻¹ := by group
      _ = (b * o) * s * o⁻¹ := by rw [hob]
      _ = b * (o * s * o⁻¹) := by group
  have hsw := swap_R_of_ff hr hP hyp hbS hb2 hF₁ hos hs's hs'ne hs'conj hs'b
  have hs := hyp.std.setting
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hs.stand.hyp
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := hs.stand.mem
  have hK'Ω : K' ∈ CoreAssembly.conjClass (tightCore R) := hs.hK'.1
  obtain ⟨w, hwR, hw4⟩ := exists_order_four_of_quat hT.hqR'
  have hwK' : w ∈ K' := hyp.hR'.2.1 hwR
  have hwJ : w ∈ conjSub (o * s * o⁻¹) (tightCore R) := by
    have h1 : w ∈ conjSub (o * s * o⁻¹) R₁ := by rw [hsw]; exact hwR
    exact (conjSub_mono (n := o * s * o⁻¹) hyp.hR.2.1) h1
  have hKK' : conjSub (o * s * o⁻¹) (tightCore R) = K' :=
    (eq_of_mem_inf_of_four_dvd hΩ (hΩ.conjInvariant _ _ hK) hK'Ω hwJ hwK' (by rw [hw4])).symm.symm
  have e : s = o⁻¹ * (o * s * o⁻¹) * o := by group
  rw [e, Generic.conjSub_mul, Generic.conjSub_mul, hoK, hKK', hoiK']

end SW2

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
