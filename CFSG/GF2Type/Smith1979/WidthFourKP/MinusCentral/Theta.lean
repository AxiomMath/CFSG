module

public import CFSG.LargeExtraspecial.S8A5I
public import CFSG.GF2Type.Smith1979.CaseI25Split
public import CFSG.GF2Type.Smith1979.WidthFourKP.MinusCentral.OmegaThree
public import CFSG.GF2Type.Smith1979.W4AsOmega
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaCases

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4MinusC

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S7
  CFSG.LargeExtraspecial.S8 CFSG.Open Subgroup Module
open CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

section Context

variable (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g) (hNo : NoA2 S g)
  (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hP : ¬ PlusAt H C)

include hΩ h4 hP in
theorem hmin_of_not_plusAt (D : S8.Std H C ht ht1 hVQ) :
    ∀ U : Submodule (ZMod 2) (Vt S g t), finrank (ZMod 2) U = 2 → ∃ u ∈ U, D.Q u ≠ 0 := by
  intro U hU
  by_contra hcon
  push Not at hcon
  apply hP
  refine ⟨t, ht, ht1, hVQ, hΩ, h4, U, hU, fun v hv hv0 => ?_⟩
  exact (D.hsing v hv0).mp (hcon v hv)

include hCE hNo hΩ h4 hP in
theorem isSimpleGroup_RmodN_w4 :
    IsSimpleGroup (RmodN S g t) ∧ ¬ ∀ x y : RmodN S g t, x * y = y * x := by
  obtain ⟨D⟩ := S8.Std.nonempty hCE hNo hΩ
  obtain ⟨hsimple, hnab⟩ :=
    S8.isSimpleGroup_omegaGroup_minus_four D.hQ h4 (hmin_of_not_plusAt H C ht ht1 hVQ hΩ h4 hP D)
  refine ⟨D.hX ▸ hsimple, ?_⟩
  rw [D.hX]
  exact hnab

include hCE hNo hΩ h4 hP in
theorem card_RmodN_w4 : Nat.card (RmodN S g t) = 60 := by
  obtain ⟨D⟩ := S8.Std.nonempty hCE hNo hΩ
  rw [D.hX]
  exact S8.card_omegaGroup_minus_four D.hQ h4 (hmin_of_not_plusAt H C ht ht1 hVQ hΩ h4 hP D)

include hCE hNo hΩ h4 hP in
theorem commutator_RmodN_w4 : ⁅RmodN S g t, RmodN S g t⁆ = RmodN S g t := by
  obtain ⟨hs, hnab⟩ := isSimpleGroup_RmodN_w4 hCE H hNo C ht ht1 hVQ hΩ h4 hP
  have hnab' : ¬ IsMulCommutative (RmodN S g t) := fun h => hnab fun x y => h.is_comm.comm x y
  have h1 := CFSG.GroupTheory.commutator_eq_top_of_isSimpleGroup hs hnab'
  rw [← Subgroup.map_subtype_commutator, h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

include hCE hNo hΩ h4 hP in
theorem map_commutator_resV_w4 :
    (_root_.commutator (Rbar S g t)).map (resV H.conj_mem t) = RmodN S g t := by
  rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_resV,
    commutator_RmodN_w4 hCE H hNo C ht ht1 hVQ hΩ h4 hP]

include hCE hNo hΩ h4 hP in
theorem sixty_dvd_card_commutator_Rbar_w4 :
    60 ∣ Nat.card (⁅Rbar S g t, Rbar S g t⁆ : Subgroup S.O) := by
  have h1 := Subgroup.card_map_dvd (H := _root_.commutator (Rbar S g t)) (resV H.conj_mem t)
  rw [map_commutator_resV_w4 hCE H hNo C ht ht1 hVQ hΩ h4 hP,
    card_RmodN_w4 hCE H hNo C ht ht1 hVQ hΩ h4 hP] at h1
  rw [← Subgroup.map_subtype_commutator,
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact h1

include hCE hw hNo hΩ h4 hP in
theorem Rbar_eq_commutator_sup_w4 : Rbar S g t = ⁅Rbar S g t, Rbar S g t⁆ ⊔ zpowers t := by
  obtain ⟨hs, hnab⟩ := isSimpleGroup_RmodN_w4 hCE H hNo C ht ht1 hVQ hΩ h4 hP
  have hnab' : ¬ IsMulCommutative (RmodN S g t) := fun h => hnab fun x y => h.is_comm.comm x y
  refine le_antisymm ?_ (sup_le (Subgroup.commutator_le_self _) (zpowers_le.mpr
    (Lbar_le_Rbar ht ht)))
  have := CFSG.LargeExtraspecial.S14.Rbar_le_commutator_sup_Nbar H.conj_mem hs hnab'
  rwa [W4As.Nbar_eq_zpowers_omega4 hCE hw H hNo C ht ht1 hVQ hΩ h4] at this

include hCE hw hNo hΩ h4 hP in
theorem exists_mul_of_mem_Rbar_w4 {x : S.O} (hx : x ∈ Rbar S g t) :
    ∃ a ∈ ⁅Rbar S g t, Rbar S g t⁆, ∃ s ∈ zpowers t, x = a * s := by
  have hle : zpowers t ≤ normalizer ((⁅Rbar S g t, Rbar S g t⁆ : Subgroup S.O) : Set S.O) := by
    rw [le_normalizer_iff]
    intro s hs k hk
    have hkR : k ∈ Rbar S g t := Subgroup.commutator_le_self _ hk
    rw [(Case25.commute_zpowers_Rbar H hs hkR).eq, mul_inv_cancel_right]
    exact hk
  have h := coe_mul_of_right_le_normalizer_left _ _ hle
  rw [← Rbar_eq_commutator_sup_w4 hCE hw H hNo C ht ht1 hVQ hΩ h4 hP] at h
  have hx' : x ∈ (↑(Rbar S g t) : Set S.O) := hx
  rw [h] at hx'
  obtain ⟨a, ha, s, hs, rfl⟩ := hx'
  exact ⟨a, ha, s, hs, rfl⟩

include hCE hw hNo hΩ h4 hP in
theorem commutator_commutator_Rbar_w4 :
    ⁅⁅Rbar S g t, Rbar S g t⁆, ⁅Rbar S g t, Rbar S g t⁆⁆ = ⁅Rbar S g t, Rbar S g t⁆ := by
  refine le_antisymm (Subgroup.commutator_le_self _) (Subgroup.commutator_le.mpr ?_)
  intro x hx y hy
  obtain ⟨a, ha, s, hs, rfl⟩ := exists_mul_of_mem_Rbar_w4 hCE hw H hNo C ht ht1 hVQ hΩ h4 hP hx
  obtain ⟨b, hb, s', hs', rfl⟩ := exists_mul_of_mem_Rbar_w4 hCE hw H hNo C ht ht1 hVQ hΩ h4 hP hy
  have haR : a ∈ Rbar S g t := Subgroup.commutator_le_self _ ha
  have hbR : b ∈ Rbar S g t := Subgroup.commutator_le_self _ hb
  have hss' : Commute s s' := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hs
    obtain ⟨k', rfl⟩ := mem_zpowers_iff.mp hs'
    exact Commute.zpow_zpow_self t k k'
  rw [Case25.commutatorElement_mul_mul_of_commute (Case25.commute_zpowers_Rbar H hs hbR) hss'
    (Case25.commute_zpowers_Rbar H hs' haR)]
  exact Subgroup.commutator_mem_commutator ha hb

include hCE hw hNo hΩ h4 hP in
theorem exists_theta_of_omega {ω : Vt S g t ≃ₗ[ZMod 2] Vt S g t} (hωR : ω ∈ RmodN S g t)
    (hω3 : ω ^ 3 = 1) :
    ∃ θ ∈ ⁅Rbar S g t, Rbar S g t⁆, θ ^ 3 = 1 ∧ ∀ v : Vt S g t,
      (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = ((ω v : Vt S g t) : S.Qt) := by
  rw [← map_commutator_resV_w4 hCE H hNo C ht ht1 hVQ hΩ h4 hP] at hωR
  obtain ⟨x, hx, hxω⟩ := hωR
  have hN := W4As.Nbar_eq_zpowers_omega4 hCE hw H hNo C ht ht1 hVQ hΩ h4
  have htt : t * t = 1 := S4.mul_self_of_mem_Lbar S H.conj_mem ht
  have hx3 : ((x ^ 3 : Rbar S g t) : S.O) ∈ Nbar S g t := by
    rw [← resV_eq_one_iff H.conj_mem, map_pow, hxω, hω3]
  rw [hN] at hx3
  have hx6 : x ^ 6 = 1 := by
    apply Subtype.ext
    have h3 : (x : S.O) ^ 3 = 1 ∨ (x : S.O) ^ 3 = t := by
      have := S8.eq_one_or_eq_of_mem_zpowers htt hx3
      rwa [Subgroup.coe_pow] at this
    rw [Subgroup.coe_pow, Subgroup.coe_one, show (6 : ℕ) = 3 * 2 from rfl, pow_mul]
    rcases h3 with h | h
    · rw [h, one_pow]
    · rw [h, pow_two, htt]
  have hxR' : ((x : Rbar S g t) : S.O) ∈ ⁅Rbar S g t, Rbar S g t⁆ := by
    rw [← Subgroup.map_subtype_commutator]
    exact ⟨x, hx, rfl⟩
  refine ⟨((x ^ 4 : Rbar S g t) : S.O), ?_, ?_, fun v => ?_⟩
  · rw [Subgroup.coe_pow]
    exact pow_mem hxR' 4
  · rw [← Subgroup.coe_pow, ← pow_mul,
      show 4 * 3 = 6 * 2 from rfl, pow_mul, hx6, one_pow, Subgroup.coe_one]
  · have h1 : resV H.conj_mem t (x ^ 4) = ω := by
      rw [map_pow, hxω, show 4 = 3 + 1 from rfl, pow_succ, hω3, one_mul]
    rw [← coe_resV_apply H.conj_mem (x ^ 4) v, h1]

include hCE hw hNo hΩ h4 hP in
theorem exists_theta_w4 {b : Vt S g t} (hb0 : b ≠ 0) :
    ∃ θ ∈ ⁅Rbar S g t, Rbar S g t⁆, θ ^ 3 = 1 ∧ (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) b = b ∧
      ∃ v : Vt S g t, (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) v ≠ v := by
  obtain ⟨D⟩ := S8.Std.nonempty hCE hNo hΩ
  obtain ⟨ω, hωΩ, hω3, hω1, hωb⟩ :=
    exists_omega_three_fix D.hQ h4 (hmin_of_not_plusAt H C ht ht1 hVQ hΩ h4 hP D) hb0
  have hωR : ω ∈ RmodN S g t := D.hX ▸ hωΩ
  obtain ⟨θ, hθR, hθ3, hθω⟩ := exists_theta_of_omega hCE hw H hNo C ht ht1 hVQ hΩ h4 hP hωR hω3
  refine ⟨θ, hθR, hθ3, by rw [hθω b, hωb], ?_⟩
  by_contra hcon
  push Not at hcon
  apply hω1
  refine LinearEquiv.ext fun v => Subtype.ext ?_
  rw [← hθω v, hcon v]
  rfl

end Context

end CFSG.GF2Type.Smith1979.W4MinusC
