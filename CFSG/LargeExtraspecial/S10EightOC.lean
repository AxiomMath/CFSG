module

public import CFSG.LargeExtraspecial.S10EightF
public import CFSG.LargeExtraspecial.S10EightOA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace Dec108

variable {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
include D

theorem exists_ystar (hCE : CentralExtInput.{u}) {F : Frame X} {y : S.O} (hyY : y ∈ Yb)
    (hyL : y ∈ S.Lbar g) (hπy : F.π ⟨y, Lbar_le_Rbar X.ht hyL⟩ = τ₂) {n : S.O}
    (hnN : n ∈ Nbar S g t) {v : S.Qt} (hvP : v ∈ S.clSub (S.QG ⊓ S.Qa g))
    (hvV : v ∉ Vt S g t) (htv : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    ∃ w : S.O, ∃ hw : w ∈ S.Lbar g, F.π ⟨w, Lbar_le_Rbar X.ht hw⟩ = τ₂ ∧
      (w : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v ∧
        ((w * n * w⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = (n : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
  have haQ := X.haQ
  have hnX : n ∈ Xb := D.dec.Nbar_le hCE X hnN
  have hyn : y * n * y⁻¹ = n := by
    rw [← D.dec.comm n hnX y hyY]
    group
  by_cases hyv : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
  · exact ⟨y, hyL, hπy, hyv, by rw [hyn]⟩
  have hya : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v + S.cl (g * S.z * g⁻¹) := by
    rcases mem_span_singleton_zmod2.mp (Lbar_apply_sub_mem_span' haQ hvP hyL) with h | h
    · exact absurd (sub_eq_zero.mp h) hyv
    · exact sub_eq_iff_eq_add'.mp h
  obtain ⟨e, heA, hev⟩ : ∃ e ∈ S.Lbar g ⊓ Nbar S g t, (e : S.Qt ≃ₗ[ZMod 2] S.Qt) v ≠ v := by
    by_contra hcon
    push Not at hcon
    have hmem : v ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S (S.Lbar g ⊓ Nbar S g t) :=
      ⟨hvP, fun x hx => hcon x hx⟩
    rw [clSub_inf_fixSub_Abar X] at hmem
    exact hvV hmem.2
  have hea : (e : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v + S.cl (g * S.z * g⁻¹) := by
    rcases mem_span_singleton_zmod2.mp (Lbar_apply_sub_mem_span' haQ hvP heA.1) with h | h
    · exact absurd (sub_eq_zero.mp h) hev
    · exact sub_eq_iff_eq_add'.mp h
  have hyfa : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) :=
    (Lbar_facts X).1 y hyL
  refine ⟨y * e, mul_mem hyL heA.1, ?_, ?_, ?_⟩
  · have e1 : (⟨y * e, Lbar_le_Rbar X.ht (mul_mem hyL heA.1)⟩ : Rbar S g t) =
        ⟨y, Lbar_le_Rbar X.ht hyL⟩ * ⟨e, Lbar_le_Rbar X.ht heA.1⟩ := rfl
    rw [e1, map_mul, hπy, (F.ker _).mpr heA.2, mul_one]
  · rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hea, map_add, hya, hyfa, add_assoc,
      ZModModule.add_self, add_zero]
  ·
    obtain ⟨k₀, hk₀, hb₀, -⟩ := X.exists_pair
    obtain ⟨-, -, hcomm⟩ :=
      timmesfeld_4_7_b hCE X.H X.hNo X.C X.ht X.ht1 X.hVQ (Or.inr X.hΩ) hk₀ hb₀
    have hc : n⁻¹ * e * n * e⁻¹ ∈ zpowers t :=
      hcomm (Subgroup.commutator_mem_commutator (inv_mem hnN) heA.2)
    have hst : t ∈ vecStab S v := mem_vecStab.mpr htv
    have hcv := mem_vecStab.mp ((zpowers_le.mpr hst) hc)
    have henX : e * n * e⁻¹ ∈ Xb :=
      D.dec.Nbar_le hCE X (conj_mem_Nbar_of_mem_Rbar haQ (Lbar_le_Rbar X.ht heA.1) hnN)
    have e2 : y * e * n * (y * e)⁻¹ = n * (n⁻¹ * e * n * e⁻¹) := by
      have h1 : y * (e * n * e⁻¹) * y⁻¹ = e * n * e⁻¹ := by
        rw [← D.dec.comm _ henX y hyY]
        group
      calc y * e * n * (y * e)⁻¹ = y * (e * n * e⁻¹) * y⁻¹ := by group
        _ = e * n * e⁻¹ := h1
        _ = n * (n⁻¹ * e * n * e⁻¹) := by group
    rw [e2, Subgroup.coe_mul, LinearEquiv.mul_apply, hcv]

omit D in
theorem fix_τ₂_of_sub {F : Frame X} {n w : S.O} (hw : w ∈ S.Lbar g)
    (hπw : F.π ⟨w, Lbar_le_Rbar X.ht hw⟩ = τ₂) {v : S.Qt} (hwv : (w : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hwn : ((w * n * w⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = (n : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
    (hc : (n : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Vt S g t) :
    qf (F.φ ⟨_, hc⟩) = 0 ∧ qf (F.φ ⟨_, hc⟩ + E00) = 0 := by
  refine fix_τ₂_sing _ ?_
  have hwc : (w : S.Qt ≃ₗ[ZMod 2] S.Qt) ((n : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) =
      (n : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v := by
    have e1 : (w : S.Qt ≃ₗ[ZMod 2] S.Qt) ((n : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
        ((w * n * w⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((w : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
      simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, inv_apply_apply_O]
    rw [map_sub, e1, hwv, hwn]
  have hres : resV X.haQ t ⟨w, Lbar_le_Rbar X.ht hw⟩ ⟨_, hc⟩ = ⟨_, hc⟩ :=
    Subtype.ext (by rw [coe_resV_apply]; exact hwc)
  rw [← hπw, ← F.compat, hres]

end Dec108

end CFSG.LargeExtraspecial.S10
