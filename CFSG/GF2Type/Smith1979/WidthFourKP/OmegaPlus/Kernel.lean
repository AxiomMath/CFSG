module

public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.Orbit
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaMinusSchur
public import CFSG.LargeExtraspecial.S11MbEichler
public import CFSG.LargeExtraspecial.S14Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.OmegaPlus

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S g) in
@[expose] noncomputable def Kt (t : S.O) : Subgroup S.O where
  carrier := {σ | σ ∈ S14.Ct S t ∧ ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v}
  mul_mem' := fun {σ τ} hσ hτ =>
    ⟨(S14.Ct S t).mul_mem hσ.1 hτ.1, fun v hv => by
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hτ.2 v hv, hσ.2 v hv]⟩
  one_mem' := ⟨one_mem _, fun v _ => rfl⟩
  inv_mem' := fun {σ} hσ =>
    ⟨(S14.Ct S t).inv_mem hσ.1, fun v hv => by
      rw [Subgroup.coe_inv]
      change (LinearEquiv.symm (((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))) v = v
      rw [LinearEquiv.symm_apply_eq]
      exact (hσ.2 v hv).symm⟩

theorem mem_Kt {t σ : S.O} : σ ∈ Kt S g t ↔
    σ ∈ S14.Ct S t ∧ ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
  Iff.rfl

theorem self_mem_Kt (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) : t ∈ Kt S g t := by
  have htC : t ∈ S14.Ct S t :=
    Subgroup.mem_inf.mpr ⟨(S.Lbar_le_Mbar g) ht, mem_centralizer_singleton_iff.mpr rfl⟩
  have htN := (mem_Nbar.mp (S6.self_mem_Nbar H ht)).2
  exact mem_Kt.mpr ⟨htC, htN⟩

theorem sub_mem_Vt_of_mem_Kt (hw : S.width = 4) (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) {σ : S.O} (hσ : σ ∈ Kt S g t) (x : S.Qt) :
    (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ Vt S g t := by
  have hσt : σ * t = t * σ := (S8.mem_CMt.mp (mem_Kt.mp hσ).1).2
  have hσV : ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := (mem_Kt.mp hσ).2
  have hv : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ Vt S g t := by
    rw [← (commSpace_t_eq H C ht ht1 hVQ).1]
    exact mem_commSpace.mpr ⟨x, rfl⟩
  have hfix : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x :=
    hσV _ hv
  have hσx : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) x) =
      (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) x) := by
    rw [← coe_mul_apply, ← coe_mul_apply, hσt]
  have h2 : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) x) -
      (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) x = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x := by
    calc (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) x) -
          (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) x
        = (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) x) -
            (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) x := by rw [hσx]
      _ = (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)
            ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) := by rw [map_sub]
      _ = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x := hfix
  have hmemW : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ Wt S g t := by
    rw [← (commSpace_t_eq H C ht ht1 hVQ).2, mem_fixSpace]
    rw [map_sub]
    apply sub_eq_zero.mp
    have h3 : ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) x) -
        (t : S.Qt ≃ₗ[ZMod 2] S.Qt) x) -
        ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) = 0 := by
      have e : ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) x) -
          (t : S.Qt ≃ₗ[ZMod 2] S.Qt) x) -
          ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) =
          ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) x) -
            (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) x) -
            ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) := by abel
      rw [e, h2, sub_self]
    exact h3
  rw [W4Minus.Wt_eq_Vt_w4 hw H ht1 h4] at hmemW
  exact hmemW

theorem Wt_le_ker_sub (hw : S.width = 4) (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (σ : Kt S g t) :
    Wt S g t ≤ LinearMap.ker (LinearMap.codRestrict (Vt S g t)
      (((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)
      (sub_mem_Vt_of_mem_Kt hw H C ht ht1 hVQ h4 σ.2)) := by
  intro w hwm
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  rw [LinearMap.codRestrict_apply]
  change ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w = 0
  rw [W4Minus.Wt_eq_Vt_w4 hw H ht1 h4] at hwm
  rw [(mem_Kt.mp σ.2).2 w hwm, sub_self]

@[expose] noncomputable def endKt (hw : S.width = 4) (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (σ : Kt S g t) : Vt S g t →ₗ[ZMod 2] Vt S g t :=
  ((Wt S g t).liftQ (LinearMap.codRestrict (Vt S g t)
      (((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)
      (sub_mem_Vt_of_mem_Kt hw H C ht ht1 hVQ h4 σ.2))
    (Wt_le_ker_sub hw H C ht ht1 hVQ h4 σ)) ∘ₗ (chi H C ht ht1 hVQ).symm.toLinearMap

theorem endKt_chi (hw : S.width = 4) (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (σ : Kt S g t) (y : S.Qt) :
    (endKt hw H C ht ht1 hVQ h4 σ (chi H C ht ht1 hVQ (Submodule.Quotient.mk y)) : S.Qt) =
      ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y := by
  simp [endKt, Submodule.liftQ_apply]

theorem endKt_injective (hw : S.width = 4) (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) :
    Function.Injective (endKt hw H C ht ht1 hVQ h4) := by
  intro σ τ hστ
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have h := congrArg (fun f : Vt S g t →ₗ[ZMod 2] Vt S g t =>
    f (chi H C ht ht1 hVQ (Submodule.Quotient.mk x))) hστ
  have h2 : ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x =
      ((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x := by
    have h3 := congrArg (fun v : Vt S g t => (v : S.Qt)) h
    rwa [endKt_chi, endKt_chi] at h3
  have h4' := congrArg (fun z : S.Qt => z + x) h2
  simpa [sub_add_cancel] using h4'

theorem endKt_mul (hw : S.width = 4) (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (σ τ : Kt S g t) :
    endKt hw H C ht ht1 hVQ h4 (σ * τ) =
      endKt hw H C ht ht1 hVQ h4 σ + endKt hw H C ht ht1 hVQ h4 τ := by
  apply LinearMap.ext
  intro v
  obtain ⟨y, rfl⟩ : ∃ y, chi H C ht ht1 hVQ (Submodule.Quotient.mk y) = v := by
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective (Wt S g t) ((chi H C ht ht1 hVQ).symm v)
    exact ⟨y, by rw [hy, LinearEquiv.apply_symm_apply]⟩
  apply Subtype.ext
  rw [LinearMap.add_apply]
  change (endKt hw H C ht ht1 hVQ h4 (σ * τ)
      (chi H C ht ht1 hVQ (Submodule.Quotient.mk y)) : S.Qt) =
    (endKt hw H C ht ht1 hVQ h4 σ
      (chi H C ht ht1 hVQ (Submodule.Quotient.mk y)) : S.Qt) +
    (endKt hw H C ht ht1 hVQ h4 τ
      (chi H C ht ht1 hVQ (Submodule.Quotient.mk y)) : S.Qt)
  rw [endKt_chi, endKt_chi, endKt_chi]
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply]
  have hτV : ((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y ∈ Vt S g t :=
    sub_mem_Vt_of_mem_Kt hw H C ht ht1 hVQ h4 τ.2 y
  have hσfix : ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y) =
      ((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y :=
    (mem_Kt.mp σ.2).2 _ hτV
  have hkey : ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y) =
      (((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y) +
        ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y := by
    calc ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
          (((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y)
        = ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
            ((((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y) + y) := by
          rw [sub_add_cancel]
      _ = ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
            (((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y) +
            ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y := by rw [map_add]
      _ = (((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y) +
            ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y := by rw [hσfix]
  rw [hkey]
  abel

theorem endKt_self (hw : S.width = 4) (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) :
    endKt hw H C ht ht1 hVQ h4 ⟨t, self_mem_Kt H ht⟩ = LinearMap.id := by
  apply LinearMap.ext
  intro v
  obtain ⟨y, rfl⟩ : ∃ y, chi H C ht ht1 hVQ (Submodule.Quotient.mk y) = v := by
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective (Wt S g t) ((chi H C ht ht1 hVQ).symm v)
    exact ⟨y, by rw [hy, LinearEquiv.apply_symm_apply]⟩
  apply Subtype.ext
  rw [endKt_chi, LinearMap.id_apply, coe_chi_apply_mk]

theorem beta_endKt_self (hw : S.width = 4) (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (σ : Kt S g t) (v : Vt S g t) :
    beta H C ht ht1 hVQ (endKt hw H C ht ht1 hVQ h4 σ v) v = 0 := by
  obtain ⟨y, hy⟩ := exists_t_sub_eq H C ht ht1 hVQ v
  have hv : chi H C ht ht1 hVQ (Submodule.Quotient.mk y) = v :=
    Subtype.ext (by rw [coe_chi_apply_mk, hy])
  have hfv : endKt hw H C ht ht1 hVQ h4 σ v =
      ⟨((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y,
        sub_mem_Vt_of_mem_Kt hw H C ht ht1 hVQ h4 σ.2 y⟩ := by
    rw [← hv]
    apply Subtype.ext
    rw [endKt_chi]
  rw [hfv]
  rw [beta_apply H C ht ht1 hVQ _ v hy]
  rw [S11.polar_sub_self_eq (σ : S.O).2 y]
  exact q_eq_zero_of_mem_Vt H ht1 (sub_mem_Vt_of_mem_Kt hw H C ht ht1 hVQ h4 σ.2 y)

theorem commute_of_mem_Kt (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) {P : Subgroup S.O} (hPR : P ≤ Rbar S g t)
    (hP3 : ∀ x ∈ P, x ^ 3 = 1) {σ : S.O} (hσ : σ ∈ Kt S g t) {x : S.O} (hx : x ∈ P) :
    σ * x = x * σ := by
  have hσC := (mem_Kt.mp hσ).1
  have hσM : σ ∈ S.Mbar := (S8.mem_CMt.mp hσC).1
  have hσt : σ * t = t * σ := (S8.mem_CMt.mp hσC).2
  have hσV := (mem_Kt.mp hσ).2
  have hxR : x ∈ Rbar S g t := hPR hx
  have hcommN : x * σ * x⁻¹ * σ⁻¹ ∈ Nbar S g t :=
    W4As.comm_mem_Nbar_of_fix H hσM hσt hσV hxR
  have hN := W4As.Nbar_eq_zpowers_omega4 hCE hw H hNo C ht ht1 hVQ hΩ h4
  rw [hN] at hcommN
  have ht2 : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  rcases eq_one_or_eq_of_mem_zpowers ht2 hcommN with h1 | h1
  · have hxσ : x * σ = σ * x := by
      calc x * σ = (x * σ * x⁻¹ * σ⁻¹) * (σ * x) := by group
        _ = 1 * (σ * x) := by rw [h1]
        _ = σ * x := one_mul _
    exact hxσ.symm
  · exfalso
    have h2 : σ * x⁻¹ * σ⁻¹ = x⁻¹ * t := by
      calc σ * x⁻¹ * σ⁻¹ = x⁻¹ * (x * σ * x⁻¹ * σ⁻¹) := by group
        _ = x⁻¹ * t := by rw [h1]
    have hx3 : x ^ 3 = 1 := hP3 x hx
    have hxinv3 : (x⁻¹) ^ 3 = 1 := by rw [inv_pow, hx3, inv_one]
    have hleft : (σ * x⁻¹ * σ⁻¹) ^ 3 = 1 := by
      rw [conj_pow (a := σ) (b := x⁻¹) (i := 3), hxinv3]
      group
    have hxt : x * t = t * x := commute_of_mem_Rbar H.conj_mem hxR
    have ht3 : t ^ 3 = t := by
      rw [pow_succ, pow_two, ht2, one_mul]
    have hright : (x⁻¹ * t) ^ 3 = t := by
      have hcomm : Commute x⁻¹ t := (show Commute x t from hxt).inv_left
      rw [hcomm.mul_pow, hxinv3, ht3, one_mul]
    rw [← h2, hleft] at hright
    exact ht1 hright.symm

theorem endKt_resV (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) {P : Subgroup S.O} (hPR : P ≤ Rbar S g t)
    (hP3 : ∀ x ∈ P, x ^ 3 = 1) (σ : Kt S g t) {x : S.O} (hx : x ∈ P) (v : Vt S g t) :
    endKt hw H C ht ht1 hVQ h4 σ (resV H.conj_mem t ⟨x, hPR hx⟩ v) =
      resV H.conj_mem t ⟨x, hPR hx⟩ (endKt hw H C ht ht1 hVQ h4 σ v) := by
  obtain ⟨y, rfl⟩ : ∃ y, chi H C ht ht1 hVQ (Submodule.Quotient.mk y) = v := by
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective (Wt S g t) ((chi H C ht ht1 hVQ).symm v)
    exact ⟨y, by rw [hy, LinearEquiv.apply_symm_apply]⟩
  apply Subtype.ext
  let xR : Rbar S g t := ⟨x, hPR hx⟩
  rw [← chi_equivariant H C ht ht1 hVQ xR y]
  rw [endKt_chi, coe_resV_apply, endKt_chi, map_sub]
  have hmul : ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) * ((xR : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      ((xR : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) * ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    have hxσ : ((σ : S.O) * (xR : S.O)) = ((xR : S.O) * (σ : S.O)) :=
      commute_of_mem_Kt hCE hw H hNo C ht ht1 hVQ hΩ h4 hPR hP3 σ.2 hx
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hxσ]
  have happ : ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((xR : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y) =
      ((xR : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y) := by
    calc ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((xR : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y)
        = (((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) *
            ((xR : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) y :=
          (LinearEquiv.mul_apply _ _ _).symm
      _ = (((xR : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) *
            ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) y := by rw [hmul]
      _ = ((xR : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y) :=
          LinearEquiv.mul_apply _ _ _
  rw [happ]

theorem card_Kt_le_four (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) {P : Subgroup S.O} (hPR : P ≤ Rbar S g t)
    (hP3 : ∀ x ∈ P, x ^ 3 = 1)
    (hcomm4 : Nat.card {f : Vt S g t →ₗ[ZMod 2] Vt S g t //
      (∀ (x : S.O) (hx : x ∈ P) (v : Vt S g t),
        f (resV H.conj_mem t ⟨x, hPR hx⟩ v) = resV H.conj_mem t ⟨x, hPR hx⟩ (f v)) ∧
      ∀ v, beta H C ht ht1 hVQ (f v) v = 0} ≤ 4) :
    Nat.card (Kt S g t) ≤ 4 := by
  haveI : Finite (Vt S g t →ₗ[ZMod 2] Vt S g t) := Module.finite_of_finite (ZMod 2)
  haveI : Finite {f : Vt S g t →ₗ[ZMod 2] Vt S g t //
      (∀ (x : S.O) (hx : x ∈ P) (v : Vt S g t),
        f (resV H.conj_mem t ⟨x, hPR hx⟩ v) = resV H.conj_mem t ⟨x, hPR hx⟩ (f v)) ∧
      ∀ v, beta H C ht ht1 hVQ (f v) v = 0} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let F : Kt S g t → {f : Vt S g t →ₗ[ZMod 2] Vt S g t //
      (∀ (x : S.O) (hx : x ∈ P) (v : Vt S g t),
        f (resV H.conj_mem t ⟨x, hPR hx⟩ v) = resV H.conj_mem t ⟨x, hPR hx⟩ (f v)) ∧
      ∀ v, beta H C ht ht1 hVQ (f v) v = 0} := fun σ =>
    ⟨endKt hw H C ht ht1 hVQ h4 σ,
      fun x hx v => endKt_resV hCE hw H hNo C ht ht1 hVQ hΩ h4 hPR hP3 σ hx v,
      fun v => beta_endKt_self hw H C ht ht1 hVQ h4 σ v⟩
  have hF : Function.Injective F := by
    intro σ τ h
    exact endKt_injective hw H C ht ht1 hVQ h4 (congrArg Subtype.val h)
  exact (Nat.card_le_card_of_injective F hF).trans hcomm4

theorem mul_self_of_mem_Kt (hw : S.width = 4) (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) {σ : S.O} (hσ : σ ∈ Kt S g t) : σ * σ = 1 := by
  let σK : Kt S g t := ⟨σ, hσ⟩
  have hff : endKt hw H C ht ht1 hVQ h4 σK + endKt hw H C ht ht1 hVQ h4 σK = 0 := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    rw [LinearMap.add_apply]
    change ((endKt hw H C ht ht1 hVQ h4 σK v : Vt S g t) : S.Qt) +
      ((endKt hw H C ht ht1 hVQ h4 σK v : Vt S g t) : S.Qt) = 0
    exact CFSG.LargeExtraspecial.OrthoF2.vec_add_self _
  have h0 : endKt hw H C ht ht1 hVQ h4 (1 : Kt S g t) = 0 := by
    apply LinearMap.ext
    intro v
    obtain ⟨y, rfl⟩ : ∃ y, chi H C ht ht1 hVQ (Submodule.Quotient.mk y) = v := by
      obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective (Wt S g t) ((chi H C ht ht1 hVQ).symm v)
      exact ⟨y, by rw [hy, LinearEquiv.apply_symm_apply]⟩
    apply Subtype.ext
    rw [endKt_chi]
    simp
  have h : endKt hw H C ht ht1 hVQ h4 (σK * σK) =
      endKt hw H C ht ht1 hVQ h4 (1 : Kt S g t) := by
    rw [endKt_mul, hff, h0]
  have hEq : σK * σK = 1 := endKt_injective hw H C ht ht1 hVQ h4 h
  simpa using congrArg Subtype.val hEq

theorem mul_self_of_fix (hw : S.width = 4) (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) :
    ∀ σ ∈ S14.Ct S t, (∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → σ * σ = 1 := by
  intro σ hσ hfix
  exact mul_self_of_mem_Kt hw H C ht ht1 hVQ h4 (mem_Kt.mpr ⟨hσ, hfix⟩)

theorem card_dvd_four_of_fix (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) {P : Subgroup S.O} (hPR : P ≤ Rbar S g t)
    (hP3 : ∀ x ∈ P, x ^ 3 = 1)
    (hcomm4 : Nat.card {f : Vt S g t →ₗ[ZMod 2] Vt S g t //
      (∀ (x : S.O) (hx : x ∈ P) (v : Vt S g t),
        f (resV H.conj_mem t ⟨x, hPR hx⟩ v) = resV H.conj_mem t ⟨x, hPR hx⟩ (f v)) ∧
      ∀ v, beta H C ht ht1 hVQ (f v) v = 0} ≤ 4) :
    ∀ T : Subgroup S.O, T ≤ S14.Ct S t →
      (∀ σ ∈ T, ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → Nat.card T ∣ 4 := by
  intro T hT hfix
  have hTK : T ≤ Kt S g t := fun σ hσ => mem_Kt.mpr ⟨hT hσ, hfix σ hσ⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKp : IsPGroup 2 (Kt S g t) := by
    intro σ
    refine ⟨1, ?_⟩
    have h2 : (σ : Kt S g t) ^ 2 = 1 :=
      Subtype.ext (mul_self_of_mem_Kt hw H C ht ht1 hVQ h4 σ.2)
    rw [show (2 : ℕ) ^ 1 = 2 by norm_num]
    exact h2
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hKp
  have hle : 2 ^ n ≤ 4 := by
    rw [← hn]
    exact card_Kt_le_four hCE hw H hNo C ht ht1 hVQ hΩ h4 hPR hP3 hcomm4
  have hn2 : n ≤ 2 := by
    by_contra h
    push Not at h
    have h3 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h3
    omega
  have hdvdK : Nat.card (Kt S g t) ∣ 4 := by
    rw [hn, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact pow_dvd_pow 2 hn2
  exact (Subgroup.card_dvd_of_le hTK).trans hdvdK

theorem self_mem_of_fix_of_card_eq_four (hCE : CentralExtInput.{0}) (hw : S.width = 4)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) {P : Subgroup S.O} (hPR : P ≤ Rbar S g t)
    (hP3 : ∀ x ∈ P, x ^ 3 = 1)
    (hcomm4 : Nat.card {f : Vt S g t →ₗ[ZMod 2] Vt S g t //
      (∀ (x : S.O) (hx : x ∈ P) (v : Vt S g t),
        f (resV H.conj_mem t ⟨x, hPR hx⟩ v) = resV H.conj_mem t ⟨x, hPR hx⟩ (f v)) ∧
      ∀ v, beta H C ht ht1 hVQ (f v) v = 0} ≤ 4) :
    ∀ T : Subgroup S.O, T ≤ S14.Ct S t →
      (∀ σ ∈ T, ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → Nat.card T = 4 →
        t ∈ T := by
  intro T hT hfix hcard
  have hTK : T ≤ Kt S g t := fun σ hσ => mem_Kt.mpr ⟨hT hσ, hfix σ hσ⟩
  have hKle : Nat.card (Kt S g t) ≤ Nat.card T := by
    rw [hcard]
    exact card_Kt_le_four hCE hw H hNo C ht ht1 hVQ hΩ h4 hPR hP3 hcomm4
  have hEq : T = Kt S g t := Subgroup.eq_of_le_of_card_ge hTK hKle
  rw [hEq]
  exact self_mem_Kt H ht

theorem eq_t_of_fix_of_conj (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) {P : Subgroup S.O} (hPR : P ≤ Rbar S g t)
    (hP3 : ∀ x ∈ P, x ^ 3 = 1)
    (hid : ∀ f : Vt S g t →ₗ[ZMod 2] Vt S g t,
      (∀ (x : S.O) (hx : x ∈ P) (v : Vt S g t),
        f (resV H.conj_mem t ⟨x, hPR hx⟩ v) = resV H.conj_mem t ⟨x, hPR hx⟩ (f v)) →
      (∀ v, beta H C ht ht1 hVQ (f v) v = 0) → Function.Injective f → f = LinearMap.id) :
    ∀ σ ∈ S14.Ct S t, (∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) →
      ∀ m ∈ S.Mbar, σ = m * t * m⁻¹ → σ = t := by
  intro σ hσ hσV m hm hσeq
  have hσK : σ ∈ Kt S g t := mem_Kt.mpr ⟨hσ, hσV⟩
  let σK : Kt S g t := ⟨σ, hσK⟩
  let es : S.Qt ≃ₗ[ZMod 2] S.Qt := ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
  let em : S.Qt ≃ₗ[ZMod 2] S.Qt := ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
  let et : S.Qt ≃ₗ[ZMod 2] S.Qt := ((t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
  let ds : S.Qt →ₗ[ZMod 2] S.Qt := es.toLinearMap - 1
  have hlin : es = em * et * em⁻¹ := by
    change ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) * ((t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) *
        ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹
    rw [hσeq]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hsub : ds = em.toLinearMap.comp ((et.toLinearMap - 1).comp em.symm.toLinearMap) := by
    apply LinearMap.ext
    intro x
    have hσx : es.toLinearMap x = em.toLinearMap (et.toLinearMap (em.symm.toLinearMap x)) := by
      rw [hlin]
      simp [LinearEquiv.mul_apply]
    rw [LinearMap.sub_apply, Module.End.one_apply, hσx, LinearMap.comp_apply,
      LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub]
    simp
  have hrange : LinearMap.range ds = (Vt S g t).map em.toLinearMap := by
    have hcomm := (commSpace_t_eq H C ht ht1 hVQ).1
    rw [hsub, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range,
      Submodule.map_top]
    rw [show LinearMap.range (et.toLinearMap - 1) = Vt S g t from hcomm]
  have hds : ∀ y0 : S.Qt,
      (endKt hw H C ht ht1 hVQ h4 σK
        (chi H C ht ht1 hVQ (Submodule.Quotient.mk y0)) : S.Qt) = ds y0 := by
    intro y0
    rw [endKt_chi]
    rfl
  have hmap : ((endKt hw H C ht ht1 hVQ h4 σK).range).map (Vt S g t).subtype =
      LinearMap.range ds := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨z, rfl⟩ := hw
      obtain ⟨y0, rfl⟩ : ∃ y0, chi H C ht ht1 hVQ (Submodule.Quotient.mk y0) = z := by
        obtain ⟨y0, hy0⟩ :=
          Submodule.Quotient.mk_surjective (Wt S g t) ((chi H C ht ht1 hVQ).symm z)
        exact ⟨y0, by rw [hy0, LinearEquiv.apply_symm_apply]⟩
      exact ⟨y0, (hds y0).symm⟩
    · rintro ⟨y0, rfl⟩
      exact ⟨endKt hw H C ht ht1 hVQ h4 σK (chi H C ht ht1 hVQ (Submodule.Quotient.mk y0)),
        ⟨chi H C ht ht1 hVQ (Submodule.Quotient.mk y0), rfl⟩, hds y0⟩
  have hfr : finrank (ZMod 2) (endKt hw H C ht ht1 hVQ h4 σK).range = 4 := by
    have h1 := Submodule.finrank_map_subtype_eq (Vt S g t)
      (endKt hw H C ht ht1 hVQ h4 σK).range
    rw [hmap, hrange, LinearEquiv.finrank_map_eq, h4] at h1
    omega
  have htop : (endKt hw H C ht ht1 hVQ h4 σK).range = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hfr, h4])
  have hinj : Function.Injective (endKt hw H C ht ht1 hVQ h4 σK) :=
    LinearMap.injective_iff_surjective.mpr (LinearMap.range_eq_top.mp htop)
  have hcommP : ∀ (x : S.O) (hx : x ∈ P) (v : Vt S g t),
      endKt hw H C ht ht1 hVQ h4 σK (resV H.conj_mem t ⟨x, hPR hx⟩ v) =
        resV H.conj_mem t ⟨x, hPR hx⟩ (endKt hw H C ht ht1 hVQ h4 σK v) :=
    fun x hx v => endKt_resV hCE hw H hNo C ht ht1 hVQ hΩ h4 hPR hP3 σK hx v
  have halt : ∀ v, beta H C ht ht1 hVQ (endKt hw H C ht ht1 hVQ h4 σK v) v = 0 :=
    fun v => beta_endKt_self hw H C ht ht1 hVQ h4 σK v
  have hId : endKt hw H C ht ht1 hVQ h4 σK = LinearMap.id := hid _ hcommP halt hinj
  have hIdT : endKt hw H C ht ht1 hVQ h4 ⟨t, self_mem_Kt H ht⟩ = LinearMap.id :=
    endKt_self hw H C ht ht1 hVQ h4
  have hEnd : endKt hw H C ht ht1 hVQ h4 σK =
      endKt hw H C ht ht1 hVQ h4 ⟨t, self_mem_Kt H ht⟩ := by rw [hId, hIdT]
  have hEq : σK = ⟨t, self_mem_Kt H ht⟩ := endKt_injective hw H C ht ht1 hVQ h4 hEnd
  simpa using congrArg Subtype.val hEq

theorem fix_of_commute (H : Hyp4 S g) {t : S.O} {P : Subgroup S.O} (hPR : P ≤ Rbar S g t)
    (hcube : ∀ φ : Vt S g t ≃ₗ[ZMod 2] Vt S g t, (∀ (x : S.O) (hx : x ∈ P),
      φ * resV H.conj_mem t ⟨x, hPR hx⟩ = resV H.conj_mem t ⟨x, hPR hx⟩ * φ) → φ ^ 3 = 1) :
    ∀ c ∈ S14.Ct S t, (∃ k : ℕ, c ^ 2 ^ k = 1) → (∀ x ∈ P, c * x = x * c) →
      ∀ v ∈ Vt S g t, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  intro c hc hpow hcommP v hv
  have hcCM : c ∈ S8.CMt S t := hc
  let φ : Vt S g t ≃ₗ[ZMod 2] Vt S g t := S8.resCV S g H.conj_mem t ⟨c, hcCM⟩
  have hcomm : ∀ (x : S.O) (hx : x ∈ P),
      φ * resV H.conj_mem t ⟨x, hPR hx⟩ =
        resV H.conj_mem t ⟨x, hPR hx⟩ * φ := by
    intro x hx
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    let xR : Rbar S g t := ⟨x, hPR hx⟩
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    change ((φ : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ((resV H.conj_mem t xR) w) : S.Qt) =
      ((resV H.conj_mem t xR) ((φ : Vt S g t ≃ₗ[ZMod 2] Vt S g t) w) : S.Qt)
    rw [S8.coe_resCV_apply, coe_resV_apply, coe_resV_apply, S8.coe_resCV_apply]
    have hcx : ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) * ((xR : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
        ((xR : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) * ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      have hcx' : ((c : S.O) * (xR : S.O)) = ((xR : S.O) * (c : S.O)) := hcommP x hx
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hcx']
    have happ : ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((xR : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
        ((xR : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := by
      calc ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((xR : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w)
          = (((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) *
              ((xR : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) w :=
            (LinearEquiv.mul_apply _ _ _).symm
        _ = (((xR : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) *
              ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) w := by rw [hcx]
        _ = ((xR : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) :=
            LinearEquiv.mul_apply _ _ _
    rw [happ]
  obtain ⟨k, hk⟩ := hpow
  have hφpow : φ ^ 2 ^ k = 1 := by
    have hcpow : (⟨c, hcCM⟩ : S8.CMt S t) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      simpa using hk
    change (S8.resCV S g H.conj_mem t ⟨c, hcCM⟩) ^ 2 ^ k = 1
    rw [← map_pow, hcpow, map_one]
  have h3 : φ ^ 3 = 1 := hcube φ hcomm
  have hgd : φ ^ Nat.gcd 3 (2 ^ k) = 1 := pow_gcd_eq_one.mpr ⟨h3, hφpow⟩
  have hcop : Nat.Coprime 3 (2 ^ k) :=
    Nat.prime_two.coprime_pow_of_not_dvd (m := k) (a := 3) (by norm_num)
  rw [hcop.gcd_eq_one, pow_one] at hgd
  have hφ1 : φ = 1 := hgd
  have hv' : φ ⟨v, hv⟩ = ⟨v, hv⟩ := by rw [hφ1]; rfl
  have h := congrArg (fun w : Vt S g t => (w : S.Qt)) hv'
  rw [S8.coe_resCV_apply] at h
  exact h

end CFSG.GF2Type.Smith1979.OmegaPlus
