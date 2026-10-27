module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.S6ThreeH
public import CFSG.LargeExtraspecial.S9Basic
public import CFSG.LargeExtraspecial.S9Mod

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem two_mul_lt_two_pow {m : ℕ} (hm : 3 ≤ m) : 2 * m < 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ]
    have : 2 ≤ 2 ^ m := Nat.le_self_pow (n := m) (by omega) 2
    omega

theorem mem_Nbar_of_mem_Lbar_mul (H : Hyp4 S g) {t : S.O}
    (hL : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t) {k : S.M}
    (hk : S.ρ k ∈ Rbar S g t) {x : S.O} (hxM : x ∈ S.Mbar)
    (hxk : x * t * x⁻¹ ∈ S.Lbar ((k : G) * g)) : x * t * x⁻¹ ∈ Nbar S g t := by
  have hkt := commute_of_mem_Rbar H.conj_mem hk
  have h1 := (mem_Lbar_mul_iff S k g).mp hxk
  have e : (S.ρ k)⁻¹ * (x * t * x⁻¹) * S.ρ k =
      ((S.ρ k)⁻¹ * x) * t * ((S.ρ k)⁻¹ * x)⁻¹ := by
    calc (S.ρ k)⁻¹ * (x * t * x⁻¹) * S.ρ k =
        ((S.ρ k)⁻¹ * x) * t * ((S.ρ k)⁻¹ * x)⁻¹ * ((S.ρ k)⁻¹ * S.ρ k) := by group
      _ = ((S.ρ k)⁻¹ * x) * t * ((S.ρ k)⁻¹ * x)⁻¹ := by rw [inv_mul_cancel, mul_one]
  rw [e] at h1
  have h2 := hL _ (S.Mbar.mul_mem (inv_mem (Rbar_le_Mbar hk)) hxM) h1
  rw [← e] at h2
  have h3 := conj_mem_Nbar H.conj_mem hkt h2
  have e2 : S.ρ k * ((S.ρ k)⁻¹ * (x * t * x⁻¹) * S.ρ k) * (S.ρ k)⁻¹ = x * t * x⁻¹ := by group
  rwa [e2] at h3

theorem inf_commSpace_eq_bot (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (htr : ∀ v : Vt S g t, v ≠ 0 → ∃ x ∈ RmodN S g t, x (aV ht) = v)
    (hL : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t) {x : S.O}
    (hxM : x ∈ S.Mbar)
    (hβ : ∀ k : S.M, S.ρ k ∈ Rbar S g t → x * t * x⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t) :
    Vt S g t ⊓ commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hvV, hvτ⟩
  rw [Submodule.mem_bot]
  by_contra hv0
  obtain ⟨k', hk'L, hk'v⟩ := exists_point_of_mem_commSpace H C ht ht1 hVQ htr hxM hvτ hv0
  obtain ⟨k, hk, hkv⟩ := exists_of_mem_orbit (mem_orbit_of_ne_zero ht htr hvV hv0) H.conj_mem
  have hLeq := Lbar_eq_of_cl_eq S (conj_mem_QG' S k'.2 H.conj_mem) (conj_ne_z' S k'.2 H.conj_ne)
    (conj_mem_QG' S k.2 H.conj_mem) (hkv.symm.trans hk'v)
  rw [← hLeq] at hk'L
  exact hβ k hk ⟨hk'L, mem_Nbar_of_mem_Lbar_mul H hL hk hxM hk'L⟩

theorem fix_Vt_of_inf_eq_bot (H : Hyp4 S g) {t τ : S.O} (hτM : τ ∈ S.Mbar)
    (hτt : τ * t = t * τ)
    (hinf : Vt S g t ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥) :
    ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  intro v hv
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hτM
  have h1 := apply_mem_Vt H.conj_mem hτt hv
  have h2 : ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈
      Vt S g t ⊓ commSpace ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    ⟨sub_mem h1 hv, sub_mem_commSpace _ v⟩
  rw [hinf, Submodule.mem_bot, sub_eq_zero] at h2
  exact h2

section Two

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hSp : SpCase H C ht ht1 hVQ) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include hCE H hNo C ht ht1 hVQ hSp hh hb

theorem apply_sub_mem_Vone_of_fix (h6 : 6 ≤ finrank (ZMod 2) (Vt S g t)) {x : S.O}
    (hxM : x ∈ S.Mbar) (hτt : x * t * x⁻¹ * t = t * (x * t * x⁻¹))
    (hτV : ∀ v ∈ Vt S g t, ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) {w : S.Qt}
    (hw : w ∈ Wone S g t g ((h : G) * g)) :
    ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vone S g t g ((h : G) * g) := by
  have hτM' : x * t * x⁻¹ ∈ S.Mbar :=
    S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have hcomm : commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (Vt S g t).map (x : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap := by
    rw [S8.commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1]
  generalize x * t * x⁻¹ = τ at hτt hτV hτM' hcomm ⊢
  have hτM := hτM'
  set X := Vone S g t g ((h : G) * g) with hX
  set Y := Wone S g t g ((h : G) * g) with hY
  obtain ⟨ρ, hρ, hD⟩ := timmesfeld_6_3_three hCE H hNo C ht ht1 hVQ hSp hh hb
  have hτY : ∀ w ∈ Y, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Y := fun w hw =>
    apply_mem_Wone_of_commute hCE H hNo C ht ht1 hVQ hSp hh hb hτM hτt hw
  set E : Submodule (ZMod 2) S.Qt := Y.map ((τ : S.Qt →ₗ[ZMod 2] S.Qt) - 1) with hE
  have hEY : E ≤ Y := by
    rintro _ ⟨w, hw, rfl⟩
    exact sub_mem (hτY w hw) hw
  set U : Submodule (ZMod 2) ↥(Y.map X.mkQ) := (E.map X.mkQ).comap (Y.map X.mkQ).subtype
    with hU
  have hUinv : ∀ e, ∀ u ∈ U, ρ e u ∈ U := by
    intro e u hu
    obtain ⟨_, ⟨w, hw, rfl⟩, hwe⟩ := hu
    have heR : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ RmodN S g t := by
      rw [hSp.eq_sp]
      exact e.2
    rw [← range_resV H.conj_mem t] at heR
    obtain ⟨r, hr⟩ := heR
    have hw₁ : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Y := sub_mem (hτY w hw) hw
    have hu' : u = secMk X hw₁ := Subtype.ext (by
      rw [coe_secMk]
      simp only [Submodule.coe_subtype, LinearMap.sub_apply, Module.End.one_apply,
        LinearEquiv.coe_coe] at hwe
      exact hwe.symm)
    rw [hu']
    have hrY : ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Y :=
      apply_mem_Wone hCE H hNo C ht ht1 hVQ hSp hh hb r.2 hw
    refine ⟨_, ⟨((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w, hrY, rfl⟩, ?_⟩
    rw [Submodule.coe_subtype, hρ e r hr.symm _ hw₁]
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe]
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hτM
    have hτR : τ * r * τ⁻¹ ∈ Rbar S g t := by
      have := conj_mem_Rbar (k := k) (by rw [hk]; exact hτt) r.2
      rwa [hk] at this
    have hn : τ * r * τ⁻¹ * (r : S.O)⁻¹ ∈ Nbar S g t := by
      refine mem_Nbar.mpr ⟨mul_mem hτR (inv_mem r.2), fun v hv => ?_⟩
      have hv' := apply_mem_Vt_of_mem_Rbar H.conj_mem (inv_mem r.2) hv
      have hτinv : ((τ⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((((r : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
            (((r : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
        conv_lhs => rw [← hτV _ hv']
        exact inv_apply_apply_O τ _
      rw [coe_mul_apply, coe_mul_apply, coe_mul_apply, hτinv, apply_inv_apply_O, hτV v hv]
    have hrτY : ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w) ∈ Y :=
      apply_mem_Wone hCE H hNo C ht ht1 hVQ hSp hh hb r.2 (hτY w hw)
    have h1 := Nbar_apply_sub_mem_Vone hCE H hNo C ht ht1 hVQ hSp hh hb hn hrτY
    have e1 : (((τ * r * τ⁻¹ * (r : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w))) =
        (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) (((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := by
      rw [coe_mul_apply, coe_mul_apply, coe_mul_apply, inv_apply_apply_O, inv_apply_apply_O]
    rw [e1] at h1
    rw [eq_comm, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, map_sub,
      sub_sub_sub_cancel_right]
    have := neg_mem h1
    rwa [neg_sub] at this
  have hU0 : U = ⊥ := by
    by_contra hne
    obtain ⟨m, hm⟩ := even_finrank_Vt H C ht ht1 hVQ
    have h1 : 2 ^ m ≤ finrank (ZMod 2) U :=
      pow_le_finrank_of_invariant ρ (beta_isAlt H C ht ht1 hVQ)
        (beta_nondegenerate H C ht ht1 hVQ) (m := m) (by omega) (by omega)
        (beta_aV_bV H C ht ht1 hVQ hh hb) hD hUinv hne
    have h2 : finrank (ZMod 2) U ≤ finrank (ZMod 2) E := by
      have e1 := Submodule.finrank_map_le ((Y.map X.mkQ).subtype) U
      have e2 : U.map (Y.map X.mkQ).subtype ≤ E.map X.mkQ := Submodule.map_comap_le _ _
      have e3 := Submodule.finrank_mono e2
      have e4 := Submodule.finrank_map_le X.mkQ E
      have e5 : finrank (ZMod 2) (U.map (Y.map X.mkQ).subtype) = finrank (ZMod 2) U :=
        LinearEquiv.finrank_eq
          (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) U).symm
      omega
    have h3 : finrank (ZMod 2) E ≤ finrank (ZMod 2) (Vt S g t) := by
      have e1 : E ≤ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
        rintro _ ⟨w, -, rfl⟩
        exact LinearMap.mem_range_self _ w
      have e2 := Submodule.finrank_mono e1
      rw [hcomm, LinearEquiv.finrank_map_eq] at e2
      exact e2
    have h4 := two_mul_lt_two_pow (m := m) (by omega)
    omega
  have hw₁ : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Y := sub_mem (hτY w hw) hw
  have hmem : secMk X hw₁ ∈ U := ⟨_, ⟨w, hw, rfl⟩, by simp [coe_secMk]⟩
  rw [hU0, Submodule.mem_bot] at hmem
  have := congrArg Subtype.val hmem
  rw [coe_secMk, Submodule.coe_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  exact this

end Two

end CFSG.LargeExtraspecial.S9
