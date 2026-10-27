module

public import CFSG.LargeExtraspecial.S9RACaseB
public import CFSG.LargeExtraspecial.S9RANQ
public import CFSG.LargeExtraspecial.S9RAType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

section CaseB

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hSp : SpCase H C ht ht1 hVQ) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include hCE H hNo C ht ht1 hVQ hSp hh hb

theorem mul_eq_one_or_conj_of_caseB' [hN : NQHyp S g t] (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (hL : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    (hr2 : finrank (ZMod 2) (nqSub S g t (Fbar S g t)) = 2) {y w₁ w₂ : S.O} (hyM : y ∈ S.Mbar)
    (hw₁M : w₁ ∈ S.Mbar) (hw₂M : w₂ ∈ S.Mbar)
    (hw₁ : (w₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ∈
      (Vt S g t).map (y : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap)
    (hw₂ : (w₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ∈
      (Vt S g t).map (y : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap)
    {f₁ f₂ : S.O} (hf₁ : f₁ ∈ Fbar S g t) (hf₂ : f₂ ∈ Fbar S g t) :
    w₁ * f₁ * w₁⁻¹ * (w₂ * f₂ * w₂⁻¹) = 1 ∨
      ∃ x ∈ S.Mbar, w₁ * f₁ * w₁⁻¹ * (w₂ * f₂ * w₂⁻¹) = x * t * x⁻¹ := by
  have haQ := H.conj_mem
  have hpt : ∀ {w : S.O}, w ∈ S.Mbar → (w : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ∈
      (Vt S g t).map (y : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap → ∀ {f : S.O}, f ∈ Fbar S g t →
      ∃ r ∈ Rbar S g t, ∃ f' ∈ Fbar S g t, w * f * w⁻¹ = y * (r * f' * r⁻¹) * y⁻¹ := by
    intro w hwM hw f hf
    obtain ⟨v, hvV, hv⟩ := hw
    have hv0 : v ≠ 0 := by
      rintro rfl
      rw [LinearEquiv.coe_coe, map_zero] at hv
      exact cl_conj_z_ne_zero S haQ H.conj_ne
        ((LinearEquiv.map_eq_zero_iff _).mp hv.symm)
    obtain ⟨r, hr, hrv⟩ := mem_orbit_of_ne_zero ht hSp.transitive hvV hv0
    have hyw : ((y⁻¹ * w : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
        (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
      rw [coe_mul_apply, ← hv, LinearEquiv.coe_coe, inv_apply_apply_O, hrv]
    obtain ⟨f', hf'F, hf'⟩ := conj_Fbar_eq_of_apply_eq H (S.Mbar.mul_mem (inv_mem hyM) hwM)
      (Rbar_le_Mbar hr) hyw hf
    refine ⟨r, hr, f', hf'F, ?_⟩
    calc w * f * w⁻¹ = y * ((y⁻¹ * w) * f * (y⁻¹ * w)⁻¹) * y⁻¹ := by group
      _ = y * (r * f' * r⁻¹) * y⁻¹ := by rw [hf']
  obtain ⟨r₁, hr₁, f₁', hf₁', e₁⟩ := hpt hw₁M hw₁ hf₁
  obtain ⟨r₂, hr₂, f₂', hf₂', e₂⟩ := hpt hw₂M hw₂ hf₂
  have hcase := mul_eq_one_or_conj_of_caseB hCE H hNo C ht ht1 hVQ hSp hh hb h4 hL hr2 hr₁ hr₂
    hf₁' hf₂'
  rw [e₁, e₂]
  rcases hcase with h1 | ⟨x, hxM, hx⟩
  · left
    calc y * (r₁ * f₁' * r₁⁻¹) * y⁻¹ * (y * (r₂ * f₂' * r₂⁻¹) * y⁻¹) =
        y * (r₁ * f₁' * r₁⁻¹ * (r₂ * f₂' * r₂⁻¹)) * y⁻¹ := by group
      _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
  · right
    refine ⟨y * x, S.Mbar.mul_mem hyM hxM, ?_⟩
    calc y * (r₁ * f₁' * r₁⁻¹) * y⁻¹ * (y * (r₂ * f₂' * r₂⁻¹) * y⁻¹) =
        y * (r₁ * f₁' * r₁⁻¹ * (r₂ * f₂' * r₂⁻¹)) * y⁻¹ := by group
      _ = y * x * t * (y * x)⁻¹ := by rw [hx]; group

theorem commute_Fbar_of_typeII [hN : NQHyp S g t] (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (hL : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    (hr2 : finrank (ZMod 2) (nqSub S g t (Fbar S g t)) = 2)
    {x : S.O} (hxM : x ∈ S.Mbar) (hτt : x * t * x⁻¹ * t = t * (x * t * x⁻¹))
    (hβ : ∀ k : S.M, S.ρ k ∈ Rbar S g t → x * t * x⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t)
    {f : S.O} (hf : f ∈ Fbar S g t) : x * t * x⁻¹ * f = f * (x * t * x⁻¹) := by
  have haQ := H.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have hN0 := Nbar_eq_N0bar_of_spCase hCE H hNo C ht ht1 hVQ hSp
  have hD := timmesfeld_6_5_sp H hNo C ht ht1 hVQ hSp hN0 hh hb
  have hτM : x * t * x⁻¹ ∈ S.Mbar :=
    S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have hinf := inf_commSpace_eq_bot H C ht ht1 hVQ hSp.transitive hL hxM hβ
  have hτV := fix_Vt_of_inf_eq_bot H hτM hτt hinf
  have hτK : x * t * x⁻¹ ∈ S8.CMt S t := S8.mem_CMt.mpr ⟨hτM, hτt⟩
  have hτfix : ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl (((1 : S.M) : G) * g * S.z * (((1 : S.M) : G) * g)⁻¹)) =
        S.cl (((1 : S.M) : G) * g * S.z * (((1 : S.M) : G) * g)⁻¹) := by
    simpa using hτV _ (cl_a_mem_Vt ht)
  have hτN := mem_normalizer_of_fix haQ H.conj_ne (h := 1) hτM hτfix
  simp only [OneMemClass.coe_one, one_mul] at hτN
  have hFN : conjL S g t ⊆ Nbar S g t := by
    rintro τ ⟨hτL, y, hyM, rfl⟩
    exact hL y hyM hτL
  have hFle : Fbar S g t ≤ Nbar S g t := Fbar_le_of_subset hFN
  have hlev := exists_levi_pair (nqRep S g t hSp.eq_sp) (beta_isAlt H C ht ht1 hVQ)
    (beta_nondegenerate H C ht ht1 hVQ) h4 (beta_aV_bV H C ht ht1 hVQ hh hb) hD
  obtain ⟨ex, ey, hex, hey, hexx, heyy, hlevi⟩ := hlev
  have hσR : ∀ r ∈ Rbar S g t, ((⟨_, hτK⟩ : S8.CMt S t) : S.O) * r *
      ((⟨_, hτK⟩ : S8.CMt S t) : S.O)⁻¹ * r⁻¹ ∈ Nbar S g t := fun r hr =>
    comm_mem_Nbar_of_fix haQ hτM hτt hτV hr
  have hUfix := nqSub_Fbar_le_fixOf hCE H hNo C ht ht1 hVQ hSp hh hb
  have hσσ : (⟨_, hτK⟩ : S8.CMt S t) * ⟨_, hτK⟩ = 1 := Subtype.ext (by
    change x * t * x⁻¹ * (x * t * x⁻¹) = 1
    calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [htt, mul_one, mul_inv_cancel])
  have a1 : ∀ u ∈ nqSub S g t (Fbar S g t), nqLinC (g := g) (⟨_, hτK⟩ : S8.CMt S t) u ∈
      nqSub S g t (Fbar S g t) := fun u hu =>
    nqLinC_mem_nqSub (⟨_, hτK⟩ : S8.CMt S t) (fun f hf => conj_mem_Fbar hτM hτN hf) hu
  have a2 : ∀ u ∈ nqSub S g t (Fbar S g t), nqRep S g t hSp.eq_sp ex u ∈
      nqSub S g t (Fbar S g t) := fun u hu => nqRep_mem_nqSub_Fbar H C ht ht1 hVQ hSp hex hu
  have a3 : ∀ u ∈ nqSub S g t (Fbar S g t), nqRep S g t hSp.eq_sp ey u ∈
      nqSub S g t (Fbar S g t) := fun u hu => nqRep_mem_nqSub_Fbar H C ht ht1 hVQ hSp hey hu
  have a4 : ∀ u ∈ nqSub S g t (Fbar S g t), nqRep S g t hSp.eq_sp ex u = u →
      nqRep S g t hSp.eq_sp ey u = u → u = 0 := fun u hu hxu hyu => hlevi u (hUfix hu) hxu hyu
  have htriv := nqLinC_eq_of_levi hSp.eq_sp (⟨_, hτK⟩ : S8.CMt S t) hσσ hσR hr2 a1 ex ey hexx
    heyy a2 a3 a4
  have h1 := htriv (nqMk ⟨f, hFle hf⟩) ⟨⟨f, hFle hf⟩, hf, rfl⟩
  have hnc : ∀ y : S.O, y * ((⟨_, hτK⟩ : S8.CMt S t) : S.O) * y⁻¹ ≠
      ((⟨_, hτK⟩ : S8.CMt S t) : S.O) * t := fun y hy =>
    conj_ne_mul_t_of_typeII H C ht ht1 hVQ hSp.transitive hL hxM hτt hβ (y * x) (by
      rw [← hy]; change y * x * t * (y * x)⁻¹ = y * (x * t * x⁻¹) * y⁻¹; group)
  exact commute_of_nqLinC_eq htt _ hnc ⟨f, hFle hf⟩ h1

theorem false_of_caseB [hN : NQHyp S g t] (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (hL : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    (hr2 : finrank (ZMod 2) (nqSub S g t (Fbar S g t)) = 2)
    {x : S.O} (hxM : x ∈ S.Mbar) (hτt : x * t * x⁻¹ * t = t * (x * t * x⁻¹))
    (hβ : ∀ k : S.M, S.ρ k ∈ Rbar S g t → x * t * x⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t) :
    False := by
  have haQ := H.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have hFN : conjL S g t ⊆ Nbar S g t := by
    rintro τ ⟨hτL, y, hyM, rfl⟩
    exact hL y hyM hτL
  have hkey : ∀ τ ∈ conjL S g t, τ ≠ t → ∃ y ∈ S.Mbar, y * τ * y⁻¹ = τ * t := by
    rintro τ ⟨hτL, y, hyM, rfl⟩ hne
    obtain ⟨n, hn, hnτ⟩ := exists_conj_eq_mul_t hCE H hNo C ht ht1 hVQ hSp hyM
      ⟨hτL, hL y hyM hτL⟩ hne
    exact ⟨n, Rbar_le_Mbar (Nbar_le_Rbar hn), hnτ⟩
  have hsym := typeII_symm H C ht ht1 hVQ hSp.transitive hL hxM hτt hβ
  have hcomF : ∀ φ ∈ Fbar S g t, t * (x * φ * x⁻¹) = x * φ * x⁻¹ * t := by
    intro φ hφ
    have h1 := commute_Fbar_of_typeII hCE H hNo C ht ht1 hVQ hSp hh hb h4 hL hr2
      (inv_mem hxM) hsym.1 hsym.2 hφ
    calc t * (x * φ * x⁻¹) = x * (x⁻¹ * t * x⁻¹⁻¹ * φ) * x⁻¹ := by group
      _ = x * (φ * (x⁻¹ * t * x⁻¹⁻¹)) * x⁻¹ := by rw [h1]
      _ = x * φ * x⁻¹ * t := by group
  have hconjF : ∀ φ ∈ Fbar S g t, φ ≠ 1 → ∃ y ∈ S.Mbar, x * φ * x⁻¹ = y * t * y⁻¹ := by
    intro φ hφ hφ1
    rcases mem_conjL_of_mem_Fbar H C ht hkey hφ with h1 | ⟨-, y, hyM, rfl⟩
    · exact absurd h1 hφ1
    · exact ⟨x * y, S.Mbar.mul_mem hxM hyM, by group⟩
  have hne : nqSub S g t (Fbar S g t) ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at hr2
    exact absurd hr2 (by norm_num)
  have hu := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨u, ⟨n₀, hn₀F, hn₀u⟩, hu0⟩ := hu
  subst hn₀u
  have hφ₀t : (n₀ : S.O) ∉ zpowers t := fun h => hu0 ((nqMk_eq_zero_iff n₀).mpr h)
  generalize hφ₀ : (n₀ : S.O) = φ₀ at hn₀F hφ₀t
  have hφ₀1 : φ₀ ≠ 1 := fun h => hφ₀t (h ▸ one_mem _)
  have htφ₀1 : t * φ₀ ≠ 1 := fun h => hφ₀t (by
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right htt]
    exact mem_zpowers t)
  have htφ₀F : t * φ₀ ∈ Fbar S g t := mul_mem (self_mem_Fbar ht) hn₀F
  have hcomm : t * φ₀ = φ₀ * t :=
    Lbar_comm S haQ ht ((Fbar_le_Lbar : Fbar S g t ≤ S.Lbar g) hn₀F)
  have hB2 : ∃ φ ∈ Fbar S g t, φ ≠ 1 ∧ ∃ k : S.M, S.ρ k ∈ Rbar S g t ∧
      x * φ * x⁻¹ ∈ S.Lbar ((k : G) * g) ⊓ Nbar S g t := by
    obtain ⟨y₂, hy₂M, hy₂⟩ := hconjF φ₀ hn₀F hφ₀1
    obtain ⟨y₃, hy₃M, hy₃⟩ := hconjF (t * φ₀) htφ₀F htφ₀1
    by_contra hcon
    push Not at hcon
    have hβ₂ : ∀ k : S.M, S.ρ k ∈ Rbar S g t →
        y₂ * t * y₂⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t := fun k hk => by
      rw [← hy₂]; exact hcon φ₀ hn₀F hφ₀1 k hk
    have hβ₃ : ∀ k : S.M, S.ρ k ∈ Rbar S g t →
        y₃ * t * y₃⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t := fun k hk => by
      rw [← hy₃]; exact hcon (t * φ₀) htφ₀F htφ₀1 k hk
    have h₂t : y₂ * t * y₂⁻¹ * t = t * (y₂ * t * y₂⁻¹) := by
      rw [← hy₂]; exact (hcomF φ₀ hn₀F).symm
    have h₃t : y₃ * t * y₃⁻¹ * t = t * (y₃ * t * y₃⁻¹) := by
      rw [← hy₃]; exact (hcomF _ htφ₀F).symm
    refine false_of_triple hCE H hNo C ht ht1 hVQ hSp hh hb h4 hL hxM hy₂M hy₃M hτt h₂t h₃t
      hβ hβ₂ hβ₃ ?_ ?_
    · rw [← hy₂]
      calc x * t * x⁻¹ * (x * φ₀ * x⁻¹) = x * (t * φ₀) * x⁻¹ := by group
        _ = x * (φ₀ * t) * x⁻¹ := by rw [hcomm]
        _ = x * φ₀ * x⁻¹ * (x * t * x⁻¹) := by group
    · intro w _
      have e : y₃ * t * y₃⁻¹ = x * t * x⁻¹ * (y₂ * t * y₂⁻¹) := by
        rw [← hy₂, ← hy₃]; group
      rw [e, coe_mul_apply, sub_self]
      exact zero_mem _
  obtain ⟨φ, hφF, hφ1, k, hk, hfA⟩ := hB2
  have hy := hconjF φ hφF hφ1
  obtain ⟨y, hyM, hfy⟩ := hy
  have hcomm_y : commSpace ((y * t * y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (Vt S g t).map (y : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap := by
    rw [S8.commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1]
  have hw₁ : ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ∈
      (Vt S g t).map (y : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap := by
    rw [ρ_cl_conj_z S k haQ, ← hcomm_y]
    have h1 := cl_mem_commSpace_of_mem_Lbar_conj H C ht ht1 hVQ (w := k) (σ := y * t * y⁻¹)
      (by rw [← hfy]; exact hfA.1) ⟨y, hyM, rfl⟩
    simpa [mul_assoc] using h1
  obtain ⟨x₀, rfl⟩ := MonoidHom.mem_range.mp hxM
  have hw₂ : ((S.ρ x₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ∈
      (Vt S g t).map (y : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap := by
    rw [ρ_cl_conj_z S x₀ haQ, ← hcomm_y]
    have hfL : y * t * y⁻¹ ∈ S.Lbar ((x₀ : G) * g) := by
      rw [← hfy]
      exact conj_mem_Lbar_mul S x₀ ((Fbar_le_Lbar : Fbar S g t ≤ S.Lbar g) hφF)
    have h1 := cl_mem_commSpace_of_mem_Lbar_conj H C ht ht1 hVQ (w := x₀) hfL ⟨y, hyM, rfl⟩
    simpa [mul_assoc] using h1
  have hN0 := mul_eq_one_or_conj_of_caseB' hCE H hNo C ht ht1 hVQ hSp hh hb h4 hL hr2 hyM
    (Rbar_le_Mbar hk) hxM hw₁ hw₂ (self_mem_Fbar ht) (self_mem_Fbar ht)
  have hkt := commute_of_mem_Rbar haQ hk
  have e1 : S.ρ k * t * (S.ρ k)⁻¹ = t := by rw [hkt, mul_inv_cancel_right]
  rw [e1] at hN0
  rcases hN0 with h1 | ⟨z, hzM, hz⟩
  ·
    have hτ : S.ρ x₀ * t * (S.ρ x₀)⁻¹ = t := by
      rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right htt]
    refine hβ 1 (by rw [map_one]; exact one_mem _) ⟨?_, ?_⟩
    · rw [hτ]; simpa using ht
    · rw [hτ]; exact self_mem_Nbar H ht
  · refine conj_ne_mul_t_of_typeII H C ht ht1 hVQ hSp.transitive hL hxM hτt hβ z ?_
    rw [← hz]
    exact hτt.symm



end CaseB

end CFSG.LargeExtraspecial.S9
