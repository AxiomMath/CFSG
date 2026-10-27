module

public import CFSG.LargeExtraspecial.S8A5MA
public import CFSG.LargeExtraspecial.S8A5LE

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.LargeExtraspecial.S2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem exists_not_comm_le_of_good (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2)
    {x σ : S.O} (hxM : x ∈ S.Mbar) (hxσ : σ = x * t * x⁻¹)
    (hσt : σ * t = t * σ) (hσV : ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hgood : Vt S g t ⊓ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥)
    (hU : (Wt S g t).map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t =
      Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    ∃ w ∈ S.Lbar g ⊓ Nbar S g t, ∃ y ∈ Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (w : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  have haQ := H.conj_mem
  have hσM : σ ∈ S.Mbar := by
    rw [hxσ]; exact S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have hYinv : ∀ r ∈ Rbar S g t, ∀ u ∈ Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (r : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [← hU]; exact comm_sup_Vt_invariant D hσM hσt hσV
  have hYW : Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Wt S g t :=
    sup_le (Vt_le_Wt H ht1) (commSpace_le_Wt_of_fix hσV)
  by_contra hcon
  push Not at hcon
  obtain ⟨l, hl, -, -, hlN, -, -⟩ := exists_pair_not_mem_Nbar H D hm2
  have hNR : ∀ {r n : S.O}, r ∈ Rbar S g t → n ∈ Nbar S g t → r * n * r⁻¹ ∈ Nbar S g t := by
    intro r n hr hn
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hr)
    exact conj_mem_Nbar haQ (commute_of_mem_Rbar haQ hr) hn
  have hβ : ∀ β ∈ S.Lbar ((D.h : G) * g) ⊓ Nbar S g t,
      ∀ z ∈ Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt), (β : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z ∈
        (ZMod 2) ∙ S.cl ((D.h : G) * g * S.z * ((D.h : G) * g)⁻¹) := by
    rintro β ⟨hβL, hβN⟩ z hz
    rw [Lbar_mul S D.h g] at hβL
    obtain ⟨β₀, hβ₀, rfl⟩ := hβL
    have hhinv : (S.ρ D.h)⁻¹ ∈ Rbar S g t := inv_mem D.hh
    have hβ₀N : β₀ ∈ Nbar S g t := by
      have h1 := hNR hhinv hβN
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
      rwa [show (S.ρ D.h)⁻¹ * (S.ρ D.h * β₀ * (S.ρ D.h)⁻¹) * S.ρ D.h = β₀ by group] at h1
    have h1 := hcon β₀ ⟨hβ₀, hβ₀N⟩ _ (hYinv _ hhinv z hz)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
    refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [coe_mul_apply, coe_mul_apply, ← ρ_cl_conj_z S D.h haQ, ← map_smul, hc, map_sub,
      apply_inv_apply_O]
  have h1R : S.ρ 1 ∈ Rbar S g t := by rw [map_one]; exact one_mem _
  have hgen' : Rbar S g t ≤ S.Lbar (((1 : S.M) : G) * g) ⊔ S.Lbar ((D.h : G) * g) ⊔
      Nbar S g t :=
    D.hgen 1 D.h h1R D.hh (by rw [OneMemClass.coe_one, one_mul]; exact D.hb)
  have hr : l * S.ρ D.h ∈ Rbar S g t := mul_mem (Lbar_le_Rbar ht hl) D.hh
  have hfixY : ∀ w ∈ S.Lbar g ⊓ Nbar S g t,
      ∀ y ∈ Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt),
        (w : S.Qt ≃ₗ[ZMod 2] S.Qt) y = y := by
    intro w hw y hy
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hcon w hw y hy)
    rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
    · rw [zero_smul] at hc
      exact (sub_eq_zero.mp hc.symm)
    · exfalso
      rw [one_smul] at hc
      obtain ⟨α, hα, β, hβ', hαβ⟩ := exists_mul_of_pair H ht h1R D.hh hgen' D.hN0
        (hNR hr hw.2)
      rw [OneMemClass.coe_one, one_mul] at hα
      have hz := hYinv _ hr y hy
      obtain ⟨ν, hν⟩ := Submodule.mem_span_singleton.mp (hβ β hβ' _ hz)
      obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp (hcon α hα _ hz)
      have hβV := D.hN β hβ'.2 _ (hYW hz)
      have e1 : (l : S.Qt ≃ₗ[ZMod 2] S.Qt)
          (S.cl ((D.h : G) * g * S.z * ((D.h : G) * g)⁻¹)) =
          (((l * S.ρ D.h) * w * (l * S.ρ D.h)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
            (((l * S.ρ D.h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y) -
            ((l * S.ρ D.h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y := by
        rw [coe_mul_apply, coe_mul_apply, inv_apply_apply_O, ← map_sub, ← hc, coe_mul_apply,
          ρ_cl_conj_z S D.h haQ]
      apply apply_cl_b_ne H D hl hlN μ ν
      have hαfix := (mem_Nbar.mp hα.2).2 _ hβV
      rw [e1, hαβ, coe_mul_apply, hμ, hν, ← hαfix, map_sub]
      abel
  have h5 := five_le_finrank_clSub_inf_of_good hCE hNo hΩ D hm2 hxM hxσ hσt hσV hgood hU
  have hle : S.clSub (S.QG ⊓ S.Qa g) ⊓ (Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≤
      S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S (S.Lbar g ⊓ Nbar S g t) :=
    fun u hu => ⟨hu.1, (mem_fixSub S).mpr fun α hα => hfixY α hα u hu.2⟩
  have h6 := Submodule.finrank_mono hle
  have hcard := card_mul_two_pow_finrank_fix H C
    (inf_le_left : S.Lbar g ⊓ Nbar S g t ≤ S.Lbar g)
  have hA := D.hA
  rw [D.hdim, hm2, show (2 : ℕ) ^ (2 * 2 - 1) = 8 by norm_num] at hA
  have h7 : Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) * 2 ^ 5 ≤
      Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) * 2 ^ finrank (ZMod 2)
        ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S (S.Lbar g ⊓ Nbar S g t)) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (h5.trans h6))
  have hpos : 0 < 2 ^ S.width := pow_pos (by norm_num) _
  omega

theorem inf_commSpace_conj_eq (D : Std H C ht ht1 hVQ) {x w : S.O}
    (hσV : ∀ v ∈ Vt S g t, ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hgood : Vt S g t ⊓ commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥)
    (hwN : w ∈ Nbar S g t) :
    Vt S g t ⊓ commSpace (((x⁻¹ * w * x) * t * (x⁻¹ * w * x)⁻¹ : S.O) :
        S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓
        fixSpace (w : S.Qt ≃ₗ[ZMod 2] S.Qt)).map
          (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) := by
  have hσc : commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (Vt S g t).map ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) := by
    rw [commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1]
  have hσ'c : commSpace (((x⁻¹ * w * x) * t * (x⁻¹ * w * x)⁻¹ : S.O) :
      S.Qt ≃ₗ[ZMod 2] S.Qt) = (Vt S g t).map
        (((x⁻¹ * w * x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) := by
    rw [commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1]
  have hW : commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Wt S g t :=
    commSpace_le_Wt_of_fix hσV
  apply le_antisymm
  · intro v hv
    obtain ⟨hvV, hvσ'⟩ := Submodule.mem_inf.mp hv
    rw [hσ'c] at hvσ'
    obtain ⟨v₁, hv₁, hv₁v⟩ := hvσ'
    have hxv₁ : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v₁ ∈
        commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rw [hσc]; exact ⟨v₁, hv₁, rfl⟩
    have hxv : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈
        commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rw [hσc]; exact ⟨v, hvV, rfl⟩
    have e1 : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
        (w : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v₁) := by
      rw [← hv₁v]
      change (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (((x⁻¹ * w * x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v₁) = _
      rw [coe_mul_apply, coe_mul_apply, apply_inv_apply_O]
    have e2 : (w : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v₁) =
        (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v₁ := by
      have h1 := D.hN w hwN _ (hW hxv₁)
      have h2 : (w : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v₁) -
          (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v₁ ∈
            commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
        rw [← e1]; exact sub_mem hxv hxv₁
      have h3 : _ ∈ Vt S g t ⊓ commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
        Submodule.mem_inf.mpr ⟨h1, h2⟩
      rw [hgood, Submodule.mem_bot, sub_eq_zero] at h3
      exact h3
    refine ⟨(x : S.Qt ≃ₗ[ZMod 2] S.Qt) v, Submodule.mem_inf.mpr ⟨hxv, mem_fixSpace.mpr ?_⟩,
      inv_apply_apply_O x v⟩
    rw [e1, e2, e2]
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨huσ, huw⟩ := Submodule.mem_inf.mp hu
    rw [mem_fixSpace] at huw
    have huσ' := huσ
    rw [hσc] at huσ'
    obtain ⟨v₀, hv₀, rfl⟩ := huσ'
    simp only [LinearEquiv.coe_coe] at huw ⊢
    rw [inv_apply_apply_O]
    refine Submodule.mem_inf.mpr ⟨hv₀, ?_⟩
    rw [hσ'c]
    refine ⟨v₀, hv₀, ?_⟩
    simp only [LinearEquiv.coe_coe]
    rw [coe_mul_apply, coe_mul_apply, huw, inv_apply_apply_O]

theorem false_of_finrank_inf_fixSpace_eq_one (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2)
    (hmin : D.IsMinus) (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) {x : S.O} (hxM : x ∈ S.Mbar)
    (hxc : x * t * x⁻¹ * t = t * (x * t * x⁻¹))
    (hgood : Vt S g t ⊓ commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥)
    {w : S.O} (hwA : w ∈ S.Lbar g ⊓ Nbar S g t)
    (hdim : finrank (ZMod 2) ↥(commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓
      fixSpace (w : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 1) : False := by
  have haQ := H.conj_mem
  have hstep1 := step1_fix_Vt_A5 hCE hNo hΩ D hm2 hmin hA7
  have hσM : x * t * x⁻¹ ∈ S.Mbar :=
    S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have hσV := hstep1 _ ⟨hσM, hxc, x, hxM, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = x * t * x⁻¹ := ⟨_, rfl⟩
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have hσσ : σ * σ = 1 := by
    rw [hσ, show x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ by group, htt]
    group
  have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσσ
  have hσnorm := mem_normalizer_Abar_of_fix H ht hσM hxc hσV
  rw [← hσ] at hσnorm
  have h1 : σ * w⁻¹ * σ⁻¹ ∈ S.Lbar g ⊓ Nbar S g t :=
    (mem_normalizer_iff.mp hσnorm w⁻¹).mp (inv_mem hwA)
  have heA : w * σ * w⁻¹ * σ⁻¹ ∈ S.Lbar g ⊓ Nbar S g t := by
    have h2 := mul_mem hwA h1
    rwa [show w * (σ * w⁻¹ * σ⁻¹) = w * σ * w⁻¹ * σ⁻¹ by group] at h2
  have hei := inv_eq_of_mul_eq_one_right (mul_self_of_mem_Lbar S haQ heA.1)
  have hτσ : w * σ * w⁻¹ * σ = σ * (w * σ * w⁻¹) := by
    calc w * σ * w⁻¹ * σ = w * σ * w⁻¹ * σ⁻¹ := by rw [hσi]
      _ = (w * σ * w⁻¹ * σ⁻¹)⁻¹ := hei.symm
      _ = σ * w * σ⁻¹ * w⁻¹ := by group
      _ = σ * (w * σ * w⁻¹) := by rw [hσi]; group
  have hw'M : x⁻¹ * w * x ∈ S.Mbar :=
    S.Mbar.mul_mem (S.Mbar.mul_mem (inv_mem hxM) (S.Lbar_le_Mbar g hwA.1)) hxM
  have ht' : t = x⁻¹ * σ * x := by rw [hσ]; group
  have hσ'eq : (x⁻¹ * w * x) * t * (x⁻¹ * w * x)⁻¹ = x⁻¹ * (w * σ * w⁻¹) * x := by
    rw [hσ]; group
  have hσ't : (x⁻¹ * w * x) * t * (x⁻¹ * w * x)⁻¹ * t = t * ((x⁻¹ * w * x) * t *
      (x⁻¹ * w * x)⁻¹) := by
    rw [hσ'eq]
    calc x⁻¹ * (w * σ * w⁻¹) * x * t = x⁻¹ * (w * σ * w⁻¹ * σ) * x := by
          rw [ht']; group
      _ = x⁻¹ * (σ * (w * σ * w⁻¹)) * x := by rw [hτσ]
      _ = t * (x⁻¹ * (w * σ * w⁻¹) * x) := by rw [ht']; group
  have hσ'M : (x⁻¹ * w * x) * t * (x⁻¹ * w * x)⁻¹ ∈ S.Mbar :=
    S.Mbar.mul_mem (S.Mbar.mul_mem hw'M (S.Lbar_le_Mbar g ht)) (inv_mem hw'M)
  have hσ'V := hstep1 _ ⟨hσ'M, hσ't, _, hw'M, rfl⟩
  have hk : finrank (ZMod 2) ↥(Vt S g t ⊓ commSpace (((x⁻¹ * w * x) * t *
      (x⁻¹ * w * x)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 1 := by
    rw [inf_commSpace_conj_eq D hσV hgood hwA.2, LinearEquiv.finrank_map_eq]
    exact hdim
  have hdimσ' : finrank (ZMod 2) (commSpace (((x⁻¹ * w * x) * t * (x⁻¹ * w * x)⁻¹ : S.O) :
      S.Qt ≃ₗ[ZMod 2] S.Qt)) = finrank (ZMod 2) (Vt S g t) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, finrank_commSpace_conj',
      (commSpace_t_eq H C ht ht1 hVQ).1]
  have hdimV := D.hdim
  rw [hm2] at hdimV
  rcases bad_or_good_A5 hCE hNo hΩ D hm2 hmin hw'M rfl hσ't hσ'V with hbad | ⟨hgood', -⟩
  · have h2 := finrank_map_Wt_add (S := S) (g := g) (t := t)
      ((x⁻¹ * w * x) * t * (x⁻¹ * w * x)⁻¹)
    have hle : (Wt S g t).map (((((x⁻¹ * w * x) * t * (x⁻¹ * w * x)⁻¹ : S.O) :
        S.Qt ≃ₗ[ZMod 2] S.Qt)).toLinearMap - 1) ≤ Vt S g t ⊓ commSpace
          (((x⁻¹ * w * x) * t * (x⁻¹ * w * x)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨hbad y hy, sub_mem_commSpace _ y⟩
    have h3 := Submodule.finrank_mono hle
    omega
  · rw [hgood', finrank_bot] at hk
    omega

theorem false_of_good_A5 (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2)
    (hmin : D.IsMinus) (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) {x : S.O} (hxM : x ∈ S.Mbar)
    (hxc : x * t * x⁻¹ * t = t * (x * t * x⁻¹))
    (hxg : ¬ ∀ w ∈ Wt S g t, ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) :
    False := by
  have hσM : x * t * x⁻¹ ∈ S.Mbar :=
    S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have hσV := step1_fix_Vt_A5 hCE hNo hΩ D hm2 hmin hA7 _ ⟨hσM, hxc, x, hxM, rfl⟩
  obtain ⟨hgood, hU⟩ := (bad_or_good_A5 hCE hNo hΩ D hm2 hmin hxM rfl hxc hσV).resolve_left hxg
  obtain ⟨w, hwA, y, hy, hwy⟩ :=
    exists_not_comm_le_of_good hCE hNo hΩ D hm2 hxM rfl hxc hσV hgood hU
  rcases rank_dichotomy_A5 hCE hNo hΩ D hm2 hmin hxM rfl hxc hσV hgood hU hwA with h | h
  · exact hwy (h y hy)
  · exact false_of_finrank_inf_fixSpace_eq_one hCE hNo hΩ D hm2 hmin hA7 hxM hxc hgood hwA h

theorem timmesfeld83A5InfLinBadE : Timmesfeld83A5InfLinBadE.{u} := by
  intro G _ _ S g hCE _ H hNo C t ht ht1 hVQ hΩ D hm2 hmin hA7 x hxM hxc _ hxg
  exact (false_of_good_A5 hCE hNo hΩ D hm2 hmin hA7 hxM hxc hxg).elim

end CFSG.LargeExtraspecial.S8
