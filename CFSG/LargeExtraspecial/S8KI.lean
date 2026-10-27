module

public import CFSG.LargeExtraspecial.S8KD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem inv_conj_mem_Nbar (haQ : g * S.z * g⁻¹ ∈ S.QG) {r n : S.O} (hr : r ∈ Rbar S g t)
    (hn : n ∈ Nbar S g t) : r⁻¹ * n * r ∈ Nbar S g t := by
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar (inv_mem hr))
  have h1 := conj_mem_Nbar haQ (k := k) (by rw [hk]; exact commute_of_mem_Rbar haQ (inv_mem hr))
    hn
  rw [hk, inv_inv] at h1
  exact h1

theorem mem_Vt_of_fix_Nbar (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) {w : S.Qt} (hw : w ∈ Wt S g t)
    (hfix : ∀ n ∈ Nbar S g t, (n : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) : w ∈ Vt S g t := by
  have haQ := H.conj_mem
  set A := Wt S g t ⊓ fixSub S (Nbar S g t) with hA
  have hAinv : ∀ r ∈ Rbar S g t, ∀ u ∈ A, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ A := by
    intro r hr u hu
    refine ⟨apply_mem_Wt_of_commute H C ht ht1 hVQ (commute_of_mem_Rbar haQ hr) hu.1, ?_⟩
    refine (mem_fixSub S).mpr fun n hn => ?_
    have h1 := (mem_fixSub S).mp hu.2 _ (inv_conj_mem_Nbar haQ hr hn)
    rw [coe_mul_apply, coe_mul_apply] at h1
    calc (n : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) u) =
        (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((n : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) u))) :=
          (apply_inv_apply_O r _).symm
      _ = (r : S.Qt ≃ₗ[ZMod 2] S.Qt) u := by rw [h1]
  have hLa : ∀ l ∈ S.Lbar g, ∀ u ∈ A, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ Vt S g t := by
    intro l hl u hu
    have hP := apply_sub_mem_clSub_of_mem_Wt C (cl_a_mem_Vt ht) haQ hu.1 hl
    have hlu := hAinv l (Lbar_le_Rbar ht hl) u hu
    have hfA : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ fixSub S (S.Lbar g ⊓ Nbar S g t) :=
      (mem_fixSub S).mpr fun n hn => by
        rw [map_sub, (mem_fixSub S).mp hlu.2 n hn.2, (mem_fixSub S).mp hu.2 n hn.2]
    have hmem : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈
        S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S (S.Lbar g ⊓ Nbar S g t) := ⟨hP, hfA⟩
    rw [clSub_inf_fixSub_Abar H C ht ht1 hVQ D.hA] at hmem
    exact hmem.2
  have hLb : ∀ l ∈ S.Lbar ((D.h : G) * g), ∀ u ∈ A,
      (l : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ Vt S g t := by
    intro l hl u hu
    rw [Lbar_mul S D.h g] at hl
    obtain ⟨l₀, hl₀, rfl⟩ := hl
    have hu' := hAinv _ (inv_mem D.hh) u hu
    have h1 := hLa l₀ hl₀ _ hu'
    have h2 := apply_mem_Vt_of_mem_Rbar haQ D.hh h1
    have e : ((MulAut.conj (S.ρ D.h)).toMonoidHom l₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u =
        ((S.ρ D.h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l₀ : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((((S.ρ D.h)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u) -
            (((S.ρ D.h)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u) := by
      rw [map_sub, apply_inv_apply_O]
      rfl
    rw [e]
    exact h2
  obtain ⟨ρ, hρ, hD⟩ := timmesfeld_6_1_two hCE H hNo C ht ht1 hVQ hΩ D.hh D.hb D.hX D.hE
  have hwA : w ∈ A := ⟨hw, (mem_fixSub S).mpr hfix⟩
  have hfa : secMk (Vt S g t) hw ∈ ⊤ ⊓ S2.fixOf ρ
      (S2.radFix D.Q ⊥ (aV ht) : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) := by
    refine ⟨Submodule.mem_top, (S2.mem_fixOf _).mpr fun e he => ?_⟩
    rw [SetLike.mem_coe, S2.radFix_bot, ← D.hE] at he
    obtain ⟨x, hx, hex⟩ := he
    have hxR : x ∈ Rbar S g t := Lbar_le_Rbar ht hx
    have hres : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV haQ t ⟨x, hxR⟩ :=
      LinearEquiv.ext fun v => Subtype.ext ((hex v).trans (coe_resV_apply haQ ⟨x, hxR⟩ v).symm)
    apply Subtype.ext
    rw [hρ e ⟨x, hxR⟩ hres w hw, coe_secMk]
    exact (Submodule.Quotient.eq _).mpr (hLa x hx w hwA)
  have hfb : secMk (Vt S g t) hw ∈ ⊤ ⊓ S2.fixOf ρ
      (S2.radFix D.Q ⊥ (bV (mem_Lbar_of_pair H ht D.hh)) :
        Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) := by
    refine ⟨Submodule.mem_top, (S2.mem_fixOf _).mpr fun e he => ?_⟩
    rw [SetLike.mem_coe, S2.radFix_bot,
      ← LhmodN_eq_pointRadical H ht D.hh (mem_Lbar_of_pair H ht D.hh) D.hX D.hE] at he
    obtain ⟨x, hx, hex⟩ := he
    have hxR : x ∈ Rbar S g t := Lbar_mul_le_Rbar (mem_Lbar_of_pair H ht D.hh) hx
    have hres : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV haQ t ⟨x, hxR⟩ :=
      LinearEquiv.ext fun v => Subtype.ext ((hex v).trans (coe_resV_apply haQ ⟨x, hxR⟩ v).symm)
    apply Subtype.ext
    rw [hρ e ⟨x, hxR⟩ hres w hw, coe_secMk]
    exact (Submodule.Quotient.eq _).mpr (hLb x hx w hwA)
  have h0 : secMk (Vt S g t) hw = 0 := by
    have h2 := hD.2
    rw [eq_bot_iff] at h2
    exact (Submodule.mem_bot _).mp (h2 ⟨hfa, hfb⟩)
  have h3 := congrArg Subtype.val h0
  rw [coe_secMk, ZeroMemClass.coe_zero, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at h3
  exact h3

theorem fixSub_N1bar_eq (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) {σ : S.O}
    (hσt : σ * t = t * σ) (hσσ : σ * σ = 1)
    (hσV : ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hVσ : Vt S g t ⊓ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥) :
    fixSub S (N1bar S g t σ) = Wt S g t ⊓ fixSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  apply le_antisymm
  · intro w hw
    have hwt : w ∈ Wt S g t := by
      have := (mem_fixSub S).mp hw t t_mem_N1bar
      rw [← (commSpace_t_eq H C ht ht1 hVQ).2]
      exact mem_fixSpace.mpr this
    refine ⟨hwt, mem_fixSpace.mpr ?_⟩
    set u := (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w with hu
    have hσw : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Wt S g t :=
      apply_mem_Wt_of_commute H C ht ht1 hVQ hσt hwt
    have huW : u ∈ Wt S g t := sub_mem hσw hwt
    have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσσ
    have hfixu : ∀ n ∈ Nbar S g t, (n : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := by
      intro n hn
      have h1 := (mem_fixSub S).mp hw _ (comm_mem_N1bar (t := t) (τ := σ) (inv_mem hn))
      rw [inv_inv, hσi, coe_mul_apply, coe_mul_apply, coe_mul_apply] at h1
      have h2 : (n : S.Qt ≃ₗ[ZMod 2] S.Qt) ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
          (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((n : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := by
        have h3 := congrArg (fun v => (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((n : S.Qt ≃ₗ[ZMod 2] S.Qt) v))
          h1
        simp only [apply_inv_apply_O] at h3
        rw [← coe_mul_apply σ σ, hσσ] at h3
        exact h3
      have ha := D.hN n hn w hwt
      have hσa := hσV _ ha
      have e : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((n : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
          (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) w + ((n : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := by
        rw [← hσa, ← map_add, add_sub_cancel]
      rw [hu, map_sub, h2, e]
      abel
    have huV := mem_Vt_of_fix_Nbar hCE hNo hΩ D huW hfixu
    have huC : u ∈ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) := mem_commSpace.mpr ⟨w, rfl⟩
    have hmem : u ∈ Vt S g t ⊓ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) := ⟨huV, huC⟩
    rw [hVσ, Submodule.mem_bot] at hmem
    exact sub_eq_zero.mp hmem
  · intro w hw
    exact (mem_fixSub S).mpr fun ν hν =>
      fix_of_mem_N1bar D hσV hw.1 (mem_fixSpace.mp hw.2) hν

theorem perp_sup_commSpace (σ : S.O) :
    S2.perp S.q (Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      Wt S g t ⊓ fixSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  rw [perp_sup, fixSpace_eq_orthogonal_commSpace_of_mem S.q_nondegenerate σ.2]
  rfl

theorem sup_commSpace_eq_of_inf_fixSpace_eq {σ σ' : S.O}
    (h : Wt S g t ⊓ fixSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      Wt S g t ⊓ fixSpace (σ' : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      Vt S g t ⊔ commSpace (σ' : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  rw [← perp_perp S.q_nondegenerate (Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)),
    ← perp_perp S.q_nondegenerate (Vt S g t ⊔ commSpace (σ' : S.Qt ≃ₗ[ZMod 2] S.Qt)),
    perp_sup_commSpace, perp_sup_commSpace, h]

end CFSG.LargeExtraspecial.S8
