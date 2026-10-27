module

public import CFSG.LargeExtraspecial.S8KV

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

namespace Bad3

variable {D : Std H C ht ht1 hVQ} {τ : S.O} (B : Bad3 D τ)
include B

theorem comm_comm_mem_Vt {l : S.O} (hl : l ∈ S.Lbar g)
    (h0 : ∀ z₁ ∈ S.clSub (S.QG ⊓ S.Qa ((D.h : G) * g)) ⊓ Wt S g t,
      ∀ z₂ ∈ S.clSub (S.QG ⊓ S.Qa ((D.h : G) * g)) ⊓ Wt S g t,
        tauBil S τ ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) z₁ - z₁) z₂ = 0)
    {w : S.Qt} (hw : w ∈ Wt S g t) :
    (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) -
      ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) ∈ Vt S g t := by
  have hdec := sup_eq_Wt H C ht ht1 hVQ D.hh D.hb D.hPab
  have ha : ∀ a ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t,
      (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) a - a) -
        ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) a - a) = 0 := by
    intro a ha
    have hv : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) a - a ∈ Vt S g t :=
      (Submodule.span_singleton_le_iff_mem _ _).mpr (cl_a_mem_Vt ht)
        (Lbar_apply_sub_mem_span' H.conj_mem ha.1 hl)
    rw [B.fix_Vt _ hv, sub_self]
  have hb : ∀ b ∈ S.clSub (S.QG ⊓ S.Qa ((D.h : G) * g)) ⊓ Wt S g t,
      (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) b - b) -
        ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) b - b) ∈ Vt S g t := by
    intro b hb
    have hδ := apply_sub_mem_clSub_of_mem_Wt C (cl_a_mem_Vt ht) H.conj_mem hb.2 hl
    have hX : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) b - b) -
        ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) b - b) ∈ S.clSub (S.QG ⊓ S.Qa g) :=
      sub_mem (B.apply_mem_clSub_a hδ) hδ
    rw [← perp_perp S.q_nondegenerate (Vt S g t)]
    refine S2.mem_perp.mpr fun w' hw' => ?_
    change w' ∈ Wt S g t at hw'
    rw [← hdec] at hw'
    obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.mp hw'
    rw [polar_add_left, polar_eq_zero_of_mem_clSub H.conj_ne ha'.1 hX, zero_add, polar_comm,
      ← tauBil_apply]
    exact h0 b hb b' hb'
  rw [← hdec] at hw
  obtain ⟨a, ha', b, hb', rfl⟩ := Submodule.mem_sup.mp hw
  have e : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) (a + b) - (a + b)) -
      ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) (a + b) - (a + b)) =
      ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) a - a) -
        ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) a - a)) +
      ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) b - b) -
        ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) b - b)) := by
    simp only [map_add, map_sub]
    abel
  rw [e, ha a ha', zero_add]
  exact hb b hb'

theorem apply_sub_mem_Vt_of_forall {l : S.O} (hl : l ∈ S.Lbar g)
    (h0 : ∀ z₁ ∈ S.clSub (S.QG ⊓ S.Qa ((D.h : G) * g)) ⊓ Wt S g t,
      ∀ z₂ ∈ S.clSub (S.QG ⊓ S.Qa ((D.h : G) * g)) ⊓ Wt S g t,
        tauBil S τ ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) z₁ - z₁) z₂ = 0)
    {u : S.Qt} (hu : u ∈ (Wt S g t).map ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔
      Vt S g t) :
    (l : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ Vt S g t := by
  have haQ := H.conj_mem
  have hlR := Lbar_le_Rbar ht hl
  obtain ⟨y, hy, v, hv, rfl⟩ := Submodule.mem_sup.mp hu
  obtain ⟨w, hw, rfl⟩ := hy
  obtain ⟨ν, hνdef⟩ : ∃ ν : S.O, ν = l * τ * l⁻¹ * τ⁻¹ := ⟨_, rfl⟩
  have hν : ν ∈ Nbar S g t := by
    rw [hνdef]
    exact comm_mem_Nbar_of_fix H B.τM B.τt B.fix_Vt hlR
  have h1 : l * τ = ν * τ * l := by rw [hνdef]; group
  have hlw : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Wt S g t := apply_mem_Wt H hlR hw
  have hτlw : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) w) ∈ Wt S g t :=
    apply_mem_Wt_of_commute H C ht ht1 hVQ B.τt hlw
  have hc := D.hN ν hν _ hτlw
  have hk := B.comm_comm_mem_Vt hl h0 hw
  have hlv := sub_mem (apply_mem_Vt_of_mem_Rbar haQ hlR hv) hv
  have e : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) w + v) -
      (((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) w + v) =
      ((ν : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) -
        (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) +
      ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) -
        ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w)) + ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) := by
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, map_add,
      map_sub]
    rw [← coe_mul_apply l τ, h1, coe_mul_apply, coe_mul_apply]
    abel
  rw [e]
  exact add_mem (add_mem hc hk) hlv

theorem not_forall_apply_sub_mem : ¬ ∀ l ∈ S.Lbar g, ∀ u ∈ (Wt S g t).map
    ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t,
      (l : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ Vt S g t := by
  intro hall
  have hPI := pairInt_of_radBound H C ht ht1 hVQ D.hR
  have hUX : (Wt S g t).map ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t ≤
      S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t ⊔ Vt S g t := fun u hu =>
    (forall_apply_sub_mem_Vt_iff_a H B.hNo C ht ht1 hVQ D.hh D.hb hPI (B.U_le_Wt hu)).mp
      (fun l hl => hall l hl u hu)
  have h := B.finrank_U_inf
  rw [inf_eq_left.mpr hUX, B.finrank_U] at h
  exact absurd h (by norm_num)

end Bad3

end CFSG.LargeExtraspecial.S8
