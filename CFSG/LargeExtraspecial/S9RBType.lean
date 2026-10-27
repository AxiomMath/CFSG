module

public import CFSG.LargeExtraspecial.S6TwoD
public import CFSG.LargeExtraspecial.S9One

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9.RB

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

structure IsConjCent (S : Setting G) (t σ : S.O) : Prop where
  conj : ∃ y ∈ S.Mbar, y * t * y⁻¹ = σ
  comm : σ * t = t * σ
  ne : σ ≠ t

theorem commSpace_le_Wt_of_fix {t x : S.O}
    (hfix : ∀ v ∈ Vt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Wt S g t := by
  intro v hv
  obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
  rw [mem_Wt]
  intro u hu
  have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup x.2 u w
  rw [hfix u hu] at h
  rw [polar_sub_right, h, sub_self]

namespace IsConjCent

variable {t σ : S.O} (hσ : IsConjCent S t σ)
include hσ

theorem mem_Mbar (ht : t ∈ S.Lbar g) : σ ∈ S.Mbar := by
  obtain ⟨y, hy, rfl⟩ := hσ.conj
  exact S.Mbar.mul_mem (S.Mbar.mul_mem hy (S.Lbar_le_Mbar g ht)) (inv_mem hy)

theorem mul_self (H : Hyp4 S g) (ht : t ∈ S.Lbar g) : σ * σ = 1 := by
  obtain ⟨y, -, rfl⟩ := hσ.conj
  have htt := mul_self_of_mem_Lbar S H.conj_mem ht
  calc y * t * y⁻¹ * (y * t * y⁻¹) = y * (t * t) * y⁻¹ := by group
    _ = 1 := by rw [htt, mul_one, mul_inv_cancel]

theorem not_mem_Lbar (H : Hyp4 S g)
    (hR : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t)
    {k : S.M} (hk : S.ρ k ∈ Rbar S g t) : σ ∉ S.Lbar ((k : G) * g) := by
  intro hmem
  obtain ⟨y, hy, rfl⟩ := hσ.conj
  have hkt := commute_of_mem_Rbar H.conj_mem hk
  have h1 := (mem_Lbar_mul_iff S k g).mp hmem
  have e : (S.ρ k)⁻¹ * (y * t * y⁻¹) * S.ρ k =
      ((S.ρ k)⁻¹ * y) * t * ((S.ρ k)⁻¹ * y)⁻¹ := by group
  rw [e] at h1
  have h2 := hR _ (S.Mbar.mul_mem (inv_mem (Rbar_le_Mbar hk)) hy) h1
  apply hσ.ne
  calc y * t * y⁻¹ = S.ρ k * (((S.ρ k)⁻¹ * y) * t * ((S.ρ k)⁻¹ * y)⁻¹) * (S.ρ k)⁻¹ := by
        group
    _ = S.ρ k * t * (S.ρ k)⁻¹ := by rw [h2]
    _ = t := by rw [hkt, mul_inv_cancel_right]

theorem inf_eq_bot (H : Hyp4 S g) (C : Cons311 S g) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g)
    (htr : ∀ v : Vt S g t, v ≠ 0 → ∃ x ∈ RmodN S g t, x (aV ht) = v)
    (hR : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t) :
    Vt S g t ⊓ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
  have hL : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t :=
    fun x hx hxL => by rw [hR x hx hxL]; exact self_mem_Nbar H ht
  have hne := fun (k : S.M) (hk : S.ρ k ∈ Rbar S g t) => hσ.not_mem_Lbar H hR hk
  obtain ⟨y, hy, rfl⟩ := hσ.conj
  exact inf_commSpace_eq_bot H C ht ht1 hVQ htr hL hy fun k hk hmem => hne k hk hmem.1

theorem fix_Vt (H : Hyp4 S g) (C : Cons311 S g) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g)
    (htr : ∀ v : Vt S g t, v ≠ 0 → ∃ x ∈ RmodN S g t, x (aV ht) = v)
    (hR : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t) :
    ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
  fix_Vt_of_inf_eq_bot H (hσ.mem_Mbar ht) hσ.comm (hσ.inf_eq_bot H C ht ht1 hVQ htr hR)

theorem finrank_commSpace (H : Hyp4 S g) (C : Cons311 S g) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) :
    finrank (ZMod 2) (commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)) = finrank (ZMod 2) (Vt S g t) := by
  obtain ⟨y, -, rfl⟩ := hσ.conj
  rw [S8.commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1]
  exact LinearEquiv.finrank_map_eq _ _

theorem apply_mem_Wt (H : Hyp4 S g) (C : Cons311 S g) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) {w : S.Qt} (hw : w ∈ Wt S g t) :
    (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Wt S g t := by
  have hW := (commSpace_t_eq H C ht ht1 hVQ).2
  rw [← hW, mem_fixSpace] at hw ⊢
  rw [← coe_mul_apply, ← hσ.comm, coe_mul_apply, hw]

end IsConjCent

section A6

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) (hA6 : A6Case H C ht ht1 hVQ)
include H C ht ht1 hVQ hA6

theorem N0bar_apply_sub_mem_Vt_a6 {x : S.O} (hx : x ∈ N0bar S g t) {w : S.Qt}
    (hw : w ∈ Wt S g t) : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have hP := clSub_inf_clSub_le_Vt_a6 H C ht ht1 hVQ hA6 hh hb
  exact apply_sub_mem_Vt_of_mem_N0bar H
    (fun k hk w hw => apply_sub_mem_Vt_a H C ht ht1 hVQ hh hb hP hk hw) hx hw

theorem apply_sub_mem_Vt_of_fix {x : S.O} (hxM : x ∈ S.Mbar) (hxt : x * t = t * x)
    (hfix : ∀ v ∈ Vt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) {r : S.O}
    (hr : r ∈ Rbar S g t) {w : S.Qt} (hw : w ∈ Wt S g t) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
      (r : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w) ∈ Vt S g t := by
  have haQ := H.conj_mem
  have hD := dtEqConj_of_transitive H ht hA6.transitive
  have hxW : ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Wt S g t := by
    intro w hw
    have hW := (commSpace_t_eq H C ht ht1 hVQ).2
    rw [← hW, mem_fixSpace] at hw ⊢
    rw [← coe_mul_apply, ← hxt, coe_mul_apply, hw]
  let E : Subgroup S.O :=
    { carrier := {r | r ∈ Rbar S g t ∧ ∀ w ∈ Wt S g t,
        (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
          (r : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w) ∈ Vt S g t}
      mul_mem' := by
        rintro r s ⟨hr, hr'⟩ ⟨hs, hs'⟩
        refine ⟨mul_mem hr hs, fun w hw => ?_⟩
        have hsw := apply_mem_Wt H hs hw
        rw [coe_mul_apply, coe_mul_apply]
        have e : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt)
            ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) - (r : S.Qt ≃ₗ[ZMod 2] S.Qt)
              ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) =
            ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt)
              ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) - (r : S.Qt ≃ₗ[ZMod 2] S.Qt)
                ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) w))) +
            (r : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt)
              ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) w) - (s : S.Qt ≃ₗ[ZMod 2] S.Qt)
                ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) := by
          rw [map_sub]; abel
        rw [e]
        exact add_mem (hr' _ hsw) (apply_mem_Vt_of_mem_Rbar haQ hr (hs' w hw))
      one_mem' := ⟨one_mem _, fun w _ => by
        rw [show ((1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w from rfl,
          show ((1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
            (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w from rfl, sub_self]
        exact zero_mem _⟩
      inv_mem' := by
        rintro r ⟨hr, hr'⟩
        refine ⟨inv_mem hr, fun w hw => ?_⟩
        have hw' := apply_mem_Wt H (inv_mem hr) hw
        have h1 := apply_mem_Vt_of_mem_Rbar haQ (inv_mem hr) (hr' _ hw')
        rw [apply_inv_apply_O, map_sub, inv_apply_apply_O] at h1
        have := neg_mem h1
        rwa [neg_sub] at this }
  suffices hRE : Rbar S g t ≤ E from (hRE hr).2 w hw
  refine sSup_le fun X hX => ?_
  obtain ⟨h, rfl, htX⟩ := hX
  intro r hrX
  have hrR : r ∈ Rbar S g t := Lbar_mul_le_Rbar htX hrX
  refine ⟨hrR, fun w hw => ?_⟩
  have hxN := mem_normalizer_of_fix haQ H.conj_ne hxM (hfix _ (cl_mem_Vt htX))
  have hxr : x * r * x⁻¹ ∈ S.Lbar ((h : G) * g) := (mem_normalizer_iff.mp hxN r).mp hrX
  set m := r⁻¹ * (x * r * x⁻¹) with hm
  have hmL : m ∈ S.Lbar ((h : G) * g) := mul_mem (inv_mem hrX) hxr
  have hxinv : ∀ v ∈ Vt S g t, ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := fun v hv => by
    conv_lhs => rw [← hfix v hv]
    exact inv_apply_apply_O x v
  have hmN : m ∈ Nbar S g t := by
    refine mem_Nbar.mpr ⟨mul_mem (inv_mem hrR) (Lbar_mul_le_Rbar htX hxr), fun v hv => ?_⟩
    rw [hm, coe_mul_apply, coe_mul_apply, coe_mul_apply, hxinv v hv,
      hfix _ (apply_mem_Vt_of_mem_Rbar haQ hrR hv), inv_apply_apply_O]
  obtain ⟨k, hk, hkL⟩ := hD h htX
  have hm0 : m ∈ N0bar S g t := Lbar_mul_inf_Nbar_le_N0bar hk ⟨hkL ▸ hmL, hmN⟩
  have e : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
      (r : S.Qt ≃ₗ[ZMod 2] S.Qt) ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) := by
    rw [hm, coe_mul_apply, coe_mul_apply, coe_mul_apply, inv_apply_apply_O, apply_inv_apply_O]
  rw [e, ← map_sub]
  exact apply_mem_Vt_of_mem_Rbar haQ hrR
    (N0bar_apply_sub_mem_Vt_a6 H C ht ht1 hVQ hA6 hm0 (hxW w hw))

end A6

end CFSG.LargeExtraspecial.S9.RB
