module

public import CFSG.GH74.GLS.C3.Layer1.Thm1G35Model
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1G35

open Subgroup

structure WrData (G : Type) [Group G] where
  ι : D8 →* G
  b : G
  hb2 : b * b = 1
  hι : Function.Injective ι
  hcomm : ∀ u v : D8, ι u * (b * ι v * b⁻¹) = (b * ι v * b⁻¹) * ι u
  hint : ∀ u v : D8, ι u = b * ι v * b⁻¹ → u = 1
  hb : ∀ u v : D8, b ≠ ι u * (b * ι v * b⁻¹)

namespace WrData

variable {G : Type} [Group G] (d : WrData G)

@[expose] def ι₂ : D8 →* G := (MulAut.conj d.b).toMonoidHom.comp d.ι

@[expose] def fn : D8 × D8 →* G := d.ι.noncommCoprod d.ι₂ (fun u v => d.hcomm u v)

theorem fn_apply (u v : D8) : d.fn (u, v) = d.ι u * (d.b * d.ι v * d.b⁻¹) := by
  simp [fn, ι₂]

@[expose] def fg : Z2 →* G where
  toFun q := if q = 1 then 1 else d.b
  map_one' := by simp
  map_mul' q q' := by
    by_cases hq : q = 1 <;> by_cases hq' : q' = 1
    · simp [hq, hq']
    · simp [hq, hq']
    · simp [hq, hq']
    · simp only [hq, hq', ite_false]
      rw [z2_mul_ne_one q q' hq hq']
      simpa using d.hb2.symm

theorem fg_one : d.fg 1 = 1 := map_one _

theorem fg_ne {q : Z2} (hq : q ≠ 1) : d.fg q = d.b := by simp [fg, hq]

theorem compat (g : Z2) : d.fn.comp (MulEquiv.toMonoidHom (swapHom g)) =
    (MulEquiv.toMonoidHom (MulAut.conj (d.fg g))).comp d.fn := by
  by_cases hg : g = 1
  · subst hg
    ext ⟨u, v⟩
    simp [swapHom]
  · have hsw : swapHom g = MulEquiv.prodComm := by simp [swapHom, hg]
    have hfg : d.fg g = d.b := d.fg_ne hg
    ext ⟨u, v⟩
    show d.fn ((swapHom g) (u, v)) = d.fg g * d.fn (u, v) * (d.fg g)⁻¹
    rw [hsw, hfg]
    show d.fn (v, u) = _
    rw [fn_apply, fn_apply]
    have hb2' : d.b * d.b = 1 := d.hb2
    have hbb : d.b⁻¹ * d.b⁻¹ = 1 := by rw [← mul_inv_rev, hb2', inv_one]
    have e1 : d.b * (d.ι u * (d.b * d.ι v * d.b⁻¹)) * d.b⁻¹ =
        (d.b * d.ι u * d.b⁻¹) * ((d.b * d.b) * d.ι v * (d.b⁻¹ * d.b⁻¹)) := by group
    rw [e1, hb2', hbb, one_mul, mul_one]
    exact d.hcomm v u

@[expose] noncomputable def Ψ : M35 →* G := SemidirectProduct.lift d.fn d.fg d.compat

theorem Ψ_inl' (u v : D8) : d.Ψ (inl' u v) = d.ι u * (d.b * d.ι v * d.b⁻¹) := by
  simp [Ψ, inl', SemidirectProduct.lift, fn_apply, fg_one]

theorem Ψ_injective : Function.Injective d.Ψ := by
  rw [injective_iff_map_eq_one]
  rintro ⟨⟨u, v⟩, q⟩ h
  by_cases hq : q = 1
  · subst hq
    have h1 : d.Ψ (inl' u v) = 1 := h
    rw [Ψ_inl'] at h1
    have h2 : d.ι u = d.b * d.ι (v⁻¹) * d.b⁻¹ := by
      rw [map_inv]
      have : d.ι u = (d.b * d.ι v * d.b⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      group
    have hu : u = 1 := d.hint u v⁻¹ h2
    subst hu
    rw [map_one, one_mul] at h1
    have hv : d.ι v = 1 := by
      have : d.b * d.ι v * d.b⁻¹ = 1 := h1
      calc d.ι v = d.b⁻¹ * (d.b * d.ι v * d.b⁻¹) * d.b := by group
        _ = 1 := by rw [this]; group
    have hv' : v = 1 := d.hι (by rw [hv, map_one])
    subst hv'
    rfl
  · exfalso
    have h1 : d.fn (u, v) * d.fg q = 1 := h
    rw [d.fg_ne hq, fn_apply] at h1
    have h2 : d.b = (d.ι u * (d.b * d.ι v * d.b⁻¹))⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h3 : (d.ι u * (d.b * d.ι v * d.b⁻¹))⁻¹ = d.ι u⁻¹ * (d.b * d.ι v⁻¹ * d.b⁻¹) := by
      rw [mul_inv_rev, map_inv, map_inv]
      have := d.hcomm u⁻¹ v⁻¹
      rw [map_inv, map_inv] at this
      rw [this]
      congr 1
      group
    exact d.hb u⁻¹ v⁻¹ (h2.trans h3)

theorem Ψ_apply (m : M35) : d.Ψ m = d.fn m.left * d.fg m.right := rfl

end WrData

end CFSG.GH74.GLS.C3.Layer1.Thm1G35

end
