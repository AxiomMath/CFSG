module

public import CFSG.GH74.E2.Cl2Defs

public section

namespace CFSG.GH74.E2

open Subgroup

inductive Wt
  | w0 | wa | wb | wp | wm
  deriving DecidableEq

namespace Cl2Wt

variable {M : Type*} [CommGroup M]

@[expose] def nrm (α : M →* M) : M →* M := MonoidHom.id M * α * α.comp α

theorem nrm_apply (α : M →* M) (x : M) : nrm α x = x * α x * α (α x) := rfl

@[expose] def eP (m : ℕ) (α : M →* M) : M →* M := (powMonoidHom m).comp (nrm α)

theorem eP_apply (m : ℕ) (α : M →* M) (x : M) : eP m α x = nrm α x ^ m := rfl

@[expose] def fP (m : ℕ) (α : M →* M) : M →* M := MonoidHom.id M / eP m α

theorem fP_apply (m : ℕ) (α : M →* M) (x : M) : fP m α x = x / eP m α x := rfl

@[expose] def Cm (φ ψ : M →* M) : Prop := ∀ x, φ (ψ x) = ψ (φ x)

namespace Cm

variable {φ ψ ψ₁ ψ₂ α : M →* M}

theorem refl (φ : M →* M) : Cm φ φ := fun _ => rfl

theorem symm (h : Cm φ ψ) : Cm ψ φ := fun x => (h x).symm

theorem id_right (φ : M →* M) : Cm φ (MonoidHom.id M) := fun _ => rfl

theorem mul_right (h₁ : Cm φ ψ₁) (h₂ : Cm φ ψ₂) : Cm φ (ψ₁ * ψ₂) := fun x => by
  simp only [MonoidHom.mul_apply, map_mul, h₁ x, h₂ x]

theorem div_right (h₁ : Cm φ ψ₁) (h₂ : Cm φ ψ₂) : Cm φ (ψ₁ / ψ₂) := fun x => by
  simp only [MonoidHom.div_apply, map_div, h₁ x, h₂ x]

theorem comp_right (h₁ : Cm φ ψ₁) (h₂ : Cm φ ψ₂) : Cm φ (ψ₁.comp ψ₂) := fun x => by
  simp only [MonoidHom.comp_apply, h₁ (ψ₂ x), h₂ x]

theorem pow_right (φ : M →* M) (m : ℕ) : Cm φ (powMonoidHom m) := fun x => map_pow φ x m

theorem nrm_right (h : Cm φ α) : Cm φ (nrm α) :=
  ((id_right φ).mul_right h).mul_right (h.comp_right h)

theorem eP_right (m : ℕ) (h : Cm φ α) : Cm φ (eP m α) := (pow_right φ m).comp_right h.nrm_right

theorem fP_right (m : ℕ) (h : Cm φ α) : Cm φ (fP m α) := (id_right φ).div_right (h.eP_right m)

end Cm

section Order3

variable {α : M →* M} {m : ℕ}

theorem nrm_fix (h3 : ∀ x, α (α (α x)) = x) (x : M) : α (nrm α x) = nrm α x := by
  simp only [nrm_apply, map_mul, h3]
  ac_rfl

theorem nrm_map (h3 : ∀ x, α (α (α x)) = x) (x : M) : nrm α (α x) = nrm α x :=
  ((Cm.refl α).nrm_right x).symm.trans (nrm_fix h3 x)

theorem nrm_of_fix {x : M} (hx : α x = x) : nrm α x = x ^ 3 := by
  rw [nrm_apply, hx, hx, pow_three']

theorem eq_one_of_cube (hm : ∀ x : M, (x ^ m) ^ 3 = x) {x : M} (h : x ^ 3 = 1) : x = 1 := by
  rw [← hm x, ← pow_mul, mul_comm, pow_mul, h, one_pow]

theorem eq_one_of_fix_nrm (hm : ∀ x : M, (x ^ m) ^ 3 = x) {x : M} (hx : α x = x)
    (hn : nrm α x = 1) : x = 1 :=
  eq_one_of_cube hm (by rw [← nrm_of_fix hx, hn])

theorem eP_fix (h3 : ∀ x, α (α (α x)) = x) (x : M) : α (eP m α x) = eP m α x := by
  rw [eP_apply, map_pow, nrm_fix h3]

theorem eP_of_fix (hm : ∀ x : M, (x ^ m) ^ 3 = x) {x : M} (hx : α x = x) : eP m α x = x := by
  rw [eP_apply, nrm_of_fix hx, ← pow_mul, mul_comm, pow_mul, hm]

theorem eP_of_nrm {x : M} (hn : nrm α x = 1) : eP m α x = 1 := by
  rw [eP_apply, hn, one_pow]

theorem nrm_eP (h3 : ∀ x, α (α (α x)) = x) (hm : ∀ x : M, (x ^ m) ^ 3 = x) (x : M) :
    nrm α (eP m α x) = nrm α x := by
  rw [nrm_of_fix (eP_fix h3 x), eP_apply, hm]

theorem nrm_fP (h3 : ∀ x, α (α (α x)) = x) (hm : ∀ x : M, (x ^ m) ^ 3 = x) (x : M) :
    nrm α (fP m α x) = 1 := by
  rw [fP_apply, map_div, nrm_eP h3 hm, div_self']

theorem eP_mul_fP (x : M) : eP m α x * fP m α x = x := by
  rw [fP_apply, mul_div_cancel]

theorem fP_of_fix (hm : ∀ x : M, (x ^ m) ^ 3 = x) {x : M} (hx : α x = x) : fP m α x = 1 := by
  rw [fP_apply, eP_of_fix hm hx, div_self']

theorem fP_of_nrm {x : M} (hn : nrm α x = 1) : fP m α x = x := by
  rw [fP_apply, eP_of_nrm hn, div_one]

end Order3

structure Hyp (α β : M →* M) (m : ℕ) : Prop where
  hα : ∀ x, α (α (α x)) = x
  hβ : ∀ x, β (β (β x)) = x
  hc : Cm β α
  hm : ∀ x : M, (x ^ m) ^ 3 = x

@[expose] def gam (α β : M →* M) : M →* M := α.comp (β.comp β)

theorem gam_apply (α β : M →* M) (x : M) : gam α β x = α (β (β x)) := rfl

theorem Cm.gam_right {φ α β : M →* M} (h₁ : Cm φ α) (h₂ : Cm φ β) : Cm φ (gam α β) :=
  h₁.comp_right (h₂.comp_right h₂)

namespace Hyp

variable {α β : M →* M} {m : ℕ}

theorem ba (H : Hyp α β m) (x : M) : β (α x) = α (β x) := H.hc x

theorem ab (H : Hyp α β m) (x : M) : α (β x) = β (α x) := (H.hc x).symm

theorem cube_pow (H : Hyp α β m) (x : M) : (x ^ 3) ^ m = x := by
  rw [← pow_mul, mul_comm, pow_mul, H.hm]

theorem inj_α (H : Hyp α β m) {x y : M} (h : α x = α y) : x = y := by
  rw [← H.hα x, ← H.hα y, h]

theorem hγ (H : Hyp α β m) (x : M) : gam α β (gam α β (gam α β x)) = x := by
  simp only [gam_apply, H.ba, H.hα, H.hβ]

theorem hδ (H : Hyp α β m) (x : M) : α.comp β (α.comp β (α.comp β x)) = x := by
  simp only [MonoidHom.comp_apply, H.ba, H.hα, H.hβ]

theorem nrm_four (H : Hyp α β m) (x : M) :
    nrm α x * nrm β x * nrm (gam α β) x * nrm (α.comp β) x = x ^ 3 * nrm α (nrm β x) := by
  simp only [nrm_apply, gam_apply, MonoidHom.comp_apply, map_mul, H.ba, H.hβ, pow_three']
  ac_rfl

theorem cm_αβ (H : Hyp α β m) : Cm α β := H.hc.symm

theorem cm_nα_α : Cm (nrm α) α := ((Cm.refl α).nrm_right).symm

theorem cm_nα_β (H : Hyp α β m) : Cm (nrm α) β := H.hc.nrm_right.symm

theorem cm_nβ_α (H : Hyp α β m) : Cm (nrm β) α := H.cm_αβ.nrm_right.symm

theorem cm_nβ_β : Cm (nrm β) β := ((Cm.refl β).nrm_right).symm

theorem gam_of_eq (H : Hyp α β m) {z : M} (h : α z = β z) : gam α β z = z := by
  rw [gam_apply, H.cm_αβ, H.cm_αβ, h, H.hβ]

theorem eq_of_gam (H : Hyp α β m) {z : M} (h : gam α β z = z) : α z = β z := by
  have := congrArg β h
  rwa [gam_apply, H.ba, H.hβ] at this

theorem fix_of_nrm (H : Hyp α β m) {z : M} (h₁ : nrm α z = 1) (h₂ : nrm β z = 1)
    (h₃ : nrm (gam α β) z = 1) : α (β z) = z := by
  have h4 := H.nrm_four z
  rw [h₁, h₂, h₃, map_one, one_mul, one_mul, one_mul, mul_one] at h4
  have h5 : eP m (α.comp β) z = z := by rw [eP_apply, h4, H.cube_pow]
  have h6 := eP_fix (m := m) H.hδ z
  rwa [h5] at h6

end Hyp

@[expose] def WP (α β : M →* M) : Wt → M → Prop
  | .w0, y => α y = y ∧ β y = y
  | .wa, y => β y = y ∧ nrm α y = 1
  | .wb, y => α y = y ∧ nrm β y = 1
  | .wp, y => α y = β y ∧ nrm α y = 1
  | .wm, y => α (β y) = y ∧ nrm α y = 1

@[expose] def prj (m : ℕ) (α β : M →* M) : Wt → M →* M
  | .w0 => (eP m β).comp (eP m α)
  | .wa => (eP m β).comp (fP m α)
  | .wb => (fP m β).comp (eP m α)
  | .wp => (eP m (gam α β)).comp ((fP m β).comp (fP m α))
  | .wm => (fP m (gam α β)).comp ((fP m β).comp (fP m α))

theorem Cm.prj_right {φ α β : M →* M} (m : ℕ) (h₁ : Cm φ α) (h₂ : Cm φ β) (w : Wt) :
    Cm φ (prj m α β w) := by
  cases w with
  | w0 => exact (h₂.eP_right m).comp_right (h₁.eP_right m)
  | wa => exact (h₂.eP_right m).comp_right (h₁.fP_right m)
  | wb => exact (h₂.fP_right m).comp_right (h₁.eP_right m)
  | wp =>
    exact ((h₁.gam_right h₂).eP_right m).comp_right ((h₂.fP_right m).comp_right (h₁.fP_right m))
  | wm =>
    exact ((h₁.gam_right h₂).fP_right m).comp_right ((h₂.fP_right m).comp_right (h₁.fP_right m))

namespace Hyp

variable {α β : M →* M} {m : ℕ}

theorem cm_α_prj (H : Hyp α β m) (w : Wt) : Cm α (prj m α β w) :=
  Cm.prj_right m (Cm.refl α) H.cm_αβ w

theorem cm_β_prj (H : Hyp α β m) (w : Wt) : Cm β (prj m α β w) :=
  Cm.prj_right m H.hc (Cm.refl β) w

theorem cm_γ_prj (H : Hyp α β m) (w : Wt) : Cm (gam α β) (prj m α β w) :=
  Cm.prj_right m ((Cm.refl α).gam_right H.cm_αβ).symm (H.hc.gam_right (Cm.refl β)).symm w

theorem cm_δ_prj (H : Hyp α β m) (w : Wt) : Cm (α.comp β) (prj m α β w) :=
  Cm.prj_right m ((Cm.refl α).comp_right H.cm_αβ).symm (H.hc.comp_right (Cm.refl β)).symm w

theorem nrm_β_of_eq (H : Hyp α β m) {y : M} (h : α y = β y) : nrm β y = nrm α y := by
  rw [nrm_apply, nrm_apply, ← h, H.ba, ← h]

theorem nrm_β_of_fix (H : Hyp α β m) {y : M} (h : α (β y) = y) : nrm β y = nrm α y := by
  have hb : β y = α (α y) := by rw [← H.hα (β y), h]
  have hbb : β (β y) = α y := by rw [hb, H.ba, H.ba, h]
  rw [nrm_apply, nrm_apply, hbb, hb, mul_right_comm]

theorem nrm_γ_of_fix (H : Hyp α β m) {y : M} (h : α (β y) = y) :
    nrm (gam α β) y = nrm α y := by
  have hb : β y = α (α y) := by rw [← H.hα (β y), h]
  have hbb : β (β y) = α y := by rw [hb, H.ba, H.ba, h]
  have hg : gam α β y = α (α y) := by rw [gam_apply, hbb]
  have hgg : gam α β (gam α β y) = α y := by
    rw [hg, gam_apply, H.ba, H.ba, H.ba, H.ba, hbb, H.hα]
  rw [nrm_apply, nrm_apply, hgg, hg, mul_right_comm]

theorem prj_mem (H : Hyp α β m) (w : Wt) (x : M) : WP α β w (prj m α β w x) := by
  have cnγ : Cm (nrm α) (gam α β) := cm_nα_α.gam_right H.cm_nα_β
  have cbγ : Cm (nrm β) (gam α β) := H.cm_nβ_α.gam_right cm_nβ_β
  cases w with
  | w0 =>
    refine ⟨?_, eP_fix H.hβ _⟩
    change α (eP m β (eP m α x)) = eP m β (eP m α x)
    rw [Cm.eP_right m H.cm_αβ, eP_fix H.hα]
  | wa =>
    refine ⟨eP_fix H.hβ _, ?_⟩
    change nrm α (eP m β (fP m α x)) = 1
    rw [Cm.eP_right m H.cm_nα_β, nrm_fP H.hα H.hm, map_one]
  | wb =>
    refine ⟨?_, nrm_fP H.hβ H.hm _⟩
    change α (fP m β (eP m α x)) = fP m β (eP m α x)
    rw [Cm.fP_right m H.cm_αβ, eP_fix H.hα]
  | wp =>
    refine ⟨H.eq_of_gam (eP_fix H.hγ _), ?_⟩
    change nrm α (eP m (gam α β) (fP m β (fP m α x))) = 1
    rw [Cm.eP_right m cnγ, Cm.fP_right m H.cm_nα_β, nrm_fP H.hα H.hm, map_one, map_one]
  | wm =>
    have h₁ : nrm α (fP m (gam α β) (fP m β (fP m α x))) = 1 := by
      rw [Cm.fP_right m cnγ, Cm.fP_right m H.cm_nα_β, nrm_fP H.hα H.hm, map_one, map_one]
    have h₂ : nrm β (fP m (gam α β) (fP m β (fP m α x))) = 1 := by
      rw [Cm.fP_right m cbγ, nrm_fP H.hβ H.hm, map_one]
    exact ⟨H.fix_of_nrm h₁ h₂ (nrm_fP H.hγ H.hm _), h₁⟩

theorem prj_decomp (m : ℕ) (α β : M →* M) (x : M) :
    prj m α β .w0 x * prj m α β .wa x * prj m α β .wb x * prj m α β .wp x *
      prj m α β .wm x = x := by
  change eP m β (eP m α x) * eP m β (fP m α x) * fP m β (eP m α x) *
    eP m (gam α β) (fP m β (fP m α x)) * fP m (gam α β) (fP m β (fP m α x)) = x
  calc _ = eP m β (eP m α x) * fP m β (eP m α x) *
        (eP m β (fP m α x) * (eP m (gam α β) (fP m β (fP m α x)) *
          fP m (gam α β) (fP m β (fP m α x)))) := by ac_rfl
    _ = x := by simp only [eP_mul_fP]

theorem stp (H : Hyp α β m) {y : M} (hy : WP α β .wp y) :
    nrm α y = 1 ∧ nrm β y = 1 ∧ gam α β y = y :=
  ⟨hy.2, (H.nrm_β_of_eq hy.1).trans hy.2, H.gam_of_eq hy.1⟩

theorem stm (H : Hyp α β m) {y : M} (hy : WP α β .wm y) :
    nrm α y = 1 ∧ nrm β y = 1 ∧ nrm (gam α β) y = 1 :=
  ⟨hy.2, (H.nrm_β_of_fix hy.1).trans hy.2, (H.nrm_γ_of_fix hy.1).trans hy.2⟩

theorem prj_w0 (H : Hyp α β m) {y : M} (hy : WP α β .w0 y) :
    prj m α β .w0 y = y ∧ prj m α β .wa y = 1 ∧ prj m α β .wb y = 1 ∧ prj m α β .wp y = 1 ∧
      prj m α β .wm y = 1 := by
  obtain ⟨h1, h2⟩ := hy
  simp only [prj, MonoidHom.comp_apply, eP_of_fix H.hm h1, fP_of_fix H.hm h1,
    eP_of_fix H.hm h2, fP_of_fix H.hm h2, map_one, and_self]

theorem prj_wa (H : Hyp α β m) {y : M} (hy : WP α β .wa y) :
    prj m α β .w0 y = 1 ∧ prj m α β .wa y = y ∧ prj m α β .wb y = 1 ∧ prj m α β .wp y = 1 ∧
      prj m α β .wm y = 1 := by
  obtain ⟨h2, n1⟩ := hy
  simp only [prj, MonoidHom.comp_apply, eP_of_nrm n1, fP_of_nrm n1,
    eP_of_fix H.hm h2, fP_of_fix H.hm h2, map_one, and_self]

theorem prj_wb (H : Hyp α β m) {y : M} (hy : WP α β .wb y) :
    prj m α β .w0 y = 1 ∧ prj m α β .wa y = 1 ∧ prj m α β .wb y = y ∧ prj m α β .wp y = 1 ∧
      prj m α β .wm y = 1 := by
  obtain ⟨h1, n2⟩ := hy
  simp only [prj, MonoidHom.comp_apply, eP_of_fix H.hm h1, fP_of_fix H.hm h1,
    eP_of_nrm n2, fP_of_nrm n2, map_one, and_self]

theorem prj_wp (H : Hyp α β m) {y : M} (hy : WP α β .wp y) :
    prj m α β .w0 y = 1 ∧ prj m α β .wa y = 1 ∧ prj m α β .wb y = 1 ∧ prj m α β .wp y = y ∧
      prj m α β .wm y = 1 := by
  obtain ⟨n1, n2, h3⟩ := H.stp hy
  simp only [prj, MonoidHom.comp_apply, eP_of_nrm n1, fP_of_nrm n1, eP_of_nrm n2,
    fP_of_nrm n2, eP_of_fix H.hm h3, fP_of_fix H.hm h3, map_one, and_self]

theorem prj_wm (H : Hyp α β m) {y : M} (hy : WP α β .wm y) :
    prj m α β .w0 y = 1 ∧ prj m α β .wa y = 1 ∧ prj m α β .wb y = 1 ∧ prj m α β .wp y = 1 ∧
      prj m α β .wm y = y := by
  obtain ⟨n1, n2, n3⟩ := H.stm hy
  simp only [prj, MonoidHom.comp_apply, eP_of_nrm n1, fP_of_nrm n1, eP_of_nrm n2,
    fP_of_nrm n2, eP_of_nrm n3, fP_of_nrm n3, map_one, and_self]

theorem prj_prod (H : Hyp α β m) {x0 xa xb xp xm : M} (h0 : WP α β .w0 x0)
    (h1 : WP α β .wa xa) (h2 : WP α β .wb xb) (h3 : WP α β .wp xp) (h4 : WP α β .wm xm) :
    prj m α β .w0 (x0 * xa * xb * xp * xm) = x0 ∧ prj m α β .wa (x0 * xa * xb * xp * xm) = xa ∧
      prj m α β .wb (x0 * xa * xb * xp * xm) = xb ∧
        prj m α β .wp (x0 * xa * xb * xp * xm) = xp ∧
          prj m α β .wm (x0 * xa * xb * xp * xm) = xm := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := H.prj_w0 h0
  obtain ⟨b0, b1, b2, b3, b4⟩ := H.prj_wa h1
  obtain ⟨c0, c1, c2, c3, c4⟩ := H.prj_wb h2
  obtain ⟨d0, d1, d2, d3, d4⟩ := H.prj_wp h3
  obtain ⟨e0, e1, e2, e3, e4⟩ := H.prj_wm h4
  simp only [map_mul, a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, c0, c1, c2, c3, c4, d0, d1, d2,
    d3, d4, e0, e1, e2, e3, e4, mul_one, one_mul, and_self]

theorem decomp (H : Hyp α β m) (x : M) :
    WP α β .w0 (prj m α β .w0 x) ∧ WP α β .wa (prj m α β .wa x) ∧ WP α β .wb (prj m α β .wb x) ∧
      WP α β .wp (prj m α β .wp x) ∧ WP α β .wm (prj m α β .wm x) ∧
        prj m α β .w0 x * prj m α β .wa x * prj m α β .wb x * prj m α β .wp x *
          prj m α β .wm x = x :=
  ⟨H.prj_mem _ x, H.prj_mem _ x, H.prj_mem _ x, H.prj_mem _ x, H.prj_mem _ x,
    prj_decomp m α β x⟩

theorem unique (H : Hyp α β m) {x0 xa xb xp xm y0 ya yb yp ym : M} (h0 : WP α β .w0 x0)
    (h1 : WP α β .wa xa) (h2 : WP α β .wb xb) (h3 : WP α β .wp xp) (h4 : WP α β .wm xm)
    (h0' : WP α β .w0 y0) (h1' : WP α β .wa ya) (h2' : WP α β .wb yb) (h3' : WP α β .wp yp)
    (h4' : WP α β .wm ym) (e : x0 * xa * xb * xp * xm = y0 * ya * yb * yp * ym) :
    x0 = y0 ∧ xa = ya ∧ xb = yb ∧ xp = yp ∧ xm = ym := by
  obtain ⟨k0, k1, k2, k3, k4⟩ := H.prj_prod h0 h1 h2 h3 h4
  obtain ⟨l0, l1, l2, l3, l4⟩ := H.prj_prod h0' h1' h2' h3' h4'
  rw [e] at k0 k1 k2 k3 k4
  exact ⟨k0.symm.trans l0, k1.symm.trans l1, k2.symm.trans l2, k3.symm.trans l3,
    k4.symm.trans l4⟩

theorem indep (H : Hyp α β m) {x0 xa xb xp xm : M} (h0 : WP α β .w0 x0)
    (h1 : WP α β .wa xa) (h2 : WP α β .wb xb) (h3 : WP α β .wp xp) (h4 : WP α β .wm xm)
    (e : x0 * xa * xb * xp * xm = 1) : x0 = 1 ∧ xa = 1 ∧ xb = 1 ∧ xp = 1 ∧ xm = 1 := by
  have hone : WP α β .w0 (1 : M) ∧ WP α β .wa (1 : M) ∧ WP α β .wb (1 : M) ∧
      WP α β .wp (1 : M) ∧ WP α β .wm (1 : M) := by
    simp only [WP, map_one, and_self]
  obtain ⟨o0, o1, o2, o3, o4⟩ := hone
  exact H.unique h0 h1 h2 h3 h4 o0 o1 o2 o3 o4 (by rw [e, mul_one, mul_one, mul_one, mul_one])

theorem WP_map (H : Hyp α β m) {w : Wt} {y : M} (hy : WP α β w y) :
    WP α β w (α y) ∧ WP α β w (β y) := by
  cases w with
  | w0 =>
    obtain ⟨h1, h2⟩ := hy
    exact ⟨by rw [h1]; exact ⟨h1, h2⟩, by rw [h2]; exact ⟨h1, h2⟩⟩
  | wa =>
    obtain ⟨h2, n1⟩ := hy
    exact ⟨⟨by rw [H.ba, h2], by rw [nrm_map H.hα, n1]⟩, by rw [h2]; exact ⟨h2, n1⟩⟩
  | wb =>
    obtain ⟨h1, n2⟩ := hy
    exact ⟨by rw [h1]; exact ⟨h1, n2⟩, ⟨by rw [H.ab, h1], by rw [nrm_map H.hβ, n2]⟩⟩
  | wp =>
    obtain ⟨h1, n1⟩ := hy
    refine ⟨⟨by rw [H.ba, ← h1], by rw [nrm_map H.hα, n1]⟩, ⟨by rw [H.ab, h1], ?_⟩⟩
    rw [← H.hc.nrm_right y, n1, map_one]
  | wm =>
    obtain ⟨h1, n1⟩ := hy
    refine ⟨⟨by rw [H.ba, h1], by rw [nrm_map H.hα, n1]⟩, ⟨by rw [H.ab (β y), h1], ?_⟩⟩
    rw [← H.hc.nrm_right y, n1, map_one]

theorem fix_α (H : Hyp α β m) {x : M} (hx : α x = x) :
    prj m α β .wa x = 1 ∧ prj m α β .wp x = 1 ∧ prj m α β .wm x = 1 := by
  have key : ∀ w, α (prj m α β w x) = prj m α β w x := fun w => by rw [H.cm_α_prj w x, hx]
  exact ⟨eq_one_of_fix_nrm H.hm (key _) (H.prj_mem .wa x).2,
    eq_one_of_fix_nrm H.hm (key _) (H.prj_mem .wp x).2,
    eq_one_of_fix_nrm H.hm (key _) (H.prj_mem .wm x).2⟩

theorem fix_β (H : Hyp α β m) {x : M} (hx : β x = x) :
    prj m α β .wb x = 1 ∧ prj m α β .wp x = 1 ∧ prj m α β .wm x = 1 := by
  have key : ∀ w, β (prj m α β w x) = prj m α β w x := fun w => by rw [H.cm_β_prj w x, hx]
  refine ⟨eq_one_of_fix_nrm H.hm (key _) (H.prj_mem .wb x).2, ?_, ?_⟩
  · obtain ⟨h1, n1⟩ := H.prj_mem .wp x
    exact eq_one_of_fix_nrm H.hm (h1.trans (key _)) n1
  · obtain ⟨h1, n1⟩ := H.prj_mem .wm x
    rw [key] at h1
    exact eq_one_of_fix_nrm H.hm h1 n1

theorem fix_γ (H : Hyp α β m) {x : M} (hx : α x = β x) :
    prj m α β .wa x = 1 ∧ prj m α β .wb x = 1 ∧ prj m α β .wm x = 1 := by
  have key : ∀ w, gam α β (prj m α β w x) = prj m α β w x := fun w => by
    rw [H.cm_γ_prj w x, H.gam_of_eq hx]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨h2, n1⟩ := H.prj_mem .wa x
    have k := key .wa
    rw [gam_apply, h2, h2] at k
    exact eq_one_of_fix_nrm H.hm k n1
  · obtain ⟨h1, n2⟩ := H.prj_mem .wb x
    have k := H.eq_of_gam (key .wb)
    rw [h1] at k
    exact eq_one_of_fix_nrm H.hm k.symm n2
  · obtain ⟨h1, n1⟩ := H.prj_mem .wm x
    have k := H.eq_of_gam (key .wm)
    rw [← k] at h1
    have k2 := H.hα (prj m α β .wm x)
    rw [h1] at k2
    exact eq_one_of_fix_nrm H.hm k2 n1

theorem fix_δ (H : Hyp α β m) {x : M} (hx : α (β x) = x) :
    prj m α β .wa x = 1 ∧ prj m α β .wb x = 1 ∧ prj m α β .wp x = 1 := by
  have key : ∀ w, α (β (prj m α β w x)) = prj m α β w x := fun w =>
    (H.cm_δ_prj w x).trans (congrArg (prj m α β w) hx)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨h2, n1⟩ := H.prj_mem .wa x
    have k := key .wa
    rw [h2] at k
    exact eq_one_of_fix_nrm H.hm k n1
  · obtain ⟨h1, n2⟩ := H.prj_mem .wb x
    exact eq_one_of_fix_nrm H.hm (H.inj_α ((key .wb).trans h1.symm)) n2
  · obtain ⟨h1, n1⟩ := H.prj_mem .wp x
    have k := key .wp
    rw [← h1] at k
    have k2 := H.hα (prj m α β .wp x)
    rw [k] at k2
    exact eq_one_of_fix_nrm H.hm k2 n1

end Hyp

end Cl2Wt

variable {P : Type*} [Group P]

structure AbInv2 (a b : MulAut P) (A : Subgroup P) : Prop where
  comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x
  inva : ∀ x ∈ A, a x ∈ A
  invb : ∀ x ∈ A, b x ∈ A

namespace Cl2Wt

abbrev cg (A : Subgroup P) (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : CommGroup A :=
  { A.toGroup with mul_comm := fun x y => Subtype.ext (hc x x.2 y y.2) }

@[expose] def res (a : MulAut P) (A : Subgroup P) (ha : ∀ x ∈ A, a x ∈ A) : A →* A where
  toFun x := ⟨a x.1, ha x.1 x.2⟩
  map_one' := Subtype.ext (map_one a)
  map_mul' x y := Subtype.ext (map_mul a x.1 y.1)

theorem cube_apply {a : MulAut P} (ha : a ^ 3 = 1) (x : P) : a (a (a x)) = x := by
  rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_three', ha]
  rfl

theorem exists_cube_root [Finite P] (hP : IsPGroup 2 P) :
    ∃ m : ℕ, ∀ y : P, (y ^ m) ^ 3 = y := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP
  have hcop : Nat.Coprime 3 (Nat.card P) := hn ▸ Nat.Coprime.pow_right n (by norm_num)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hcop Nat.card_pos.ne'
  refine ⟨m, fun y => ?_⟩
  have h1 : y ^ (3 * m) = y ^ 1 :=
    pow_eq_pow_iff_modEq.2 (Nat.ModEq.of_dvd (orderOf_dvd_natCard y) hm)
  rw [← pow_mul, mul_comm, h1, pow_one]

theorem eps_mul_of_mem {a : MulAut P} {A : Subgroup P} (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (ha : ∀ x ∈ A, a x ∈ A) {x y : P} (hx : x ∈ A) (hy : y ∈ A) :
    eps a (x * y) = eps a x * eps a y := by
  let _ := cg A hc
  exact congrArg Subtype.val (map_mul (nrm (res a A ha)) (⟨x, hx⟩ : A) ⟨y, hy⟩)

theorem eps_inv_of_mem {a : MulAut P} {A : Subgroup P} (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (ha : ∀ x ∈ A, a x ∈ A) {x : P} (hx : x ∈ A) : eps a x⁻¹ = (eps a x)⁻¹ := by
  let _ := cg A hc
  exact congrArg Subtype.val (map_inv (nrm (res a A ha)) (⟨x, hx⟩ : A))

end Cl2Wt

@[expose] def wsub (a b : MulAut P) (A : Subgroup P) (h : AbInv2 a b A) : Wt → Subgroup P
  | .w0 => { carrier := {x | x ∈ A ∧ a x = x ∧ b x = x}
             mul_mem' := fun {x y} hx hy => ⟨A.mul_mem hx.1 hy.1,
               by rw [map_mul, hx.2.1, hy.2.1], by rw [map_mul, hx.2.2, hy.2.2]⟩
             one_mem' := ⟨A.one_mem, map_one a, map_one b⟩
             inv_mem' := fun {x} hx => ⟨A.inv_mem hx.1, by rw [map_inv, hx.2.1],
               by rw [map_inv, hx.2.2]⟩ }
  | .wa => { carrier := {x | x ∈ A ∧ b x = x ∧ eps a x = 1}
             mul_mem' := fun {x y} hx hy => ⟨A.mul_mem hx.1 hy.1,
               by rw [map_mul, hx.2.1, hy.2.1],
               by rw [Cl2Wt.eps_mul_of_mem h.comm h.inva hx.1 hy.1, hx.2.2, hy.2.2, one_mul]⟩
             one_mem' := ⟨A.one_mem, map_one b, by simp [eps]⟩
             inv_mem' := fun {x} hx => ⟨A.inv_mem hx.1, by rw [map_inv, hx.2.1],
               by rw [Cl2Wt.eps_inv_of_mem h.comm h.inva hx.1, hx.2.2, inv_one]⟩ }
  | .wb => { carrier := {x | x ∈ A ∧ a x = x ∧ eps b x = 1}
             mul_mem' := fun {x y} hx hy => ⟨A.mul_mem hx.1 hy.1,
               by rw [map_mul, hx.2.1, hy.2.1],
               by rw [Cl2Wt.eps_mul_of_mem h.comm h.invb hx.1 hy.1, hx.2.2, hy.2.2, one_mul]⟩
             one_mem' := ⟨A.one_mem, map_one a, by simp [eps]⟩
             inv_mem' := fun {x} hx => ⟨A.inv_mem hx.1, by rw [map_inv, hx.2.1],
               by rw [Cl2Wt.eps_inv_of_mem h.comm h.invb hx.1, hx.2.2, inv_one]⟩ }
  | .wp => { carrier := {x | x ∈ A ∧ a x = b x ∧ eps a x = 1}
             mul_mem' := fun {x y} hx hy => ⟨A.mul_mem hx.1 hy.1,
               by rw [map_mul, map_mul, hx.2.1, hy.2.1],
               by rw [Cl2Wt.eps_mul_of_mem h.comm h.inva hx.1 hy.1, hx.2.2, hy.2.2, one_mul]⟩
             one_mem' := ⟨A.one_mem, by rw [map_one, map_one], by simp [eps]⟩
             inv_mem' := fun {x} hx => ⟨A.inv_mem hx.1, by rw [map_inv, map_inv, hx.2.1],
               by rw [Cl2Wt.eps_inv_of_mem h.comm h.inva hx.1, hx.2.2, inv_one]⟩ }
  | .wm => { carrier := {x | x ∈ A ∧ a (b x) = x ∧ eps a x = 1}
             mul_mem' := fun {x y} hx hy => ⟨A.mul_mem hx.1 hy.1,
               by rw [map_mul, map_mul, hx.2.1, hy.2.1],
               by rw [Cl2Wt.eps_mul_of_mem h.comm h.inva hx.1 hy.1, hx.2.2, hy.2.2, one_mul]⟩
             one_mem' := ⟨A.one_mem, by rw [map_one, map_one], by simp [eps]⟩
             inv_mem' := fun {x} hx => ⟨A.inv_mem hx.1, by rw [map_inv, map_inv, hx.2.1],
               by rw [Cl2Wt.eps_inv_of_mem h.comm h.inva hx.1, hx.2.2, inv_one]⟩ }

@[expose] def omega1 (A : Subgroup P) (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : Subgroup P where
  carrier := {x | x ∈ A ∧ x * x = 1}
  mul_mem' := fun {x y} hx hy => ⟨A.mul_mem hx.1 hy.1, by
    rw [mul_assoc, ← mul_assoc y x y, ← hc x hx.1 y hy.1, mul_assoc, hy.2, mul_one, hx.2]⟩
  one_mem' := ⟨A.one_mem, mul_one 1⟩
  inv_mem' := fun {x} hx => ⟨A.inv_mem hx.1, by rw [← mul_inv_rev, hx.2, inv_one]⟩

variable {a b : MulAut P} {A : Subgroup P}

theorem mem_wsub_w0 (h : AbInv2 a b A) {x : P} :
    x ∈ wsub a b A h .w0 ↔ x ∈ A ∧ a x = x ∧ b x = x := Iff.rfl
theorem mem_wsub_wa (h : AbInv2 a b A) {x : P} :
    x ∈ wsub a b A h .wa ↔ x ∈ A ∧ b x = x ∧ eps a x = 1 := Iff.rfl
theorem mem_wsub_wb (h : AbInv2 a b A) {x : P} :
    x ∈ wsub a b A h .wb ↔ x ∈ A ∧ a x = x ∧ eps b x = 1 := Iff.rfl
theorem mem_wsub_wp (h : AbInv2 a b A) {x : P} :
    x ∈ wsub a b A h .wp ↔ x ∈ A ∧ a x = b x ∧ eps a x = 1 := Iff.rfl
theorem mem_wsub_wm (h : AbInv2 a b A) {x : P} :
    x ∈ wsub a b A h .wm ↔ x ∈ A ∧ a (b x) = x ∧ eps a x = 1 := Iff.rfl
theorem mem_omega1 (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {x : P} :
    x ∈ omega1 A hc ↔ x ∈ A ∧ x * x = 1 := Iff.rfl

theorem Cl2Wt.omega1_le (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : omega1 A hc ≤ A :=
  fun _ hx => hx.1

theorem wsub_le (h : AbInv2 a b A) (w : Wt) : wsub a b A h w ≤ A := by
  cases w <;> exact fun x hx => hx.1

theorem AbInv2.mono (h : AbInv2 a b A) {E : Subgroup P} (hE : E ≤ A)
    (hEa : ∀ x ∈ E, a x ∈ E) (hEb : ∀ x ∈ E, b x ∈ E) : AbInv2 a b E :=
  ⟨fun x hx y hy => h.comm x (hE hx) y (hE hy), hEa, hEb⟩

private theorem mem_wsub_of_le (h : AbInv2 a b A) {E : Subgroup P} (hE : E ≤ A)
    (hE' : AbInv2 a b E) (w : Wt) {x : P} :
    x ∈ wsub a b E hE' w ↔ x ∈ E ∧ x ∈ wsub a b A h w := by
  cases w <;> exact ⟨fun hx => ⟨hx.1, hE hx.1, hx.2⟩, fun hx => ⟨hx.1, hx.2.2⟩⟩

theorem wsub_of_le (h : AbInv2 a b A) {E : Subgroup P} (hE : E ≤ A)
    (hEa : ∀ x ∈ E, a x ∈ E) (hEb : ∀ x ∈ E, b x ∈ E) (w : Wt) :
    wsub a b E (h.mono hE hEa hEb) w = E ⊓ wsub a b A h w := by
  ext x
  rw [Subgroup.mem_inf]
  exact mem_wsub_of_le h hE _ w

theorem AbInv2.omega1 (h : AbInv2 a b A) : AbInv2 a b (omega1 A h.comm) :=
  ⟨fun x hx y hy => h.comm x hx.1 y hy.1,
    fun x hx => ⟨h.inva x hx.1, by rw [← map_mul, hx.2, map_one]⟩,
    fun x hx => ⟨h.invb x hx.1, by rw [← map_mul, hx.2, map_one]⟩⟩

namespace Cl2Wt

theorem mem_wsub_iff (h : AbInv2 a b A) (w : Wt) (y : A) :
    (y : P) ∈ wsub a b A h w ↔
      @WP A (cg A h.comm) (res a A h.inva) (res b A h.invb) w y := by
  cases w <;>
    exact ⟨fun hy => ⟨Subtype.ext hy.2.1, Subtype.ext hy.2.2⟩,
      fun hy => ⟨y.2, congrArg Subtype.val hy.1, congrArg Subtype.val hy.2⟩⟩

theorem hyp_res [Finite P] (hP : IsPGroup 2 P) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a * b = b * a) (h : AbInv2 a b A) :
    ∃ m, @Hyp A (cg A h.comm) (res a A h.inva) (res b A h.invb) m := by
  obtain ⟨m, hm⟩ := exists_cube_root hP
  let _ := cg A h.comm
  refine ⟨m, fun y => Subtype.ext (cube_apply ha y), fun y => Subtype.ext (cube_apply hb y),
    fun y => Subtype.ext ?_, fun y => Subtype.ext (hm y)⟩
  change b (a y) = a (b y)
  rw [← MulAut.mul_apply, ← hab, MulAut.mul_apply]

end Cl2Wt

open Cl2Wt in
theorem wsub_inv [Finite P] (hP : IsPGroup 2 P) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a * b = b * a) (h : AbInv2 a b A) (w : Wt) {x : P} (hx : x ∈ wsub a b A h w) :
    a x ∈ wsub a b A h w ∧ b x ∈ wsub a b A h w := by
  obtain ⟨m, H⟩ := hyp_res hP ha hb hab h
  let _ := cg A h.comm
  obtain ⟨h1, h2⟩ := H.WP_map ((mem_wsub_iff h w ⟨x, wsub_le h w hx⟩).1 hx)
  exact ⟨(mem_wsub_iff h w _).2 h1, (mem_wsub_iff h w _).2 h2⟩

open Cl2Wt in
theorem wsub_decomp [Finite P] (hP : IsPGroup 2 P) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a * b = b * a) (h : AbInv2 a b A) {x : P} (hx : x ∈ A) :
    ∃ x0 ∈ wsub a b A h .w0, ∃ xa ∈ wsub a b A h .wa, ∃ xb ∈ wsub a b A h .wb,
      ∃ xp ∈ wsub a b A h .wp, ∃ xm ∈ wsub a b A h .wm, x = x0 * xa * xb * xp * xm := by
  obtain ⟨m, H⟩ := hyp_res hP ha hb hab h
  let _ := cg A h.comm
  obtain ⟨h0, h1, h2, h3, h4, e⟩ := H.decomp ⟨x, hx⟩
  exact ⟨_, (mem_wsub_iff h _ _).2 h0, _, (mem_wsub_iff h _ _).2 h1, _,
    (mem_wsub_iff h _ _).2 h2, _, (mem_wsub_iff h _ _).2 h3, _, (mem_wsub_iff h _ _).2 h4,
    (congrArg Subtype.val e).symm⟩

open Cl2Wt in
theorem wsub_indep [Finite P] (hP : IsPGroup 2 P) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a * b = b * a) (h : AbInv2 a b A) {x0 xa xb xp xm : P}
    (h0 : x0 ∈ wsub a b A h .w0) (h1 : xa ∈ wsub a b A h .wa) (h2 : xb ∈ wsub a b A h .wb)
    (h3 : xp ∈ wsub a b A h .wp) (h4 : xm ∈ wsub a b A h .wm)
    (hx : x0 * xa * xb * xp * xm = 1) :
    x0 = 1 ∧ xa = 1 ∧ xb = 1 ∧ xp = 1 ∧ xm = 1 := by
  obtain ⟨m, H⟩ := hyp_res hP ha hb hab h
  let _ := cg A h.comm
  obtain ⟨k0, k1, k2, k3, k4⟩ := H.indep ((mem_wsub_iff h _ ⟨x0, wsub_le h _ h0⟩).1 h0)
    ((mem_wsub_iff h _ ⟨xa, wsub_le h _ h1⟩).1 h1) ((mem_wsub_iff h _ ⟨xb, wsub_le h _ h2⟩).1 h2)
    ((mem_wsub_iff h _ ⟨xp, wsub_le h _ h3⟩).1 h3) ((mem_wsub_iff h _ ⟨xm, wsub_le h _ h4⟩).1 h4)
    (Subtype.ext hx)
  exact ⟨congrArg Subtype.val k0, congrArg Subtype.val k1, congrArg Subtype.val k2,
    congrArg Subtype.val k3, congrArg Subtype.val k4⟩

open Cl2Wt in
theorem wsub_card [Finite P] (hP : IsPGroup 2 P) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a * b = b * a) (h : AbInv2 a b A) :
    Nat.card A = Nat.card (wsub a b A h .w0) * Nat.card (wsub a b A h .wa) *
      Nat.card (wsub a b A h .wb) * Nat.card (wsub a b A h .wp) *
        Nat.card (wsub a b A h .wm) := by
  obtain ⟨m, H⟩ := hyp_res hP ha hb hab h
  let _ := cg A h.comm
  have mem : ∀ w (z : wsub a b A h w),
      @WP A (cg A h.comm) (res a A h.inva) (res b A h.invb) w ⟨z, wsub_le h w z.2⟩ :=
    fun w z => (mem_wsub_iff h w _).1 z.2
  let f : wsub a b A h .w0 × wsub a b A h .wa × wsub a b A h .wb × wsub a b A h .wp ×
      wsub a b A h .wm → A := fun p =>
    ⟨p.1 * p.2.1 * p.2.2.1 * p.2.2.2.1 * p.2.2.2.2,
      A.mul_mem (A.mul_mem (A.mul_mem (A.mul_mem (wsub_le h _ p.1.2) (wsub_le h _ p.2.1.2))
        (wsub_le h _ p.2.2.1.2)) (wsub_le h _ p.2.2.2.1.2)) (wsub_le h _ p.2.2.2.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨x0, xa, xb, xp, xm⟩ ⟨y0, ya, yb, yp, ym⟩ hxy
      have e : (x0 : P) * xa * xb * xp * xm = y0 * ya * yb * yp * ym := congrArg Subtype.val hxy
      obtain ⟨k0, k1, k2, k3, k4⟩ := H.unique (mem .w0 x0) (mem .wa xa) (mem .wb xb)
        (mem .wp xp) (mem .wm xm) (mem .w0 y0) (mem .wa ya) (mem .wb yb) (mem .wp yp)
        (mem .wm ym) (Subtype.ext e)
      simp only [Prod.mk.injEq]
      have v : ∀ {u v : A}, u = v → (u : P) = v := fun e => congrArg Subtype.val e
      exact ⟨Subtype.ext (v k0), Subtype.ext (v k1), Subtype.ext (v k2), Subtype.ext (v k3),
        Subtype.ext (v k4)⟩
    · intro y
      obtain ⟨x0, h0, xa, h1, xb, h2, xp, h3, xm, h4, e⟩ := wsub_decomp hP ha hb hab h y.2
      exact ⟨(⟨x0, h0⟩, ⟨xa, h1⟩, ⟨xb, h2⟩, ⟨xp, h3⟩, ⟨xm, h4⟩), Subtype.ext e.symm⟩
  rw [← Nat.card_eq_of_bijective f hf]
  simp only [Nat.card_prod, mul_assoc]

theorem wsub_decomp_sub [Finite P] (hP : IsPGroup 2 P) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a * b = b * a) (h : AbInv2 a b A) {N : Subgroup P} (hN : N ≤ A)
    (hNa : ∀ x ∈ N, a x ∈ N) (hNb : ∀ x ∈ N, b x ∈ N) {x : P} (hx : x ∈ N) :
    ∃ x0 ∈ N ⊓ wsub a b A h .w0, ∃ xa ∈ N ⊓ wsub a b A h .wa,
      ∃ xb ∈ N ⊓ wsub a b A h .wb, ∃ xp ∈ N ⊓ wsub a b A h .wp,
        ∃ xm ∈ N ⊓ wsub a b A h .wm, x = x0 * xa * xb * xp * xm := by
  simp only [← wsub_of_le h hN hNa hNb]
  exact wsub_decomp hP ha hb hab (h.mono hN hNa hNb) hx

theorem wsub_card_ge_four [Finite P] (hP : IsPGroup 2 P) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a * b = b * a) (h : AbInv2 a b A) (hE : ∀ x ∈ A, x * x = 1) {w : Wt}
    (hw : w ≠ .w0) (hne : wsub a b A h w ≠ ⊥) : 4 ≤ Nat.card (wsub a b A h w) := by
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hxA : (x : P) ∈ A := wsub_le h w x.2
  obtain ⟨φ, hφW, hφ⟩ : ∃ φ : MulAut P, φ x ∈ wsub a b A h w ∧ eps φ x = 1 := by
    have hinv := wsub_inv hP ha hb hab h w x.2
    have hx2 := x.2
    cases w with
    | w0 => exact absurd rfl hw
    | wa => exact ⟨a, hinv.1, hx2.2.2⟩
    | wb => exact ⟨b, hinv.2, hx2.2.2⟩
    | wp => exact ⟨a, hinv.1, hx2.2.2⟩
    | wm => exact ⟨a, hinv.1, hx2.2.2⟩
  have hfix : φ x ≠ x := fun e => hx1 (Subtype.ext (by
    have h3 : eps φ x = x := by rw [eps, e, e, hE x hxA, one_mul]
    rw [← h3, hφ]
    rfl))
  have hφ1 : (⟨φ x, hφW⟩ : wsub a b A h w) ≠ 1 := fun e =>
    hx1 (Subtype.ext ((map_eq_one_iff φ φ.injective).1 (congrArg Subtype.val e)))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hP.to_subgroup (wsub a b A h w))
  have c1 : Nat.card (wsub a b A h w) ≠ 1 := fun e => hne (Subgroup.card_eq_one.1 e)
  have c2 : Nat.card (wsub a b A h w) ≠ 2 := fun e => by
    obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (1 : wsub a b A h w)).1 e
    exact hfix (congrArg Subtype.val ((hu _ hφ1).trans (hu _ hx1).symm))
  rw [hk] at c1 c2 ⊢
  rcases k with _ | _ | k
  · exact absurd (pow_zero 2) c1
  · exact absurd (pow_one 2) c2
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem wsub_omega1_ne_bot [Finite P] (hP : IsPGroup 2 P) (_ha : a ^ 3 = 1) (_hb : b ^ 3 = 1)
    (_hab : a * b = b * a) (h : AbInv2 a b A) {w : Wt} (hne : wsub a b A h w ≠ ⊥) :
    wsub a b (omega1 A h.comm) h.omega1 w ≠ ⊥ := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hP.to_subgroup (wsub a b A h w))
  have c1 : Nat.card (wsub a b A h w) ≠ 1 := fun e => hne (Subgroup.card_eq_one.1 e)
  have hdvd : 2 ∣ Nat.card (wsub a b A h w) := by
    rw [hk] at c1 ⊢
    rcases k with _ | k
    · exact absurd (pow_zero 2) c1
    · exact dvd_pow_self 2 (Nat.succ_ne_zero k)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hzz : (z : P) * z = 1 := by
    have h2 := pow_orderOf_eq_one z
    rw [hz, pow_two] at h2
    exact congrArg Subtype.val h2
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  refine ⟨⟨z, (mem_wsub_of_le h (Cl2Wt.omega1_le h.comm) h.omega1 w).2
    ⟨⟨wsub_le h w z.2, hzz⟩, z.2⟩⟩, fun e => ?_⟩
  have hz1 : z = 1 :=
    Subtype.ext (congrArg (fun u : wsub a b (omega1 A h.comm) h.omega1 w => (u : P)) e)
  rw [hz1, orderOf_one] at hz
  exact absurd hz (by norm_num)

open Cl2Wt in
theorem fix_a_decomp [Finite P] (hP : IsPGroup 2 P) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a * b = b * a) (h : AbInv2 a b A) {x : P} (hx : x ∈ A) (hax : a x = x) :
    ∃ x0 ∈ wsub a b A h .w0, ∃ xb ∈ wsub a b A h .wb, x = x0 * xb := by
  obtain ⟨m, H⟩ := hyp_res hP ha hb hab h
  let _ := cg A h.comm
  obtain ⟨h0, -, h2, -, -, e⟩ := H.decomp ⟨x, hx⟩
  obtain ⟨k1, k3, k4⟩ := H.fix_α (x := ⟨x, hx⟩) (Subtype.ext hax)
  simp only [k1, k3, k4, mul_one] at e
  exact ⟨_, (mem_wsub_iff h _ _).2 h0, _, (mem_wsub_iff h _ _).2 h2,
    (congrArg Subtype.val e).symm⟩

open Cl2Wt in
theorem fix_b_decomp [Finite P] (hP : IsPGroup 2 P) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a * b = b * a) (h : AbInv2 a b A) {x : P} (hx : x ∈ A) (hbx : b x = x) :
    ∃ x0 ∈ wsub a b A h .w0, ∃ xa ∈ wsub a b A h .wa, x = x0 * xa := by
  obtain ⟨m, H⟩ := hyp_res hP ha hb hab h
  let _ := cg A h.comm
  obtain ⟨h0, h1, -, -, -, e⟩ := H.decomp ⟨x, hx⟩
  obtain ⟨k2, k3, k4⟩ := H.fix_β (x := ⟨x, hx⟩) (Subtype.ext hbx)
  simp only [k2, k3, k4, mul_one] at e
  exact ⟨_, (mem_wsub_iff h _ _).2 h0, _, (mem_wsub_iff h _ _).2 h1,
    (congrArg Subtype.val e).symm⟩

open Cl2Wt in
theorem fix_ab_inv_decomp [Finite P] (hP : IsPGroup 2 P) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a * b = b * a) (h : AbInv2 a b A) {x : P} (hx : x ∈ A) (hx' : a x = b x) :
    ∃ x0 ∈ wsub a b A h .w0, ∃ xp ∈ wsub a b A h .wp, x = x0 * xp := by
  obtain ⟨m, H⟩ := hyp_res hP ha hb hab h
  let _ := cg A h.comm
  obtain ⟨h0, -, -, h3, -, e⟩ := H.decomp ⟨x, hx⟩
  obtain ⟨k1, k2, k4⟩ := H.fix_γ (x := ⟨x, hx⟩) (Subtype.ext hx')
  simp only [k1, k2, k4, mul_one] at e
  exact ⟨_, (mem_wsub_iff h _ _).2 h0, _, (mem_wsub_iff h _ _).2 h3,
    (congrArg Subtype.val e).symm⟩

open Cl2Wt in
theorem fix_ab_decomp [Finite P] (hP : IsPGroup 2 P) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a * b = b * a) (h : AbInv2 a b A) {x : P} (hx : x ∈ A) (hx' : a (b x) = x) :
    ∃ x0 ∈ wsub a b A h .w0, ∃ xm ∈ wsub a b A h .wm, x = x0 * xm := by
  obtain ⟨m, H⟩ := hyp_res hP ha hb hab h
  let _ := cg A h.comm
  obtain ⟨h0, -, -, -, h4, e⟩ := H.decomp ⟨x, hx⟩
  obtain ⟨k1, k2, k3⟩ := H.fix_δ (x := ⟨x, hx⟩) (Subtype.ext hx')
  simp only [k1, k2, k3, mul_one] at e
  exact ⟨_, (mem_wsub_iff h _ _).2 h0, _, (mem_wsub_iff h _ _).2 h4,
    (congrArg Subtype.val e).symm⟩

theorem mem_sqsub_iff (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {x : P} :
    x ∈ sqsub A ↔ ∃ u ∈ A, x = u * u := by
  let S : Subgroup P :=
    { carrier := {w | ∃ u ∈ A, w = u * u}
      mul_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
        refine ⟨u * v, A.mul_mem hu hv, ?_⟩
        calc u * u * (v * v) = u * (u * v) * v := by simp only [mul_assoc]
          _ = u * (v * u) * v := by rw [hc u hu v hv]
          _ = u * v * (u * v) := by simp only [mul_assoc]
      one_mem' := ⟨1, A.one_mem, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨u⁻¹, A.inv_mem hu, mul_inv_rev u u⟩ }
  refine ⟨fun hx => (Subgroup.closure_le S).2 (fun w hw => hw) hx, ?_⟩
  rintro ⟨u, hu, rfl⟩
  exact Subgroup.subset_closure ⟨u, hu, rfl⟩

theorem omega1_card_eq_relIndex_sqsub [Finite P] (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    Nat.card (omega1 A hc) = (sqsub A).relIndex A := by
  let f : A →* A :=
    { toFun := fun y => ⟨y * y, A.mul_mem y.2 y.2⟩
      map_one' := Subtype.ext (mul_one 1)
      map_mul' := fun x y => Subtype.ext (by
        change (x : P) * y * (x * y) = x * x * (y * y)
        calc (x : P) * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
          _ = x * (x * y) * y := by rw [hc y y.2 x x.2]
          _ = x * x * (y * y) := by simp only [mul_assoc]) }
  have hker : (omega1 A hc).subgroupOf A = f.ker := by
    ext y
    rw [Subgroup.mem_subgroupOf, mem_omega1, MonoidHom.mem_ker]
    exact ⟨fun hy => Subtype.ext hy.2, fun hy => ⟨y.2, congrArg Subtype.val hy⟩⟩
  have hrange : (sqsub A).subgroupOf A = f.range := by
    ext y
    rw [Subgroup.mem_subgroupOf, mem_sqsub_iff hc, MonoidHom.mem_range]
    constructor
    · rintro ⟨u, hu, hy⟩
      exact ⟨⟨u, hu⟩, Subtype.ext hy.symm⟩
    · rintro ⟨u, rfl⟩
      exact ⟨u, u.2, rfl⟩
  have h1 : Nat.card (omega1 A hc) = Nat.card f.ker := by
    rw [← hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Cl2Wt.omega1_le hc)).toEquiv.symm
  rw [h1, Subgroup.relIndex, hrange]
  have e1 := f.range.card_mul_index
  have e2 := f.ker.card_mul_index
  rw [Subgroup.index_ker] at e2
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := f.range)) (by rw [mul_comm, e2, e1])

end CFSG.GH74.E2
