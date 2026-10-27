module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Fintype.EquivFin

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem rho_conj_mul_inv_not_mem (Q V : Subgroup G) (rho : G) (hVQ : V ≤ Q)
    (hVsq : ∀ v ∈ V, v * v = 1) (hρV : ∀ v ∈ V, rho * v * rho⁻¹ ∈ V)
    (hfix : ∀ q ∈ Q, rho * q = q * rho → q = 1) {b : G} (hbQ : b ∈ Q) (hbV : b ∉ V) :
    rho * b * rho⁻¹ * b⁻¹ ∉ V := by
  classical
  haveI : Finite V := Finite.of_injective (Subtype.val : V → G) Subtype.val_injective
  let φ : MulAut G := MulAut.conj rho
  have hφ_apply : ∀ x : G, φ x = rho * x * rho⁻¹ := fun x => MulAut.conj_apply rho x
  have hφV : ∀ v ∈ V, φ v ∈ V := fun v hv => by rw [hφ_apply]; exact hρV v hv
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb
    have h1 : (a * b) * (a * b) = 1 := hVsq (a * b) (V.mul_mem ha hb)
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hVsq a ha)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hVsq b hb)
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = b⁻¹ * a⁻¹ := by rw [mul_inv_rev]
      _ = b * a := by rw [ha', hb']
  have hf_inj : Function.Injective (fun x : V => (x : G) * (φ (x : G))⁻¹) := by
    intro x y hxy
    change (x : G) * (φ (x : G))⁻¹ = (y : G) * (φ (y : G))⁻¹ at hxy
    apply Subtype.ext
    let w : G := (y : G)⁻¹ * (x : G)
    have hwV : w ∈ V := V.mul_mem (V.inv_mem y.2) x.2
    have hw : w = φ w := by
      have h1 : (y : G)⁻¹ * ((x : G) * (φ (x : G))⁻¹) = (φ (y : G))⁻¹ := by
        rw [hxy, inv_mul_cancel_left]
      have h2 : w = (φ (y : G))⁻¹ * φ (x : G) := by
        have := congrArg (fun t => t * φ (x : G)) h1
        simpa [w, mul_assoc] using this
      calc w = (φ (y : G))⁻¹ * φ (x : G) := h2
        _ = φ ((y : G)⁻¹ * (x : G)) := by rw [← map_inv, ← map_mul]
        _ = φ w := rfl
    have hwcomm : rho * w = w * rho := by
      have h := congrArg (fun t => t * rho) hw
      rw [hφ_apply] at h
      simpa [mul_assoc] using h.symm
    have hw1 : w = 1 := hfix w (hVQ hwV) hwcomm
    have : (y : G) * ((y : G)⁻¹ * (x : G)) = (y : G) * 1 :=
      congrArg (fun t => (y : G) * t) hw1
    simpa [w, mul_assoc] using this
  have hf_surj : ∀ w ∈ V, ∃ v ∈ V, v * (φ v)⁻¹ = w := by
    intro w hw
    let f : V → V := fun x => ⟨(x : G) * (φ (x : G))⁻¹, V.mul_mem x.2 (V.inv_mem (hφV x x.2))⟩
    have hfinj : Function.Injective f := by
      intro x y hxy
      exact hf_inj (congrArg Subtype.val hxy)
    have hfsurj : Function.Surjective f := Finite.surjective_of_injective hfinj
    obtain ⟨v, hv⟩ := hfsurj ⟨w, hw⟩
    exact ⟨v, v.2, congrArg Subtype.val hv⟩
  have hH2 : ∀ b ∈ Q, b ∉ V → φ b * b⁻¹ ∉ V := by
    intro b hbQ hbV hmem
    obtain ⟨v₀, hv₀V, hv₀⟩ := hf_surj (φ b * b⁻¹) hmem
    have hφb : φ b = v₀ * (φ v₀)⁻¹ * b := by
      rw [hv₀, mul_assoc, inv_mul_cancel, mul_one]
    have hfix_eq : φ (v₀ * b) = v₀ * b := by
      rw [map_mul, hφb]
      calc φ v₀ * (v₀ * (φ v₀)⁻¹ * b)
          = (φ v₀ * v₀ * (φ v₀)⁻¹) * b := by group
        _ = (v₀ * φ v₀ * (φ v₀)⁻¹) * b := by
              rw [hVab (φ v₀) (hφV v₀ hv₀V) v₀ hv₀V]
        _ = v₀ * b := by group
    have hb' : v₀ * b ∈ Q := Q.mul_mem (hVQ hv₀V) hbQ
    have hb'comm : rho * (v₀ * b) = (v₀ * b) * rho := by
      have h := hfix_eq
      rw [hφ_apply] at h
      have hh := congrArg (fun t => t * rho) h
      simpa [mul_assoc] using hh
    have h1 : v₀ * b = 1 := hfix (v₀ * b) hb' hb'comm
    apply hbV
    have h2 : b = v₀⁻¹ := by
      have := congrArg (fun t => v₀⁻¹ * t) h1
      simpa [mul_assoc] using this
    rw [h2]
    exact V.inv_mem hv₀V
  intro hmem
  exact hH2 b hbQ hbV (by rw [hφ_apply]; exact hmem)

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
