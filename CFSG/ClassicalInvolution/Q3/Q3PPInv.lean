module

public import CFSG.ClassicalInvolution.Basic
public import CFSG.ClassicalInvolution.Generic.SL2Anticommute

public section

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

section Fpf

variable {Y : Type*} [Group Y]

theorem fpf_inverts_of_finite {W : Subgroup Y} [Finite W] {u : Y} (hu : u * u = 1)
    (hW : ∀ w ∈ W, u * w * u⁻¹ ∈ W) (hfpf : ∀ w ∈ W, u * w * u⁻¹ = w → w = 1) :
    (∀ w ∈ W, u * w * u⁻¹ = w⁻¹) ∧ ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
  have hinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  let f : W → W := fun w => ⟨(w : Y)⁻¹ * (u * w * u⁻¹), W.mul_mem (W.inv_mem w.2) (hW w w.2)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : (a : Y)⁻¹ * (u * a * u⁻¹) = (b : Y)⁻¹ * (u * b * u⁻¹) := congrArg Subtype.val hab
    have h2 : u * ((a : Y) * (b : Y)⁻¹) * u⁻¹ = (a : Y) * (b : Y)⁻¹ := by
      calc u * ((a : Y) * (b : Y)⁻¹) * u⁻¹
          = (u * a * u⁻¹) * (u * b * u⁻¹)⁻¹ := by group
        _ = (a : Y) * (b : Y)⁻¹ := by
          have h3 : u * (a : Y) * u⁻¹ = (a : Y) * ((b : Y)⁻¹ * (u * b * u⁻¹)) := by
            calc u * (a : Y) * u⁻¹ = (a : Y) * ((a : Y)⁻¹ * (u * a * u⁻¹)) := by group
              _ = _ := by rw [h1]
          rw [h3]
          group
    have h4 := hfpf _ (W.mul_mem a.2 (W.inv_mem b.2)) h2
    exact Subtype.ext (mul_inv_eq_one.mp h4)
  have hs : Function.Surjective f := Finite.injective_iff_surjective.mp hf
  have key : ∀ w ∈ W, u * w * u⁻¹ = w⁻¹ := by
    intro w hw
    obtain ⟨v, hv⟩ := hs ⟨w, hw⟩
    have hv' : (v : Y)⁻¹ * (u * v * u⁻¹) = w := congrArg Subtype.val hv
    rw [← hv', hinv]
    simp only [mul_inv_rev, inv_inv, hinv, mul_assoc, hu, mul_one]
  refine ⟨key, fun a ha b hb => ?_⟩
  have hab : u * (a * b) * u⁻¹ = (a * b)⁻¹ := key _ (W.mul_mem ha hb)
  have h1 : u * a * u⁻¹ = a⁻¹ := key a ha
  have h2 : u * b * u⁻¹ = b⁻¹ := key b hb
  have h3 : u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) := by group
  have h4 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ :=
    calc a⁻¹ * b⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) := by rw [h1, h2]
      _ = u * (a * b) * u⁻¹ := h3.symm
      _ = (a * b)⁻¹ := hab
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
  have h5 := congrArg (fun t => t⁻¹) h4
  simpa using h5.symm

end Fpf

end CFSG.ClassicalInvolution.Q3.Q3PP
