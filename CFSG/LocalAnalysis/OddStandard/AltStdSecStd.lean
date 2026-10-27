module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecDefs

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

section Conj

variable {X : Type*} [Group X]

theorem mem_map_conj_iff {H : Subgroup X} {g x : X} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hh
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem mem_centralizer_map_conj_iff {A : Subgroup X} {g x : X} :
    x ∈ centralizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X) ↔
      g⁻¹ * x * g ∈ centralizer (A : Set X) := by
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h a ha
    have := h (g * a * g⁻¹) (mem_map_conj_iff.2 (by simpa [mul_assoc] using ha))
    calc a * (g⁻¹ * x * g) = g⁻¹ * ((g * a * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * a * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * x * g * a := by group
  · intro h y hy
    have hy' : g⁻¹ * y * g ∈ A := mem_map_conj_iff.1 hy
    have := h _ hy'
    calc y * x = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
      _ = x * y := by group

theorem mem_normalizer_map_conj_iff {A : Subgroup X} {g y : X} :
    y ∈ normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X) ↔
      g⁻¹ * y * g ∈ normalizer (A : Set X) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h a
    have := h (g * a * g⁻¹)
    simp only [mem_map_conj_iff] at this
    have e1 : g⁻¹ * (g * a * g⁻¹) * g = a := by group
    have e2 : g⁻¹ * (y * (g * a * g⁻¹) * y⁻¹) * g = (g⁻¹ * y * g) * a * (g⁻¹ * y * g)⁻¹ := by
      group
    rw [e1, e2] at this
    exact this
  · intro h x
    have := h (g⁻¹ * x * g)
    simp only [mem_map_conj_iff]
    have e2 : (g⁻¹ * y * g) * (g⁻¹ * x * g) * (g⁻¹ * y * g)⁻¹ = g⁻¹ * (y * x * y⁻¹) * g := by
      group
    rw [e2] at this
    exact this

end Conj

section Shape

variable {X : Type} [Group X] [Finite X] {t : X} {A : Subgroup X} {m : ℕ}

omit [Finite X] in
theorem mem_centralizer_of_exactShape (h : ExactShape t A m) : t ∈ centralizer (A : Set X) := by
  rw [mem_centralizer_iff]
  intro a ha
  exact mem_centralizer_singleton_iff.1 (h.le_cent ha)

end Shape

end CFSG.OddStandard.AltStdSec
