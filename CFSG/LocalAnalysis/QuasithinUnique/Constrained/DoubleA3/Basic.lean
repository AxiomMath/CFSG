module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Defs

public section

namespace CFSG.QuasithinUnique.DoubleA3

variable {G : Type*} [Group G]

theorem mem_conjR {X : Subgroup G} {g y : G} : y ∈ conjR X g ↔ g * y * g⁻¹ ∈ X := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have e : g * ((MulAut.conj g⁻¹).toMonoidHom a) * g⁻¹ = a := by
      simp; group
    rw [e]; exact ha
  · intro h
    exact ⟨g * y * g⁻¹, h, by simp [mul_assoc]⟩

theorem conj_mem_conjClass {z y : G} (h : y ∈ conjClass z) (g : G) :
    g⁻¹ * y * g ∈ conjClass z := by
  obtain ⟨h, rfl⟩ := h
  exact ⟨h * g, by simp [mul_assoc]⟩

theorem image_conj_eq {s z₂ : G} (B : Subgroup G) :
    ((fun y : G => s⁻¹ * y * s) '' {y | y ∈ conjClass z₂ ∧ y ∈ B}) =
      {y | y ∈ conjClass z₂ ∧ y ∈ conjR B s} := by
  ext y
  simp only [Set.mem_image, mem_conjR]
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    exact ⟨conj_mem_conjClass hx1 s, by simpa [mul_assoc] using hx2⟩
  · rintro ⟨hy1, hy2⟩
    refine ⟨s * y * s⁻¹, ⟨?_, hy2⟩, by simp [mul_assoc]⟩
    simpa using conj_mem_conjClass hy1 s⁻¹

end CFSG.QuasithinUnique.DoubleA3
