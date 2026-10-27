module

public import Mathlib.GroupTheory.Complement

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise QuotientGroup

variable {G : Type*} [Group G] {A : Subgroup G} [A.Normal]

noncomputable def normalizedSection (A : Subgroup G) [A.Normal] (x : G ⧸ A) : G :=
  x.out * ((1 : G ⧸ A).out)⁻¹

@[simp]
theorem mk_normalizedSection (A : Subgroup G) [A.Normal] (x : G ⧸ A) :
    ((normalizedSection A x : G) : G ⧸ A) = x := by
  simp [normalizedSection]

@[simp]
theorem normalizedSection_one (A : Subgroup G) [A.Normal] :
    normalizedSection A (1 : G ⧸ A) = 1 := by
  simp [normalizedSection]

theorem normalizedSection_injective (A : Subgroup G) [A.Normal] :
    Function.Injective (normalizedSection A) := fun x y h => by
  rw [← mk_normalizedSection A x, ← mk_normalizedSection A y, h]

theorem exists_normalizedSection (A : Subgroup G) [A.Normal] :
    ∃ s : G ⧸ A → G, s 1 = 1 ∧ ∀ x, ((s x : G) : G ⧸ A) = x :=
  ⟨normalizedSection A, normalizedSection_one A, mk_normalizedSection A⟩

omit [A.Normal] in
theorem section_smul_coe (A : Subgroup G) {s : G ⧸ A → G} (hs : ∀ x, ((s x : G) : G ⧸ A) = x)
    (x : G ⧸ A) : s x • (A : Set G) = {g : G | (g : G ⧸ A) = x} := by
  conv_rhs => rw [← hs x]
  rw [← QuotientGroup.eq_class_eq_leftCoset]

theorem existsUnique_of_section {s : G ⧸ A → G} (hs : ∀ x, ((s x : G) : G ⧸ A) = x) (g : G) :
    ∃! p : A × (G ⧸ A), g = (p.1 : G) * s p.2 := by
  refine ⟨⟨⟨g * (s (g : G ⧸ A))⁻¹, ?_⟩, (g : G ⧸ A)⟩, by simp, ?_⟩
  · rw [← QuotientGroup.eq_one_iff]
    simp [hs]
  · rintro ⟨⟨a, ha⟩, x⟩ h
    simp only at h
    have hx : x = (g : G ⧸ A) := by
      rw [h, QuotientGroup.mk_mul, hs, (QuotientGroup.eq_one_iff a).2 ha, one_mul]
    subst hx
    have ha' : a = g * (s (g : G ⧸ A))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      exact h.symm
    simp [ha']

theorem existsUnique_mul_normalizedSection (A : Subgroup G) [A.Normal] (g : G) :
    ∃! p : A × (G ⧸ A), g = (p.1 : G) * normalizedSection A p.2 :=
  existsUnique_of_section (mk_normalizedSection A) g

theorem isComplement_range_of_section {s : G ⧸ A → G} (hs : ∀ x, ((s x : G) : G ⧸ A) = x) :
    Subgroup.IsComplement (A : Set G) (Set.range s) := by
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨-, x, rfl⟩⟩ ⟨⟨b, hb⟩, ⟨-, y, rfl⟩⟩ h
    simp only at h
    have hxy : x = y := by
      have := congrArg (QuotientGroup.mk (s := A)) h
      simpa [hs, (QuotientGroup.eq_one_iff a).2 ha, (QuotientGroup.eq_one_iff b).2 hb] using this
    subst hxy
    have : a = b := by simpa using h
    simp [this]
  · intro g
    obtain ⟨p, hp, -⟩ := existsUnique_of_section hs g
    exact ⟨⟨p.1, ⟨s p.2, p.2, rfl⟩⟩, hp.symm⟩

end CFSG.FeitThompson
