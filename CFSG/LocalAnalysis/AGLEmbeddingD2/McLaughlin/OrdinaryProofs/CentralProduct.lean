module

public import CFSG.Assembly.Defs

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open Subgroup
open scoped commutatorElement

theorem exists_mul_of_mem_sup {G : Type*} [Group G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let K : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [h a' ha' b hb]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have hc : (b⁻¹ * a⁻¹ : G) = a⁻¹ * b⁻¹ := by
          have := congrArg (fun g : G => g⁻¹) (h a ha b hb)
          simpa only [mul_inv_rev] using this
        rw [mul_inv_rev, hc] }
  have hsub : A ⊔ B ≤ K :=
    sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
      (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  obtain ⟨a, ha, b, hb, hxab⟩ := hsub hx
  exact ⟨a, ha, b, hb, hxab⟩

end CFSG.AGLEmbeddingD2.McLaughlin
