module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.EvenSporadicStandard.Fin76b

@[expose] def ElAb16 (Γ : Type*) [Group Γ] : Prop :=
  ∀ A : Subgroup Γ, (∀ a ∈ A, a * a = 1) → Nat.card ↥A ≤ 16

theorem ElAb16.of_mulEquiv {Γ Δ : Type*} [Group Γ] [Group Δ] (e : Γ ≃* Δ) (h : ElAb16 Δ) :
    ElAb16 Γ := by
  intro A hA
  have hB : ∀ b ∈ A.map e.toMonoidHom, b * b = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hA a ha, map_one]
  have hc : Nat.card ↥(A.map e.toMonoidHom) = Nat.card ↥A :=
    Subgroup.card_map_of_injective e.injective
  rw [← hc]
  exact h _ hB

theorem ea16_isPGroup_two {H : Type*} [Group H] {K : Subgroup H} (hK : ∀ a ∈ K, a * a = 1) :
    IsPGroup 2 K := by
  intro a
  exact ⟨1, Subtype.ext (by simpa [pow_two] using hK a a.2)⟩

end CFSG.EvenSporadicStandard.Fin76b
