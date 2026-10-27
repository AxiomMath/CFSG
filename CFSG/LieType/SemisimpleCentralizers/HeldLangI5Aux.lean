module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open scoped commutatorElement

variable {G : Type*} [Group G]

private theorem commutator_mul_central' {x y z₁ z₂ : G} (h1 : ∀ w, z₁ * w = w * z₁)
    (h2 : ∀ w, z₂ * w = w * z₂) : ⁅x * z₁, y * z₂⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc x * z₁ * (y * z₂) * (x * z₁)⁻¹ * (y * z₂)⁻¹
      = x * (z₁ * y) * z₂ * z₁⁻¹ * x⁻¹ * z₂⁻¹ * y⁻¹ := by group
    _ = x * (y * z₁) * z₂ * z₁⁻¹ * x⁻¹ * z₂⁻¹ * y⁻¹ := by rw [h1 y]
    _ = x * y * (z₁ * z₂) * z₁⁻¹ * x⁻¹ * z₂⁻¹ * y⁻¹ := by group
    _ = x * y * (z₂ * z₁) * z₁⁻¹ * x⁻¹ * z₂⁻¹ * y⁻¹ := by rw [h1 z₂]
    _ = x * y * z₂ * x⁻¹ * z₂⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * z₂) * z₂⁻¹ * y⁻¹ := by rw [← h2 x⁻¹]; group
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem eq_of_central_displacement [Group.IsPerfect G] (β ζ : G →* G)
    (h : ∀ x, (ζ x)⁻¹ * β x ∈ Subgroup.center G) : β = ζ := by
  have hβζ : ∀ x, β x = ζ x * ((ζ x)⁻¹ * β x) := fun x => by group
  have hcomm : ∀ x : G, ∀ z ∈ Subgroup.center G, ∀ w : G, z * w = w * z :=
    fun x z hz w => (Subgroup.mem_center_iff.1 hz w).symm
  have hle : commutator G ≤ MonoidHom.eqLocus β ζ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    show β ⁅a, b⁆ = ζ ⁅a, b⁆
    rw [map_commutatorElement, map_commutatorElement, hβζ a, hβζ b]
    exact commutator_mul_central' (hcomm a _ (h a)) (hcomm b _ (h b))
  have htop : commutator G = ⊤ := Group.IsPerfect.commutator_eq_top
  rw [htop] at hle
  ext x
  exact hle (Subgroup.mem_top x)

theorem isElemAbelian_map_of_injective {H : Type*} [Group H] {p : ℕ} (Φ : G →* H)
    {D : Subgroup G} (hD : CFSG.Open.IsElemAbelian p D) : CFSG.Open.IsElemAbelian p (D.map Φ) := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    show Φ a * Φ b = Φ b * Φ a
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hD.2 a ha, map_one]

end CFSG.LieType.SemisimpleCentralizers.HeldLang
