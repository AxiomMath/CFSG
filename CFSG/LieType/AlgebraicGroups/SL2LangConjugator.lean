module

public import CFSG.LieType.AlgebraicGroups.SL2FrobeniusLang

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

theorem exists_fixed_conjugator_of_sl2_centralizer
    {G k : Type} [Group G] [Field k] [IsAlgClosed k] (p f : ℕ)
    [Fact p.Prime] [CharP k p] (hf : 1 ≤ f) (F : G →* G)
    (ρ : Matrix.SpecialLinearGroup (Fin 2) k →* G)
    (hρF : ∀ Y, F (ρ Y) = ρ (Matrix.SpecialLinearGroup.map (iterateFrobenius k p f) Y))
    (H : Subgroup G) (hρC : ρ.range ≤ Subgroup.centralizer (H : Set G))
    (a : G) (ha : a⁻¹ * F a ∈ ρ.range) :
    ∃ b : G, F b = b ∧ (∀ g ∈ H, b * g * b⁻¹ = a * g * a⁻¹) ∧
      ∃ Y : Matrix.SpecialLinearGroup (Fin 2) k, b = a * (ρ Y)⁻¹ := by
  obtain ⟨X, hX⟩ := ha
  obtain ⟨Y, hY⟩ := sl2_frobenius_lang p f hf X
  let t := ρ Y
  have htC : t ∈ Subgroup.centralizer (H : Set G) := hρC ⟨Y, rfl⟩
  have htLang : t⁻¹ * F t = a⁻¹ * F a := by
    change (ρ Y)⁻¹ * F (ρ Y) = a⁻¹ * F a
    rw [hρF, ← map_inv, ← map_mul, ← hY, hX]
  have htF : F t = t * (a⁻¹ * F a) := by
    rw [← htLang]
    group
  refine ⟨a * t⁻¹, ?_, ?_, Y, rfl⟩
  · rw [map_mul, map_inv, htF]
    group
  · intro g hg
    have hcomm : t * g = g * t := (Subgroup.mem_centralizer_iff.mp htC g hg).symm
    have hfix : t⁻¹ * g * t = g := by
      calc
        t⁻¹ * g * t = t⁻¹ * (t * g) := by rw [hcomm]; group
        _ = g := by group
    calc
      (a * t⁻¹) * g * (a * t⁻¹)⁻¹ = a * (t⁻¹ * g * t) * a⁻¹ := by group
      _ = a * g * a⁻¹ := by rw [hfix]

end CFSG.LieType.AlgebraicGroups
