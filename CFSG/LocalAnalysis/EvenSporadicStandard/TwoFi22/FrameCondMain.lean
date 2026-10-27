module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameCondOdd
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameCondPairs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameCondTransitive

public section

namespace CFSG.EvenSporadicStandard.TwoFi22

open CFSG.Fischer

theorem sylow_conditions_of_frame {G : Type} [Group G] [Finite G] {D : Set G}
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (_hD2 : ∀ x ∈ D, orderOf x = 2)
    (T : Sylow 2 G) (F : GoodFrame G) (hΩ : (T : Set G) ∩ D = Set.range F.pt) :
    (∀ x ∈ Subgroup.closure ((T : Set G) ∩ D), ∀ y ∈ Subgroup.closure ((T : Set G) ∩ D),
      x * y = y * x) ∧
    (Subgroup.closure ((T : Set G) ∩ D) =
      Subgroup.closure {x | ∃ a ∈ (T : Set G) ∩ D, ∃ b ∈ (T : Set G) ∩ D, a * b = x}) ∧
    (∀ a ∈ (T : Set G) ∩ D, ∀ b ∈ (T : Set G) ∩ D, ∀ a' ∈ (T : Set G) ∩ D,
      ∀ b' ∈ (T : Set G) ∩ D, a ≠ b → a' ≠ b' → a * b = a' * b' →
        (a = a' ∧ b = b') ∨ (a = b' ∧ b = a')) ∧
    ({x | x ∈ Subgroup.closure ((T : Set G) ∩ D) ∧ x ≠ 1} ≠ (T : Set G) ∩ D) ∧
    (∀ a ∈ (T : Set G) ∩ D, ∀ b ∈ (T : Set G) ∩ D, ∀ c ∈ (T : Set G) ∩ D,
      ¬ ∀ e ∈ (T : Set G) ∩ D, ∀ f ∈ (T : Set G) ∩ D,
        ∃ g ∈ Subgroup.normalizer ((T : Set G) ∩ D) ⊓ Subgroup.centralizer {a * b * c},
          g * e * g⁻¹ = f) ∧
    (∀ Δ : (commGraph D).ConnectedComponent,
      ∀ x ∈ Subgroup.normalizer (Subtype.val '' Δ.supp), orderOf x = 2 →
        ∃ f ∈ Subtype.val '' Δ.supp, x * f * x⁻¹ = f) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hΩ]
    exact fun x hx y hy => F.commute_of_mem_closure hx hy
  · rw [hΩ]
    exact F.closure_range_pt_eq
  · rw [hΩ]
    exact F.pair_inj
  · rw [hΩ]
    exact F.closure_ne_range
  · rw [hΩ]
    exact F.not_transitive
  · refine fixed_of_component_of_odd hclass T ?_ ?_
    · rw [hΩ]
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact F.pt_comm i j
    · rw [hΩ, F.ncard_range_pt]
      exact ⟨11, rfl⟩

end CFSG.EvenSporadicStandard.TwoFi22
