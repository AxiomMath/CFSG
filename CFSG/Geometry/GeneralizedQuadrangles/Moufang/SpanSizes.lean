module

public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.Transitive
public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.Symmetries
public import CFSG.Geometry.GeneralizedQuadrangles.Trichotomy.Closure3

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons CFSG.Quasithin CFSG.Quasithin.Stroth

variable {V : Type} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem exists_ncard_spanSet_eq {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (hM : MoufangCondition H Γ 4)
    (c : Γ.Coloring (Fin 2)) (i : Fin 2) :
    ∃ p : ℕ, ∀ x y, c x = i → Γ.dist x y = 4 → (spanSet Γ x y).ncard = p + 1 := by
  by_cases h : ∃ x₀ y₀, c x₀ = i ∧ Γ.dist x₀ y₀ = 4
  · obtain ⟨x₀, y₀, hx₀, h₀⟩ := h
    have hne : x₀ ≠ y₀ := by
      rintro rfl
      simp at h₀
    have h2 : 2 ≤ (spanSet Γ x₀ y₀).ncard := by
      rw [← Set.ncard_pair hne]
      exact Set.ncard_le_ncard (Set.insert_subset (left_mem_spanSet h₀)
        (Set.singleton_subset_iff.mpr (right_mem_spanSet h₀))) (Set.toFinite _)
    refine ⟨(spanSet Γ x₀ y₀).ncard - 1, fun x y hx hxy => ?_⟩
    rw [ncard_spanSet_eq_of_color_eq hP hT hM c hxy h₀ (hx.trans hx₀.symm)]
    omega
  · exact ⟨0, fun x y hx hxy => absurd ⟨x, y, hx, hxy⟩ h⟩

theorem trichotomy_dual (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hH : ∀ u : V, c u = 1 → HasPropertyH Γ u) {p : ℕ}
    (hp : ∀ L M : V, c L = 1 → Γ.dist L M = 4 → (spanSet Γ L M).ncard = p + 1) :
    p = s ∨ p = 1 ∨ (t = p ^ 2 ∧ s = p ^ 3) := by
  have hdual : ∀ v, dualColoring c v = 0 ↔ c v = 1 := by
    intro v
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rw [dualColoring_apply]
    rcases hfin (c v) with hv | hv <;> rw [hv] <;> decide
  exact trichotomy hP hT (dualColoring c) (degree_eq_of_dualColoring hdeg)
    (fun u hu => hH u ((hdual u).1 hu)) (fun L M hL hLM => hp L M ((hdual L).1 hL) hLM)

end CFSG.Geometry.GeneralizedQuadrangles

end
