module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.Phan.PhanQ9KGeo

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin

section Wedge2

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem exists_parallel_of_wedge_zero {X Y : Fin 4 → K} (h : ∀ i j, X i * Y j - X j * Y i = 0) :
    ∃ l m : K, (l ≠ 0 ∨ m ≠ 0) ∧ ∀ i, l * X i + m * Y i = 0 := by
  by_cases hX : ∀ i, X i = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, fun i => by simp [hX i]⟩
  · obtain ⟨i, hi⟩ := not_forall.1 hX
    refine ⟨Y i, -X i, Or.inr (neg_ne_zero.2 hi), fun j => ?_⟩
    have := h i j
    linear_combination -this

end Wedge2

end CFSG.ClassicalInvolution.PhanQ
