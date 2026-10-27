module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.FourMinus
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Bridge
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallCases

public section

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

variable {K : Type} [Field K] [IsF2 K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem isSimpleGroup_elementaryGroup_of_isometry_plus {m : ℕ} (hm : 3 ≤ m)
    (φ : V ≃ₗ[K] (Fin m ⊕ Fin m → K)) (hφ : ∀ v, quadPlus m K (φ v) = Q v) :
    IsSimpleGroup (elementaryGroup Q) := by
  obtain ⟨hfd, hd, hnd⟩ := isometry_plus_facts φ hφ
  exact isSimpleGroup_elementaryGroup_of_six_le_finrank hnd (by omega)

theorem isSimpleGroup_elementaryGroup_of_isometry_minus {m : ℕ} (hm : 2 ≤ m)
    (φ : V ≃ₗ[K] (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K))
    (hφ : ∀ v, quadMinus m K 1 1 (φ v) = Q v) :
    IsSimpleGroup (elementaryGroup Q) := by
  obtain ⟨hfd, hd, hnd⟩ := isometry_minus_facts (m := m) (by omega) φ hφ
  by_cases h3 : 3 ≤ m
  · exact isSimpleGroup_elementaryGroup_of_six_le_finrank hnd (by omega)
  · obtain rfl : m = 2 := by omega
    exact isSimpleGroup_elementaryGroup_of_four hnd (by omega)
      (not_exists_totallySingular_plane_of_isometry φ hφ
        not_exists_totallySingular_plane_quadMinus_two)

section ZModTwo

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] {Q' : QuadraticForm (ZMod 2) W}

theorem isSimpleGroup_elementaryGroup_of_isPlusSpace {m : ℕ} (hm : 3 ≤ m)
    (h : IsPlusSpace Q' m) : IsSimpleGroup (elementaryGroup Q') := by
  obtain ⟨φ, hφ⟩ := h
  exact isSimpleGroup_elementaryGroup_of_isometry_plus hm φ hφ

theorem isSimpleGroup_elementaryGroup_of_isMinusSpace {m : ℕ} (hm : 2 ≤ m)
    (h : IsMinusSpace Q' m) : IsSimpleGroup (elementaryGroup Q') := by
  obtain ⟨φ, hφ⟩ := h
  exact isSimpleGroup_elementaryGroup_of_isometry_minus hm φ hφ

end ZModTwo

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
