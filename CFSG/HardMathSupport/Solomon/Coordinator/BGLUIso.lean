module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUExist

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix CFSG.ClassicalGroups.Unitary

variable {K : Type*} [Field K] {ι ρ : K ≃+* K}

@[expose] def isoVec (u ω : K) : Fin 3 → Fin 3 → K := ![![1, u, 0], ![1, ω * u, 0], ![0, 1, u]]

theorem herm_isoVec (u ω : K) (k l : Fin 3) :
    herm ι (isoVec u ω k) (isoVec u ω l) =
      ι (isoVec u ω k 0) * isoVec u ω l 0 + ι (isoVec u ω k 1) * isoVec u ω l 1 +
        ι (isoVec u ω k 2) * isoVec u ω l 2 := by
  simp [herm, Fin.sum_univ_three]

theorem isoBasis_exists (hι : ∀ x, ι (ι x) = x)
    {u ω : K} (hρu : ρ u = u) (hρω : ρ ω = ω) (hu : ι u * u = -1) (hω : ι ω * ω = 1)
    (hω1 : ω ≠ 1) : Nonempty (IsoBasis ι ρ) := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  have hιu0 : ι u ≠ 0 := by
    intro h
    apply hu0
    rw [← hι u, h, map_zero]
  have hιω0 : ι ω ≠ 0 := by
    intro h
    apply hω0
    rw [← hι ω, h, map_zero]
  have hιω1 : ι ω ≠ 1 := by
    intro h
    apply hω1
    rw [← hι ω, h, map_one]
  have hω1' : 1 - ω ≠ 0 := sub_ne_zero.mpr (Ne.symm hω1)
  have hιω1' : 1 - ι ω ≠ 0 := sub_ne_zero.mpr (Ne.symm hιω1)
  have hD : u * (ω - 1) ≠ 0 := mul_ne_zero hu0 (sub_ne_zero.mpr hω1)
  refine ⟨⟨isoVec u ω, ?_, ?_, ?_, ?_⟩⟩
  · intro k i
    fin_cases k <;> fin_cases i <;> simp [isoVec, hρu, hρω, map_mul]
  · intro k
    fin_cases k
    · rw [herm_isoVec]; simp [isoVec, hu]
    · rw [herm_isoVec]
      simp only [isoVec]
      simp [map_mul]
      linear_combination (ι ω * ω) * hu + hω * (-1) + hω * 0
    · rw [herm_isoVec]; simp [isoVec, hu]
  · intro k l hkl
    fin_cases k <;> fin_cases l <;> first | exact absurd rfl hkl | skip
    all_goals rw [herm_isoVec]
    all_goals simp [isoVec, map_mul]
    · intro h
      apply hω1'
      linear_combination h - ω * hu
    · exact hu0
    · intro h
      apply hιω1'
      linear_combination h - ι ω * hu
    · exact ⟨hω0, hu0⟩
    · exact hu0
    · exact ⟨hω0, hu0⟩
  · intro j
    have hω1'' : ω - 1 ≠ 0 := sub_ne_zero.mpr hω1
    have hD' : u * (ω - 1) ≠ 0 := hD
    fin_cases j
    · refine ⟨![1 + 1 / (ω - 1), -(1 / (ω - 1)), 0], ?_, ?_⟩
      · intro k
        fin_cases k <;> simp [map_add, map_sub, hρω]
      · funext i
        fin_cases i
        all_goals simp [isoVec, Fin.sum_univ_three]
        all_goals field_simp
        all_goals ring
    · refine ⟨![-(1 / (u * (ω - 1))), 1 / (u * (ω - 1)), 0], ?_, ?_⟩
      · intro k
        fin_cases k <;> simp [map_sub, map_mul, hρω, hρu]
      · funext i
        fin_cases i
        all_goals simp [isoVec, Fin.sum_univ_three]
        all_goals field_simp
        all_goals ring
    · refine ⟨![u⁻¹ * (1 / (u * (ω - 1))), -(u⁻¹ * (1 / (u * (ω - 1)))), u⁻¹], ?_, ?_⟩
      · intro k
        fin_cases k <;> simp [map_sub, map_mul, hρω, hρu]
      · funext i
        fin_cases i
        all_goals simp [isoVec, Fin.sum_univ_three]
        all_goals field_simp
        all_goals ring

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
