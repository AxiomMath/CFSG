module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.CoordSpec
public import CFSG.Adapters.ProjectiveSpecialLinear

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction

set_option linter.unusedSectionVars false


variable (τ : Tag) (K : Type) [Field K]

@[expose] def heisCoord : ModGL τ K → (Fin τ.rank → ℤ) → K :=
  Classical.choose (exists_heisCoord τ K)

theorem heisCoord_spec : HeisCoordSpec τ K (heisCoord τ K) :=
  Classical.choose_spec (exists_heisCoord τ K)

variable {τ K}

theorem heisCoord_one : heisCoord τ K 1 = 0 := by
  have h := (heisCoord_spec τ K).mul 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at h
  exact left_eq_add.1 h |>.symm ▸ rfl

theorem heisCoord_inv {q : ModGL τ K} (hq : q ∈ Qθ τ K) : heisCoord τ K q⁻¹ = -heisCoord τ K q := by
  have h := (heisCoord_spec τ K).mul q hq q⁻¹ (inv_mem hq)
  rw [mul_inv_cancel, heisCoord_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
