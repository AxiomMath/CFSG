module

public import CFSG.ClassicalInvolution.Q3.Q3TIYLarge
public import CFSG.ClassicalInvolution.Q3.Q3TIYSmall

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W

@[expose] def TwinRowNeedD3 (t : StatedLieTag) (n : ℕ) : Prop := t = .POmegaPlus ∧ n = 6

@[expose] def TwinRowNeedB3 (t : StatedLieTag) (n : ℕ) : Prop := t = .POmegaOdd ∧ 3 ≤ n

@[expose] def TwinRowNeedTD3 (t : StatedLieTag) (n : ℕ) : Prop :=
  t = .POmegaMinus ∧ (n = 4 ∨ n = 5)

@[expose] def TwinRowNeeded3 (t : StatedLieTag) (n : ℕ) : Prop :=
  TwinRowNeedD3 t n ∨ TwinRowNeedB3 t n ∨ TwinRowNeedTD3 t n

theorem TwinRowNeeded3.large_or_mid {t : StatedLieTag} {n : ℕ} (h : TwinRowNeeded3 t n) :
    TwinRowLarge3 t n ∨ TwinRowMid3 t n := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn | hn⟩
  · exact Or.inl (Or.inl ⟨rfl, by norm_num⟩)
  · by_cases h4 : 4 ≤ n
    · exact Or.inl (Or.inr (Or.inr ⟨rfl, h4⟩))
    · exact Or.inr (Or.inl ⟨rfl, by omega⟩)
  · subst hn
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · subst hn
    exact Or.inl (Or.inr (Or.inl ⟨rfl, le_rfl⟩))

theorem twinYType3On_needed_of_noCentral (h3 : OddThreeFreeInput)
    (hNC : TwinYNoCentral3On TwinRowMid3) : Q3TY.TwinYType3On TwinRowNeeded3 :=
  twinYType3On_mono (P₁ := fun t n => TwinRowLarge3 t n ∨ TwinRowMid3 t n)
    (fun _ _ h => h.large_or_mid)
    (twinYType3On_union (twinYType3_of_odd3 h3) (twinYType3On_mid_of_noCentral h3 hNC))

theorem twinYType3On_needed_B (h : Q3TY.TwinYType3On TwinRowNeeded3) :
    Q3TY.TwinYType3On TwinRowNeedB3 :=
  twinYType3On_mono (fun _ _ h => Or.inr (Or.inl h)) h

theorem twinYType3On_needed_TD (h : Q3TY.TwinYType3On TwinRowNeeded3) :
    Q3TY.TwinYType3On TwinRowNeedTD3 :=
  twinYType3On_mono (fun _ _ h => Or.inr (Or.inr h)) h

theorem twinYType3On_needed_D_of_odd3 (h3 : OddThreeFreeInput) :
    Q3TY.TwinYType3On TwinRowNeedD3 :=
  twinYType3On_mono (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact Or.inl ⟨rfl, by norm_num⟩)
    (twinYType3_of_odd3 h3)

end CFSG.ClassicalInvolution.Q3.Q3TIY
