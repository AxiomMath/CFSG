module

public import CFSG.ClassicalInvolution.Asc77.AscT7JSq

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Generic


structure TwinSqRows3 : Prop where
  psp : StatedLieAdmissible .PSp 2 3 1 → TwinSqAlpha 3 1 .PSp 2
  psl : StatedLieAdmissible .PSL 4 3 1 → TwinSqAlpha 3 1 .PSL 4
  psu : StatedLieAdmissible .PSU 4 3 1 → TwinSqAlpha 3 1 .PSU 4
  odd : ∀ n, 3 ≤ n → StatedLieAdmissible .POmegaOdd n 3 1 → TwinSqAlpha 3 1 .POmegaOdd n
  plus : ∀ n, 4 ≤ n → StatedLieAdmissible .POmegaPlus n 3 1 → TwinSqAlpha 3 1 .POmegaPlus n
  minus : ∀ n, 4 ≤ n → StatedLieAdmissible .POmegaMinus n 3 1 → TwinSqAlpha 3 1 .POmegaMinus n

theorem twinSqAlphaRows3_of_rows (h : TwinSqRows3) :
    ∀ (t : StatedLieTag) (n : ℕ), StatedLieAdmissible t n 3 1 → TwinShape t n →
      TwinSqAlpha 3 1 t n := by
  intro t n hadm hsh
  rcases hsh with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h.odd n hn hadm
  · exact h.plus n hn hadm
  · exact h.minus n hn hadm
  · exact h.psp hadm
  · exact h.psl hadm
  · exact h.psu hadm

structure TwinOuterRows3 : Prop where
  psp : StatedLieAdmissible .PSp 2 3 1 → TwinOuterAlpha 3 1 .PSp 2
  psl : StatedLieAdmissible .PSL 4 3 1 → TwinOuterAlpha 3 1 .PSL 4
  psu : StatedLieAdmissible .PSU 4 3 1 → TwinOuterAlpha 3 1 .PSU 4
  odd : ∀ n, 3 ≤ n → StatedLieAdmissible .POmegaOdd n 3 1 → TwinOuterAlpha 3 1 .POmegaOdd n
  plus : ∀ n, 4 ≤ n → StatedLieAdmissible .POmegaPlus n 3 1 → TwinOuterAlpha 3 1 .POmegaPlus n
  minus : ∀ n, 4 ≤ n → StatedLieAdmissible .POmegaMinus n 3 1 → TwinOuterAlpha 3 1 .POmegaMinus n

theorem twinOuterAlphaRows3_of_rows (h : TwinOuterRows3) :
    ∀ (t : StatedLieTag) (n : ℕ), StatedLieAdmissible t n 3 1 → TwinShape t n →
      TwinOuterAlpha 3 1 t n := by
  intro t n hadm hsh
  rcases hsh with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h.odd n hn hadm
  · exact h.plus n hn hadm
  · exact h.minus n hn hadm
  · exact h.psp hadm
  · exact h.psl hadm
  · exact h.psu hadm

@[expose] def TwinSqAlphaAll3 : Prop :=
  ∀ (t : StatedLieTag) (n : ℕ), IsFundTag t → StatedLieAdmissible t n 3 1 → TwinSqAlpha 3 1 t n

@[expose] def TwinOuterAlphaAll3 : Prop :=
  ∀ (t : StatedLieTag) (n : ℕ), IsFundTag t → StatedLieAdmissible t n 3 1 → TwinOuterAlpha 3 1 t n

end CFSG.ClassicalInvolution.Q3.Q3T7
