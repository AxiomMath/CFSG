module

public import CFSG.ClassicalInvolution.Asc77.AscC25X4

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD

namespace C25X

variable (p : ℕ) [Fact p.Prime]

@[expose] def NC4SL : Prop :=
  ∀ e : ℕ, StatedLieAdmissible .PSL 4 p e → p ≠ 2 → 5 ≤ p ^ e → p ^ e % 4 = 1 →
    NC4At p .PSL 4 e

@[expose] def NC4SU : Prop :=
  ∀ e : ℕ, StatedLieAdmissible .PSU 4 p e → p ≠ 2 → 5 ≤ p ^ e → p ^ e % 4 = 3 →
    NC4At p .PSU 4 e

@[expose] def NC4Spin7 : Prop :=
  ∀ e : ℕ, StatedLieAdmissible .POmegaOdd 3 p e → p ≠ 2 → 5 ≤ p ^ e →
    NC4At p .POmegaOdd 3 e

@[expose] def NC4D4P : Prop :=
  ∀ e : ℕ, StatedLieAdmissible .POmegaPlus 4 p e → p ≠ 2 → 5 ≤ p ^ e →
    NC4At p .POmegaPlus 4 e

@[expose] def NC4D4M : Prop :=
  ∀ e : ℕ, StatedLieAdmissible .POmegaMinus 4 p e → p ≠ 2 → 5 ≤ p ^ e →
    NC4At p .POmegaMinus 4 e

variable {p}

theorem nc4Fact_of_rows (hsl : NC4SL p) (hsu : NC4SU p) (h7 : NC4Spin7 p) (hdp : NC4D4P p)
    (hdm : NC4D4M p) : NC4Fact p := by
  intro t k e hadm hp2 hq hcase
  rcases hcase with ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hsl e hadm hp2 hq h
  · exact hsu e hadm hp2 hq h
  · exact h7 e hadm hp2 hq
  · exact hdp e hadm hp2 hq
  · exact hdm e hadm hp2 hq

end C25X

end CFSG.ClassicalInvolution.Asc77
