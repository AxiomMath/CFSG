module

public import CFSG.ClassicalInvolution.Asc77.AscT7L6

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD

variable (p : ℕ) [Fact p.Prime]

@[expose] def TwinCentralAt (t : StatedLieTag) (k e : ℕ) : Prop :=
  ∀ R ∈ ModelFund p t k e, ∀ R' ∈ ModelFund p t k e, R ≠ R' → Commutes R R' →
    ∀ x ∈ R, x * x = 1 → x ≠ 1 → ∀ x' ∈ R', x' * x' = 1 → x' ≠ 1 →
      x * x' ∈ Subgroup.center (modelUniv t k p e Fact.out).K →
      ∀ a ∈ R, a * a = x → ∀ b ∈ R', b * b = x' →
        ∃ R'' ∈ ModelFund p t k e, ∀ r ∈ R'', (a * b) * r = r * (a * b)

@[expose] def TwinCentralSL : Prop :=
  ∀ e : ℕ, StatedLieAdmissible .PSL 4 p e → p ≠ 2 → 5 ≤ p ^ e → p ^ e % 4 = 1 →
    TwinCentralAt p .PSL 4 e

@[expose] def TwinCentralSU : Prop :=
  ∀ e : ℕ, StatedLieAdmissible .PSU 4 p e → p ≠ 2 → 5 ≤ p ^ e → p ^ e % 4 = 3 →
    TwinCentralAt p .PSU 4 e

@[expose] def TwinCentralSpin7 : Prop :=
  ∀ e : ℕ, StatedLieAdmissible .POmegaOdd 3 p e → p ≠ 2 → 5 ≤ p ^ e →
    TwinCentralAt p .POmegaOdd 3 e

@[expose] def TwinCentralD4P : Prop :=
  ∀ e : ℕ, StatedLieAdmissible .POmegaPlus 4 p e → p ≠ 2 → 5 ≤ p ^ e →
    TwinCentralAt p .POmegaPlus 4 e

@[expose] def TwinCentralD4M : Prop :=
  ∀ e : ℕ, StatedLieAdmissible .POmegaMinus 4 p e → p ≠ 2 → 5 ≤ p ^ e →
    TwinCentralAt p .POmegaMinus 4 e

variable {p}

theorem twinCentralFact_of_rows (hsl : TwinCentralSL p) (hsu : TwinCentralSU p)
    (h7 : TwinCentralSpin7 p) (hdp : TwinCentralD4P p) (hdm : TwinCentralD4M p) :
    TwinCentralFact p := by
  intro t k e hadm hp2 hq hcase
  rcases hcase with ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hsl e hadm hp2 hq h
  · exact hsu e hadm hp2 hq h
  · exact h7 e hadm hp2 hq
  · exact hdp e hadm hp2 hq
  · exact hdm e hadm hp2 hq

variable (p)

@[expose] def E4GenAt (t : StatedLieTag) (k e : ℕ) : Prop :=
  ∀ R ∈ ModelFund p t k e, ∀ R' ∈ ModelFund p t k e, R ≠ R' → Commutes R R' →
    ∀ x ∈ R, x * x = 1 → x ≠ 1 → ∀ x' ∈ R', x' * x' = 1 → x' ≠ 1 →
      x * x' ∈ Subgroup.center (modelUniv t k p e Fact.out).K →
      ∀ a ∈ R, a * a = x → ∀ b ∈ R', b * b = x' →
        (⊤ : Subgroup (modelUniv t k p e Fact.out).K) =
          Subgroup.center (modelUniv t k p e Fact.out).K ⊔
            (Subgroup.centralizer ({x} : Set (modelUniv t k p e Fact.out).K) ⊔
              Subgroup.centralizer ({a * b} : Set (modelUniv t k p e Fact.out).K) ⊔
              Subgroup.centralizer ({a⁻¹ * b} : Set (modelUniv t k p e Fact.out).K))

@[expose] def E4GenSp : Prop :=
  ∀ e : ℕ, StatedLieAdmissible .PSp 2 p e → p ≠ 2 → 5 ≤ p ^ e → E4GenAt p .PSp 2 e

@[expose] def E4GenSL : Prop :=
  ∀ e : ℕ, StatedLieAdmissible .PSL 4 p e → p ≠ 2 → 5 ≤ p ^ e → p ^ e % 4 = 3 →
    E4GenAt p .PSL 4 e

@[expose] def E4GenSU : Prop :=
  ∀ e : ℕ, StatedLieAdmissible .PSU 4 p e → p ≠ 2 → 5 ≤ p ^ e → p ^ e % 4 = 1 →
    E4GenAt p .PSU 4 e

variable {p}

theorem e4TwinGen_of_rows (hsp : E4GenSp p) (hsl : E4GenSL p) (hsu : E4GenSU p) :
    E4TwinGen p := by
  intro t k e hadm hp2 hq hcase
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩
  · exact hsp e hadm hp2 hq
  · exact hsl e hadm hp2 hq h
  · exact hsu e hadm hp2 hq h

end CFSG.ClassicalInvolution.Asc77
