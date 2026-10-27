module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinT

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank

variable (p : ℕ) [Fact p.Prime]

@[expose] def TwinSmallInnerSp : Prop :=
  p ≠ 2 → ∀ e, 5 ≤ p ^ e → StatedLieAdmissible .PSp 2 p e → TwinInnerAlpha p e .PSp 2

@[expose] def TwinSmallInnerSL : Prop :=
  p ≠ 2 → ∀ e, 5 ≤ p ^ e → StatedLieAdmissible .PSL 4 p e → TwinInnerAlpha p e .PSL 4

@[expose] def TwinSmallInnerSU : Prop :=
  p ≠ 2 → ∀ e, 5 ≤ p ^ e → StatedLieAdmissible .PSU 4 p e → TwinInnerAlpha p e .PSU 4

@[expose] def TwinSmallInnerD4 : Prop :=
  p ≠ 2 → ∀ e, 5 ≤ p ^ e → StatedLieAdmissible .POmegaPlus 4 p e →
    TwinInnerAlpha p e .POmegaPlus 4

theorem twinSmallInner_of_rows {p : ℕ} [Fact p.Prime] (hsp : TwinSmallInnerSp p)
    (hsl : TwinSmallInnerSL p) (hsu : TwinSmallInnerSU p) (hd4 : TwinSmallInnerD4 p) :
    TwinSmallInner p :=
  ⟨hsp, hsl, hsu, hd4⟩

theorem twinSmallInner_iff_rows {p : ℕ} [Fact p.Prime] :
    TwinSmallInner p ↔
      TwinSmallInnerSp p ∧ TwinSmallInnerSL p ∧ TwinSmallInnerSU p ∧ TwinSmallInnerD4 p :=
  ⟨fun h => ⟨h.psp, h.psl, h.psu, h.d4⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

@[expose] def TwinSmallOuterSp : Prop :=
  p ≠ 2 → ∀ e, 5 ≤ p ^ e → StatedLieAdmissible .PSp 2 p e → TwinOuterAlpha p e .PSp 2

@[expose] def TwinSmallOuterSL : Prop :=
  p ≠ 2 → ∀ e, 5 ≤ p ^ e → StatedLieAdmissible .PSL 4 p e → TwinOuterAlpha p e .PSL 4

@[expose] def TwinSmallOuterSU : Prop :=
  p ≠ 2 → ∀ e, 5 ≤ p ^ e → StatedLieAdmissible .PSU 4 p e → TwinOuterAlpha p e .PSU 4

@[expose] def TwinSmallOuterD4 : Prop :=
  p ≠ 2 → ∀ e, 5 ≤ p ^ e → StatedLieAdmissible .POmegaPlus 4 p e →
    TwinOuterAlpha p e .POmegaPlus 4

theorem twinSmallOuter_of_rows {p : ℕ} [Fact p.Prime] (hsp : TwinSmallOuterSp p)
    (hsl : TwinSmallOuterSL p) (hsu : TwinSmallOuterSU p) (hd4 : TwinSmallOuterD4 p) :
    TwinSmallOuter p :=
  ⟨hsp, hsl, hsu, hd4⟩

theorem twinSmallOuter_iff_rows {p : ℕ} [Fact p.Prime] :
    TwinSmallOuter p ↔
      TwinSmallOuterSp p ∧ TwinSmallOuterSL p ∧ TwinSmallOuterSU p ∧ TwinSmallOuterD4 p :=
  ⟨fun h => ⟨h.psp, h.psl, h.psu, h.d4⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

end CFSG.ClassicalInvolution.Asc77
