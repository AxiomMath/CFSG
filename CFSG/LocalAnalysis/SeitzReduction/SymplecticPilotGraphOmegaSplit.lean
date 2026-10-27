module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotMainInputs

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank

@[expose] def SpGraphRowInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, RootKindSp e t f k κ) → False

@[expose] def SpLinearEvenRowInput : Prop := SpGraphRowInput .linearEven

@[expose] def SpUnitaryEvenRowInput : Prop := SpGraphRowInput .unitaryEven

@[expose] def SpLinearOddRowInput : Prop := SpGraphRowInput .linearOdd

@[expose] def SpUnitaryOddRowInput : Prop := SpGraphRowInput .unitaryOdd

@[expose] def SpOmegaPlusRowInput : Prop := SpGraphRowInput .omegaPlus

@[expose] def SpOmegaMinusRowInput : Prop := SpGraphRowInput .omegaMinus

theorem spGraphRowsInput_of_rows (hLE : SpLinearEvenRowInput) (hUE : SpUnitaryEvenRowInput)
    (hLO : SpLinearOddRowInput) (hUO : SpUnitaryOddRowInput) (hOP : SpOmegaPlusRowInput)
    (hOM : SpOmegaMinusRowInput) : SpGraphRowsInput := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt κ hκf hκs hκ
  cases κ with
  | field => exact hκf rfl
  | swap => exact hκs rfl
  | linearEven => exact hLE G L hset n f K hn hKc hf e t ht hKt hκ
  | unitaryEven => exact hUE G L hset n f K hn hKc hf e t ht hKt hκ
  | linearOdd => exact hLO G L hset n f K hn hKc hf e t ht hKt hκ
  | unitaryOdd => exact hUO G L hset n f K hn hKc hf e t ht hKt hκ
  | omegaPlus => exact hOP G L hset n f K hn hKc hf e t ht hKt hκ
  | omegaMinus => exact hOM G L hset n f K hn hKc hf e t ht hKt hκ

theorem spGraphRowInput_of_spGraphRowsInput (h : SpGraphRowsInput) {κ : Sp2mKind}
    (hκf : κ ≠ .field) (hκs : κ ≠ .swap) : SpGraphRowInput κ :=
  fun G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hκ =>
    h G L hset n f K hn hKc hf e t ht hKt κ hκf hκs hκ

theorem spGraphRowsInput_iff : SpGraphRowsInput ↔
    SpLinearEvenRowInput ∧ SpUnitaryEvenRowInput ∧ SpLinearOddRowInput ∧
      SpUnitaryOddRowInput ∧ SpOmegaPlusRowInput ∧ SpOmegaMinusRowInput := by
  constructor
  · intro h
    exact ⟨spGraphRowInput_of_spGraphRowsInput h (by decide) (by decide),
      spGraphRowInput_of_spGraphRowsInput h (by decide) (by decide),
      spGraphRowInput_of_spGraphRowsInput h (by decide) (by decide),
      spGraphRowInput_of_spGraphRowsInput h (by decide) (by decide),
      spGraphRowInput_of_spGraphRowsInput h (by decide) (by decide),
      spGraphRowInput_of_spGraphRowsInput h (by decide) (by decide)⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact spGraphRowsInput_of_rows h1 h2 h3 h4 h5 h6

end CFSG.SeitzReduction.SymplecticPilot
