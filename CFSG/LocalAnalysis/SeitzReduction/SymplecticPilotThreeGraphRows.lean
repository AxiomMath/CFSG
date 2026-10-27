module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank

section Void

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem not_rootKindSp_three_omegaPlus (e : L ≃* StatedSp 3 K) (t : G) (f : ℕ) (k : Fin 3) :
    ¬ RootKindSp e t f k .omegaPlus := by
  intro h
  obtain ⟨htX, Kc, -, -, h1 | h2⟩ := h
  · obtain ⟨-, -, -, -, -, -, hty⟩ := h1
    exact not_sp2mKindType_two_omegaPlus hty
  · exact absurd h2.1 (by decide)

theorem not_rootKindSp_three_omegaMinus (e : L ≃* StatedSp 3 K) (t : G) (f : ℕ) (k : Fin 3) :
    ¬ RootKindSp e t f k .omegaMinus := by
  intro h
  obtain ⟨htX, Kc, -, -, h1 | h2⟩ := h
  · obtain ⟨-, -, -, -, -, -, hty⟩ := h1
    exact not_sp2mKindType_two_omegaMinus hty
  · exact absurd h2.1 (by decide)

end Void

@[expose] def SpThreeGraphRowInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* StatedSp 3 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 3, RootKindSp e t f k κ) → False

theorem spThreeGraphRowsInput_of_rows (hLE : SpThreeGraphRowInput .linearEven)
    (hUE : SpThreeGraphRowInput .unitaryEven) (hLO : SpThreeGraphRowInput .linearOdd)
    (hUO : SpThreeGraphRowInput .unitaryOdd) : SpThreeGraphRowsInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt κ hκf hκs hκ
  cases κ with
  | field => exact hκf rfl
  | swap => exact hκs rfl
  | linearEven => exact hLE G L hset f K hKc hf e t ht hKt hκ
  | unitaryEven => exact hUE G L hset f K hKc hf e t ht hKt hκ
  | linearOdd => exact hLO G L hset f K hKc hf e t ht hKt hκ
  | unitaryOdd => exact hUO G L hset f K hKc hf e t ht hKt hκ
  | omegaPlus => exact not_rootKindSp_three_omegaPlus e t f 0 (hκ 0)
  | omegaMinus => exact not_rootKindSp_three_omegaMinus e t f 0 (hκ 0)

end CFSG.SeitzReduction.SymplecticPilot
