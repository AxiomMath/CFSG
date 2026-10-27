module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapLift

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup Equiv Equiv.Perm

private theorem card_cycleType_eq_of_support_card {α : Type*} [DecidableEq α] [Fintype α]
    {σ : Perm α} (hσ : σ * σ = 1) {k : ℕ} (hs : σ.support.card = 2 * k) :
    Multiset.card σ.cycleType = k := by
  have h := card_support_eq_two_mul_card_cycleType hσ
  omega

theorem τ₀_mul_self : τ₀ * τ₀ = 1 := by
  decide

theorem isSwap_τ₀ : τ₀.IsSwap := by
  exact ⟨8, 9, by decide, rfl⟩

theorem sign_τ₀ : sign τ₀ = -1 := by
  simpa [τ₀] using Equiv.Perm.sign_swap (x := (8 : Fin 10)) (y := 9) (by decide)

theorem τ₀_apply_eight : τ₀ 8 = 9 := by
  simpa [τ₀] using Equiv.swap_apply_left (8 : Fin 10) 9

theorem r₁'_mul_self : r₁' * r₁' = 1 := by
  decide

theorem r₂'_mul_self : r₂' * r₂' = 1 := by
  decide

theorem r₃'_mul_self : r₃' * r₃' = 1 := by
  decide

theorem ρ₄'_mul_self : ρ₄' * ρ₄' = 1 := by
  decide

theorem card_cycleType_r₁' : Multiset.card r₁'.cycleType = 1 :=
  card_cycleType_eq_of_support_card r₁'_mul_self (k := 1) (by decide)

theorem card_cycleType_r₂' : Multiset.card r₂'.cycleType = 2 :=
  card_cycleType_eq_of_support_card r₂'_mul_self (k := 2) (by decide)

theorem card_cycleType_r₃' : Multiset.card r₃'.cycleType = 3 :=
  card_cycleType_eq_of_support_card r₃'_mul_self (k := 3) (by decide)

theorem card_cycleType_ρ₄' : Multiset.card ρ₄'.cycleType = 4 :=
  card_cycleType_eq_of_support_card ρ₄'_mul_self (k := 4) (by decide)

theorem sign_r₁' : sign r₁' = -1 := by
  change sign (Equiv.swap (0 : Fin 8) 1) = -1
  exact Equiv.Perm.sign_swap (by decide)

theorem sign_r₂' : sign r₂' = 1 := by
  change sign (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3) = 1
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide)]
  decide

theorem sign_r₃' : sign r₃' = -1 := by
  change sign (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3 * Equiv.swap 4 5) = -1
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
  decide

theorem sign_ρ₄' : sign ρ₄' = 1 := by
  change sign (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3 * Equiv.swap 4 5 *
    Equiv.swap 6 7) = 1
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
  decide

theorem card_cycleType_τ₀_mul_ρ₄ : Multiset.card (τ₀ * ρ₄).cycleType = 5 :=
  card_cycleType_eq_of_support_card (σ := τ₀ * ρ₄) (by decide) (k := 5) (by decide)

theorem τ₀_mul_ρ₄_mul_self : (τ₀ * ρ₄) * (τ₀ * ρ₄) = 1 := by
  decide

theorem τ₀_mul_r₂_eq : τ₀ * r₂ = τ₀ * liftS8 r₂' := by
  rw [liftS8_r₂']

theorem τ₀_mul_ρ₄_eq : τ₀ * ρ₄ = τ₀ * liftS8 ρ₄' := by
  rw [liftS8_ρ₄']

end CFSG.OddStandard.AltStdSec.SwapPattern
