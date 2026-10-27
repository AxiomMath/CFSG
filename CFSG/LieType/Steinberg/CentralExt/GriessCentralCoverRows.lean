module

public import CFSG.LieType.Steinberg.CentralExt.GriessGTwoFour
public import CFSG.LieType.Steinberg.CentralExt.GriessFFourTwo
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
import CFSG.RankThree.PerfectCover.HopfCentralCovers

public section

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

namespace CFSG.LieType.Steinberg.CentralExt.GriessCentralCovers

variable {X : Type} [Group X]

theorem central_covers_of_card_two (hM : Nat.card (CFSG.Open.griessHopfMultiplier X) = 2) :
    Nonempty (CFSG.Open.griessHopfMultiplier X ≃* Multiplicative (ZMod 2)) ∧
    (∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L →
      Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
      ∀ S : Sylow 2 (Subgroup.center L), Nat.card S ≤ 2) ∧
    (∀ (L L' : Type) [Group L] [Group L'] [Finite L] [Finite L'],
      CFSG.IsQuasisimple L → CFSG.IsQuasisimple L' →
      Nat.card (Subgroup.center L) = 2 → Nat.card (Subgroup.center L') = 2 →
      Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
      Nonempty ((L' ⧸ Subgroup.center L') ≃* X) → Nonempty (L ≃* L')) := by
  have : Finite (CFSG.Open.griessHopfMultiplier X) := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS (S : Sylow 2 (CFSG.Open.griessHopfMultiplier X)) : Nat.card S = 2 := by
    rw [S.card_eq_multiplicity, hM, Nat.Prime.factorization_self Nat.prime_two, pow_one]
  have h := CFSG.RankThree.PerfectCover.hopf_central_cover_consequences X
  exact ⟨⟨mulEquivOfPrimeCardEq hM (by simp)⟩, h.1 fun S => (hS S).le, h.2 hS⟩

theorem card_two_of_row {t : StatedLieTag} {n p f : ℕ} (h : GriessAll.GriessRow X t n p f)
    (hc : (genericOrders t n p f).1 * (genericOrders t n p f).2 *
      ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) = 2) :
    Nat.card (CFSG.Open.griessHopfMultiplier X) = 2 := by
  rw [Nat.card_congr h.2.some.toEquiv, ← hc]
  simp only [generic, exceptional, Nat.card_prod]
  simp [Nat.card_congr Multiplicative.toAdd]

theorem native_central_covers_z2 {t : StatedLieTag} {n p f : ℕ}
    (hmodel : CFSG.Blueprint.LieModel X t n p f)
    (ht : t = .PSp ∧ n = 3 ∧ p = 2 ∧ f = 1 ∨ t = .G2 ∧ n = 0 ∧ p = 2 ∧ f = 2 ∨
      t = .F4 ∧ n = 0 ∧ p = 2 ∧ f = 1) :
    Nonempty (CFSG.Open.griessHopfMultiplier X ≃* Multiplicative (ZMod 2)) ∧
    (∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L →
      Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
      ∀ S : Sylow 2 (Subgroup.center L), Nat.card S ≤ 2) ∧
    (∀ (L L' : Type) [Group L] [Group L'] [Finite L] [Finite L'],
      CFSG.IsQuasisimple L → CFSG.IsQuasisimple L' →
      Nat.card (Subgroup.center L) = 2 → Nat.card (Subgroup.center L') = 2 →
      Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
      Nonempty ((L' ⧸ Subgroup.center L') ≃* X) → Nonempty (L ≃* L')) := by
  apply central_covers_of_card_two
  rcases ht with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · rw [Nat.card_congr (CFSG.EvenSmallLie.SympSix.multiplier_PSp_three_two_one X
      hmodel).2.some.toEquiv]
    simp
  · exact card_two_of_row (GriessExceptional.g2_four_native_row
      (GriessNative.chevalley_of_lieModel hmodel (by decide)).2) rfl
  · exact card_two_of_row (GriessExceptional.f4_two_native_row
      (GriessNative.chevalley_of_lieModel hmodel (by decide)).2) rfl

section TauCeti


theorem central_covers_z2 {t : StatedLieTag} {n p f : ℕ}
    (hmodel : CFSG.Models.LieModel X t n p f)
    (ht : t = .PSp ∧ n = 3 ∧ p = 2 ∧ f = 1 ∨ t = .G2 ∧ n = 0 ∧ p = 2 ∧ f = 2 ∨
      t = .F4 ∧ n = 0 ∧ p = 2 ∧ f = 1) :
    Nonempty (CFSG.Open.griessHopfMultiplier X ≃* Multiplicative (ZMod 2)) ∧
    (∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L →
      Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
      ∀ S : Sylow 2 (Subgroup.center L), Nat.card S ≤ 2) ∧
    (∀ (L L' : Type) [Group L] [Group L'] [Finite L] [Finite L'],
      CFSG.IsQuasisimple L → CFSG.IsQuasisimple L' →
      Nat.card (Subgroup.center L) = 2 → Nat.card (Subgroup.center L') = 2 →
      Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
      Nonempty ((L' ⧸ Subgroup.center L') ≃* X) → Nonempty (L ≃* L')) := by
  rcases ht with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact native_central_covers_z2 (GriessClassical.blueprint_lieModel_psp hmodel) (Or.inl
      ⟨rfl, rfl, rfl, rfl⟩)
  · exact central_covers_of_card_two (card_two_of_row (GriessExceptional.g2_four_row hmodel) rfl)
  · exact central_covers_of_card_two (card_two_of_row (GriessExceptional.f4_two_row hmodel) rfl)

end TauCeti

end CFSG.LieType.Steinberg.CentralExt.GriessCentralCovers
