module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.Quotient.QuotientAction

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.PbarDimension

theorem finrank_eq {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : ExtraspecialBinaryActionCounterexample G p P T B e ρ) (n : ℕ) (hn : Nat.card ↥P = p ^ (1 + 2 * n)) :
    haveI : Fact p.Prime := ⟨hc.oddPrimeClassTwoAction.setting.prime⟩
    haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨hc.oddPrimeClassTwoAction.setting.class_le_two⟩
    haveI : Fact (Monoid.exponent ↥P = p) := ⟨hc.oddPrimeClassTwoAction.setting.exponent⟩
    Module.finrank (ZMod p) (Additive (Quotient.Pbar P)) = 2 * n := by
  have hp : p.Prime := hc.oddPrimeClassTwoAction.setting.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨hc.oddPrimeClassTwoAction.setting.class_le_two⟩
  haveI : Fact (Monoid.exponent ↥P = p) := ⟨hc.oddPrimeClassTwoAction.setting.exponent⟩
  show Module.finrank (ZMod p) (Additive (Quotient.Pbar P)) = 2 * n
  have hZ : Nat.card (Subgroup.center ↥P) = p := hc.extraspecial.2.2.2
  have hfin : Finite (Additive (Quotient.Pbar P)) :=
    inferInstanceAs (Finite (↥P ⧸ Subgroup.center ↥P))
  haveI : Module.Finite (ZMod p) (Additive (Quotient.Pbar P)) := Module.Finite.of_finite
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥P)
  have hq : Nat.card (Quotient.Pbar P) * p = p ^ (2 * n) * p := by
    rw [← hZ, ← hmul, hn, hZ]; ring
  have hq' : Nat.card (Quotient.Pbar P) = p ^ (2 * n) :=
    Nat.eq_of_mul_eq_mul_right hp.pos hq
  have hcard : Nat.card (Additive (Quotient.Pbar P)) = p ^ (2 * n) := by
    rw [← hq']; exact (Nat.card_congr Additive.toMul)
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod] at hcard
  exact Nat.pow_right_injective hp.two_le hcard

end CFSG.LocalAnalysis.RankThreeUC.Section5.PbarDimension
