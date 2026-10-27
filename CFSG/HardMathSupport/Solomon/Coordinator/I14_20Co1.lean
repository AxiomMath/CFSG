module

public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Co1Cent
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20SylowOrd
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20BigOrd
public import CFSG.Sporadic.Schreier.Co1Generation

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator.I1420

open CFSG.Sporadic.Co1Schreier CFSG.Blueprint

theorem factorization_thirteen_card_GA :
    (4157776806543360000 : ℕ).factorization 13 = 1 := by
  have h : (4157776806543360000 : ℕ) = 13 * 319828985118720000 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

section Certs


theorem noOrderSixtyFive_GA (g : ↥GA) : orderOf g ≠ 65 := by
  have : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA]; norm_num)
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  exact no_order_five_mul_of_sylow (p := 13) (y0 := yE)
    (orderOf_eq_prime yE_pow_thirteen yE_ne_one)
    (by rw [card_GA]; exact factorization_thirteen_card_GA)
    (fun c hc h5 => no_order_five_of_commute_y13 c hc h5) g

theorem noOrderSixtyFive_Co1 (g : NativeSporadic.Co1) : orderOf g ≠ 65 :=
  fun h => noOrderSixtyFive_GA _ ((CFSG.Sporadic.Co1Block.orderOf_co1MatEquiv g).trans h)

theorem noOrderSixtyFiveAt_Co1
    (hb : Nonempty (NativeSporadic.Carrier .Co1 ≃* (TauCeti.CFSGIndex.sporadic .Co1).Group)) :
    NoOrderSixtyFiveAt .Co1 := by
  obtain ⟨e⟩ := hb
  intro g hg
  have h1 : orderOf (e.symm g) = 65 := by rw [MulEquiv.orderOf_eq e.symm g]; exact hg
  exact noOrderSixtyFive_Co1 (e.symm g) h1

end Certs

end CFSG.HardMathSupport.Solomon.Coordinator.I1420
