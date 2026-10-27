module

public import CFSG.Holt.PointHullTwoGroupBasic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.Holt.OddCoreHull

open MulAction CFSG.Open PointHull

section Quotient

variable {X : Type*} [Group X] [Finite X]

theorem eq_one_of_mem_pPrimeCore {W P : Subgroup X} (hP : IsPGroup 2 P) {x : W}
    (hxP : (x : X) ∈ P) (hx : x ∈ CFSG.pPrimeCore 2 W) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have h1 : orderOf x ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using congrArg Subtype.val hk))
  have h2 : orderOf x ∣ Nat.card (CFSG.pPrimeCore 2 W) := Subgroup.orderOf_dvd_natCard _ hx
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (CFSG.pPrimeCore 2 W)) :=
    Nat.Coprime.pow_left k CFSG.pPrimeCore_coprime_card
  rw [← orderOf_eq_one_iff, ← Nat.dvd_one, ← hcop.gcd_eq_one]
  exact Nat.dvd_gcd h1 h2

end Quotient

end CFSG.Holt.OddCoreHull
