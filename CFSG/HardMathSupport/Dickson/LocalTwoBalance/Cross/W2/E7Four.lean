module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamOpen
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E7FourAux.TwoFive

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.HardMathSupport.Timmesfeld.LocalTwo


theorem innerPlaneBalance_catE7_four_holds (q : TauCeti.PrimePower)
    (hv : (excIndex .E7 q).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ≠ q.p)
    (he : orderOf ((q.card : ℕ) : ZMod p) = 4) :
    InnerPlaneBalance p (CatT ⟨excIndex .E7 q, hv⟩) :=
  W2.innerPlaneBalance_catE7_four W2.e7TwoFiveBalance_holds q hv hp hp5 hpq he

theorem e7Four_orderOf_eq_four_of_five_dvd_sq_add_one (n : ℕ) (h : 5 ∣ n ^ 2 + 1) :
    orderOf ((n : ℕ) : ZMod 5) = 4 := by
  have h1 : ((n : ZMod 5)) ^ 2 + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 5).2 h
    simpa using this
  have h2 : (n : ZMod 5) ^ 2 = -1 := by linear_combination h1
  have h4 : (n : ZMod 5) ^ 4 = 1 := by
    have : (n : ZMod 5) ^ 4 = ((n : ZMod 5) ^ 2) ^ 2 := by ring
    rw [this, h2]; norm_num
  have hne : ¬ (n : ZMod 5) ^ 2 = 1 := by
    rw [h2]
    decide
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := (n : ZMod 5)) (by simpa using hne)
    (by simpa using h4)
  simpa using this

theorem e7InnerFiveFour_holds : E7InnerFiveFour :=
  fun q hv hq5 h =>
    innerPlaneBalance_catE7_four_holds q hv Nat.prime_five le_rfl (fun h5 => hq5 h5.symm)
      (e7Four_orderOf_eq_four_of_five_dvd_sq_add_one q.card h)

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
