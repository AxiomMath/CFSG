module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6SixAux.Plane
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerBase
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
  CFSG.LieType.Steinberg.Adjoint CFSG.TauCetiBridge

set_option linter.unusedSectionVars false


theorem e6Six_dvd_int {p q : ℕ} (h : p ∣ q ^ 2 - q + 1) :
    (p : ℤ) ∣ (q : ℤ) ^ 2 - (q : ℤ) + 1 := by
  have h1 : q ≤ q ^ 2 := Nat.le_self_pow two_ne_zero q
  have h2 : (((q ^ 2 - q + 1 : ℕ)) : ℤ) = (q : ℤ) ^ 2 - (q : ℤ) + 1 := by
    push_cast [Nat.cast_sub h1]
    ring
  rw [← h2]
  exact_mod_cast h

theorem innerPlaneBalance_catE6_six {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (q : TauCeti.PrimePower) (hv : (excIndex .E6 q).Valid)
    (hdvd : p ∣ q.card ^ 2 - q.card + 1) :
    InnerPlaneBalance p (CatT ⟨excIndex .E6 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  rw [← hK] at hdvd
  exact InnerPlaneBalance.of_mulEquiv e (innerPlaneBalance_adjointE6_six_R3 K hp (by omega)
    (e6Six_dvd_int hdvd))

theorem e6Six_sq_sub_add_one_of_orderOf_six {p : ℕ} [Fact p.Prime] {r : ZMod p}
    (he : orderOf r = 6) : r ^ 2 - r + 1 = 0 := by
  have h6 : r ^ 6 = 1 := by
    rw [← he]
    exact pow_orderOf_eq_one _
  have hne : ∀ m : ℕ, 0 < m → m < 6 → r ^ m ≠ 1 := fun m hm hm6 h => by
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [he] at h1
    have h2 := Nat.le_of_dvd hm h1
    omega
  have h3 : r ^ 3 + 1 = 0 := by
    have h : (r ^ 3 - 1) * (r ^ 3 + 1) = 0 := by linear_combination h6
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 (hne 3 (by norm_num) (by norm_num)))
  have hr1 : r + 1 ≠ 0 := fun h =>
    hne 2 (by norm_num) (by norm_num) (by linear_combination (r - 1) * h)
  have h2 : (r + 1) * (r ^ 2 - r + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.1 h2).resolve_left hr1

theorem e6Six_dvd_of_orderOf_six {p n : ℕ} (hp : p.Prime)
    (he : orderOf ((n : ℕ) : ZMod p) = 6) : p ∣ n ^ 2 - n + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h5 := e6Six_sq_sub_add_one_of_orderOf_six he
  have h1 : n ≤ n ^ 2 := Nat.le_self_pow two_ne_zero n
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_sub h1]
  push_cast
  exact h5

theorem innerPlaneBalance_catE6_six_of_orderOf {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (q : TauCeti.PrimePower) (hv : (excIndex .E6 q).Valid)
    (he : orderOf ((q.card : ℕ) : ZMod p) = 6) :
    InnerPlaneBalance p (CatT ⟨excIndex .E6 q, hv⟩) :=
  innerPlaneBalance_catE6_six hp hp7 q hv (e6Six_dvd_of_orderOf_six hp he)

theorem innerPlaneBalanceAt_E6_six : InnerPlaneBalanceAt .E6 6 := by
  intro q hv p hp hp7 _ hpq he
  exact innerPlaneBalance_catE6_six_of_orderOf hp hp7 q hv he

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
