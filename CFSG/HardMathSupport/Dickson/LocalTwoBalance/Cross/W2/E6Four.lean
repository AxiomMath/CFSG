module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamOpen
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6FourAux.R3Plane
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6FourAux.R3TwPlane
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
  CFSG.LieType.Steinberg.Adjoint CFSG.TauCetiBridge

set_option linter.unusedSectionVars false


theorem innerPlaneBalance_catE6_four {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (q : TauCeti.PrimePower) (hv : (excIndex .E6 q).Valid) (hdvd : p ∣ q.card ^ 2 + 1) :
    InnerPlaneBalance p (CatT ⟨excIndex .E6 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  rw [← hK] at hdvd
  exact InnerPlaneBalance.of_mulEquiv e (innerPlaneBalance_adjointE6_four_R3 K hp hp5 hdvd)

theorem innerPlaneBalance_catTwistedE6_four {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (q : TauCeti.PrimePower) (hv : (excIndex .twistedE6 q).Valid) (hdvd : p ∣ q.card ^ 2 + 1) :
    InnerPlaneBalance p (CatT ⟨excIndex .twistedE6 q, hv⟩) := by
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  rw [TauCeti.PrimePower.card_def] at hdvd
  exact InnerPlaneBalance.of_mulEquiv e (innerPlaneBalance_twistedE6_four_R3' q.prime_p K
    q.exponent_pos hK σ hσ hp hp5 hdvd)

theorem e6Four_dvd_sq_add_one_of_orderOf_four {p n : ℕ} (hp : p.Prime)
    (he : orderOf ((n : ℕ) : ZMod p) = 4) : p ∣ n ^ 2 + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h4 : ((n : ℕ) : ZMod p) ^ 4 = 1 := by
    rw [← he]
    exact pow_orderOf_eq_one _
  have h2 : ((n : ℕ) : ZMod p) ^ 2 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [he] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have h3 : (((n : ℕ) : ZMod p) ^ 2 - 1) * (((n : ℕ) : ZMod p) ^ 2 + 1) = 0 := by
    linear_combination h4
  have h5 := (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 h2)
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  exact h5

theorem innerPlaneBalance_catE6_four_of_orderOf {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (q : TauCeti.PrimePower) (hv : (excIndex .E6 q).Valid)
    (he : orderOf ((q.card : ℕ) : ZMod p) = 4) :
    InnerPlaneBalance p (CatT ⟨excIndex .E6 q, hv⟩) :=
  innerPlaneBalance_catE6_four hp hp5 q hv (e6Four_dvd_sq_add_one_of_orderOf_four hp he)

theorem innerPlaneBalance_catTwistedE6_four_of_orderOf {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (q : TauCeti.PrimePower) (hv : (excIndex .twistedE6 q).Valid)
    (he : orderOf ((q.card : ℕ) : ZMod p) = 4) :
    InnerPlaneBalance p (CatT ⟨excIndex .twistedE6 q, hv⟩) :=
  innerPlaneBalance_catTwistedE6_four hp hp5 q hv (e6Four_dvd_sq_add_one_of_orderOf_four hp he)

theorem e6InnerFiveFour_holds : E6InnerFiveFour :=
  fun q hv _ h => innerPlaneBalance_catE6_four Nat.prime_five le_rfl q hv h

theorem twistedE6InnerFiveFour_holds : TwistedE6InnerFiveFour :=
  fun q hv _ h => innerPlaneBalance_catTwistedE6_four Nat.prime_five le_rfl q hv h

theorem innerPlaneBalanceAt_E6_four : InnerPlaneBalanceAt .E6 4 := by
  intro q hv p hp hp7 _ hpq he
  exact innerPlaneBalance_catE6_four_of_orderOf hp (by omega) q hv he

theorem innerPlaneBalanceAt_twistedE6_four : InnerPlaneBalanceAt .twistedE6 4 := by
  intro q hv p hp hp7 _ hpq he
  exact innerPlaneBalance_catTwistedE6_four_of_orderOf hp (by omega) q hv he

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
