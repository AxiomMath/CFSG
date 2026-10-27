module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwistedE6ThreeAux.Reduction
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerBase
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
  CFSG.LieType.Steinberg.Adjoint CFSG.TauCetiBridge

set_option linter.unusedSectionVars false


theorem innerPlaneBalance_catTwistedE6_three {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (q : TauCeti.PrimePower) (hv : (excIndex .twistedE6 q).Valid)
    (hdvd : p ∣ q.card ^ 2 + q.card + 1) :
    InnerPlaneBalance p (CatT ⟨excIndex .twistedE6 q, hv⟩) := by
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  rw [TauCeti.PrimePower.card_def] at hdvd
  exact InnerPlaneBalance.of_mulEquiv e (TwE6Three.innerPlaneBalance_twistedE6_three_R3 q.prime_p K
    q.exponent_pos hK σ hσ hp (by omega) hdvd)

theorem twE6Three_dvd_of_orderOf_three {p n : ℕ} (hp : p.Prime)
    (he : orderOf ((n : ℕ) : ZMod p) = 3) : p ∣ n ^ 2 + n + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h3 : ((n : ℕ) : ZMod p) ^ 3 = 1 := by
    rw [← he]
    exact pow_orderOf_eq_one _
  have h1 : ((n : ℕ) : ZMod p) ≠ 1 := fun h => by
    rw [h, orderOf_one] at he
    omega
  have h2 : (((n : ℕ) : ZMod p) - 1) *
      (((n : ℕ) : ZMod p) ^ 2 + ((n : ℕ) : ZMod p) + 1) = 0 := by
    linear_combination h3
  have h5 := (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 h1)
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  exact h5

theorem innerPlaneBalance_catTwistedE6_three_of_orderOf {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (q : TauCeti.PrimePower) (hv : (excIndex .twistedE6 q).Valid)
    (he : orderOf ((q.card : ℕ) : ZMod p) = 3) :
    InnerPlaneBalance p (CatT ⟨excIndex .twistedE6 q, hv⟩) :=
  innerPlaneBalance_catTwistedE6_three hp hp7 q hv (twE6Three_dvd_of_orderOf_three hp he)

theorem innerPlaneBalanceAt_twistedE6_three : InnerPlaneBalanceAt .twistedE6 3 := by
  intro q hv p hp hp7 _ hpq he
  exact innerPlaneBalance_catTwistedE6_three_of_orderOf hp hp7 q hv he

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
