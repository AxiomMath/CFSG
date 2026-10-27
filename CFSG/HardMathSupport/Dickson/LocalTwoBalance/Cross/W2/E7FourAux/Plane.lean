module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E7FourAux.Chain
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.T1
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesE7E8

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

set_option linter.unusedSectionVars false

@[expose] def E7TwoFiveBalance : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (excIndex .E7 q).Valid), q.card = 2 →
    InnerPlaneBalance 5 (CatT ⟨excIndex .E7 q, hv⟩)


theorem innerPlaneBalance_catE7_four_of_three_le (q : TauCeti.PrimePower)
    (hv : (excIndex .E7 q).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ≠ q.p)
    (he : orderOf ((q.card : ℕ) : ZMod p) = 4) (hq3 : 3 ≤ q.card) :
    InnerPlaneBalance p (CatT ⟨excIndex .E7 q, hv⟩) :=
  innerPlaneBalance_cat_of_lang_rigid_algM (k := .E7) (by trivial)
    (R := fun p c => (5 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 4) ∧ 3 ≤ c) (M := e7FourBMat)
    (fun hk q' hv' p' hp' hR hpq' =>
      langTorusAtAlgM_E7_four_odd frobeniusOnRoots_proved hk q' hv' p' hp' hR.1 hpq')
    (fun q' hv' p' L _ _ S hR hq hAlg hρ _ =>
      setupRigid_E7_four_odd S hR.1.1 hAlg (hq ▸ hR.2) (hq ▸ hR.1.2) hρ)
    t1_pieces center_catT_E7_eq_bot q hv hp ⟨⟨hp5, he⟩, hq3⟩ hpq

theorem innerPlaneBalance_catE7_four (h2 : E7TwoFiveBalance) (q : TauCeti.PrimePower)
    (hv : (excIndex .E7 q).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ≠ q.p)
    (he : orderOf ((q.card : ℕ) : ZMod p) = 4) :
    InnerPlaneBalance p (CatT ⟨excIndex .E7 q, hv⟩) := by
  by_cases hq2 : q.card = 2
  · have h5 : p = 5 := e7Four_eq_five_of_orderOf_two_eq_four hp hp5 (by rwa [hq2] at he)
    subst h5
    exact h2 q hv hq2
  · have hge : 2 ≤ q.card := by
      have := q.prime_p.two_le
      rw [TauCeti.PrimePower.card_def]
      calc 2 ≤ q.p := this
        _ = q.p ^ 1 := (pow_one _).symm
        _ ≤ q.p ^ q.exponent := Nat.pow_le_pow_right (by omega) q.exponent_pos
    exact innerPlaneBalance_catE7_four_of_three_le q hv hp hp5 hpq he (by omega)

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
