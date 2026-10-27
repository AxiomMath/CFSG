module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamOpen
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.F4FourAux.Even
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldLinear
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge

set_option linter.unusedSectionVars false

theorem dvd_sq_add_one_of_orderOf_eq_four {p n : ℕ} (hp : p.Prime)
    (h : orderOf ((n : ℕ) : ZMod p) = 4) : p ∣ n ^ 2 + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : ((n : ℕ) : ZMod p) ^ 4 = 1 := by
    rw [← h]
    exact pow_orderOf_eq_one _
  have h2 : ((n : ℕ) : ZMod p) ^ 2 ≠ 1 := fun h' => by
    have := orderOf_dvd_of_pow_eq_one h'
    rw [h] at this
    omega
  have h3 : (((n : ℕ) : ZMod p) ^ 2 - 1) * (((n : ℕ) : ZMod p) ^ 2 + 1) = 0 := by
    linear_combination h1
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact absurd (sub_eq_zero.1 h4) h2
  · rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    exact h4

section Certs


theorem innerPlaneBalance_adjointF4_four (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpd : p ∣ Nat.card K ^ 2 + 1) :
    InnerPlaneBalance p (adjointGroup Tag.F4 K) := by
  obtain ⟨ℓ, f, hℓ, -, hf, hK⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.exists_char_card K
  refine W2.f4Four_innerPlaneBalance_of_actor hp (by omega) hpd ?_
  intro F hF g hg hgn x hx hxp hne x₁ hx₁
  by_cases h2 : ℓ = 2
  · subst h2
    exact W2.f4FourActor_even K (AlgebraicClosure K) F hf hK hF hp (by omega) hpd hg hgn hx hxp
      hne hx₁
  · exact W2.f4FourActor_odd K (AlgebraicClosure K) F hℓ h2 hf hK hF hp (by omega) hpd hg hgn
      hx hxp hne hx₁

theorem innerPlaneBalance_catF4_four (q : TauCeti.PrimePower) (hv : (excIndex .F4 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpd : p ∣ q.card ^ 2 + 1) :
    InnerPlaneBalance p (CatT ⟨excIndex .F4 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  rw [← hK] at hpd
  exact InnerPlaneBalance.of_mulEquiv e (innerPlaneBalance_adjointF4_four K hp hp5 hpd)

theorem innerPlaneBalance_catF4_of_orderOf_four (q : TauCeti.PrimePower)
    (hv : (excIndex .F4 q).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (he : orderOf ((q.card : ℕ) : ZMod p) = 4) :
    InnerPlaneBalance p (CatT ⟨excIndex .F4 q, hv⟩) :=
  innerPlaneBalance_catF4_four q hv hp hp5 (dvd_sq_add_one_of_orderOf_eq_four hp he)

theorem f4InnerFiveFour_holds : F4InnerFiveFour :=
  fun q hv _ h => innerPlaneBalance_catF4_four q hv Nat.prime_five le_rfl h

theorem innerPlaneBalanceAt_F4_four : InnerPlaneBalanceAt .F4 4 :=
  fun q hv _ hp hp7 _ _ he => innerPlaneBalance_catF4_of_orderOf_four q hv hp (by omega) he

end Certs

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
