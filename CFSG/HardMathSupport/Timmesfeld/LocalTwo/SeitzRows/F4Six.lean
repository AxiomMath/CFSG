module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.F4Assembly
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.F4SixEven

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows

open Subgroup CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.F4Weyl CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2 CFSG.LieType.SeitzGeneration
  CFSG.TauCetiBridge
open scoped commutatorElement

set_option linter.unusedSectionVars false

theorem dvd_sq_sub_self_add_one_of_orderOf_eq_six {p n : ℕ} (hp : p.Prime)
    (h : orderOf ((n : ℕ) : ZMod p) = 6) : p ∣ n ^ 2 - n + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h6 : ((n : ℕ) : ZMod p) ^ 6 = 1 := by
    rw [← h]
    exact pow_orderOf_eq_one _
  have h3 : ((n : ℕ) : ZMod p) ^ 3 ≠ 1 := fun h' => by
    have := orderOf_dvd_of_pow_eq_one h'
    rw [h] at this
    omega
  have h2 : ((n : ℕ) : ZMod p) ^ 2 ≠ 1 := fun h' => by
    have := orderOf_dvd_of_pow_eq_one h'
    rw [h] at this
    omega
  have hx1 : ((n : ℕ) : ZMod p) + 1 ≠ 0 := fun h' => by
    have : ((n : ℕ) : ZMod p) = -1 := eq_neg_of_add_eq_zero_left h'
    apply h2
    rw [this]
    exact neg_one_sq
  have h4 : (((n : ℕ) : ZMod p) ^ 3 - 1) * (((n : ℕ) : ZMod p) ^ 3 + 1) = 0 := by
    linear_combination h6
  have h5 : ((n : ℕ) : ZMod p) ^ 3 + 1 = 0 :=
    (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 h3)
  have h7 : (((n : ℕ) : ZMod p) + 1) * (((n : ℕ) : ZMod p) ^ 2 - ((n : ℕ) : ZMod p) + 1) = 0 := by
    linear_combination h5
  have h8 : ((n : ℕ) : ZMod p) ^ 2 - ((n : ℕ) : ZMod p) + 1 = 0 :=
    (mul_eq_zero.1 h7).resolve_left hx1
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_sub (Nat.le_self_pow two_ne_zero n)]
  push_cast
  exact h8


section Six


theorem innerPlaneBalance_adjointF4_six (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : p ∣ Nat.card K ^ 2 - Nat.card K + 1) :
    InnerPlaneBalance p (adjointGroup Tag.F4 K) := by
  obtain ⟨ℓ, f, hℓ, -, hf, hK⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.exists_char_card K
  refine f4_innerPlaneBalance_of_actor_of_coord hp hp3 f4PhiSix ?_ ?_
  · intro F hF P hP
    exact exists_lang_torus_coordinates_three_six K (AlgebraicClosure K) F hF
      (Or.inr ⟨rfl, rfl, hpd⟩) hp hp3 P hP
  · intro F hF g hg hgn x hx hxp hne x₁ hx₁
    by_cases h2 : ℓ = 2
    · subst h2
      exact f4SixActor_even K (AlgebraicClosure K) F hf hK hF hp hp3 hpd hg hgn hx hxp hne hx₁
    · exact f4SixActor_odd K (AlgebraicClosure K) F hℓ h2 hf hK hF hp hp3 hpd hg hgn hx hxp hne
        hx₁

end Six

section TauCeti


theorem innerPlaneBalance_catF4_of_orderOf_six (q : TauCeti.PrimePower)
    (hv : (excIndex .F4 q).Valid) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (he : orderOf ((q.card : ℕ) : ZMod p) = 6) :
    InnerPlaneBalance p (CatT ⟨excIndex .F4 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have hpd : p ∣ Nat.card K ^ 2 - Nat.card K + 1 := by
    rw [hK]
    exact dvd_sq_sub_self_add_one_of_orderOf_eq_six hp he
  exact InnerPlaneBalance.of_mulEquiv e (innerPlaneBalance_adjointF4_six K hp (by omega) hpd)

theorem innerPlaneBalanceAt_F4_six : InnerPlaneBalanceAt .F4 6 :=
  fun q hv _ hp hp7 _ _ he => innerPlaneBalance_catF4_of_orderOf_six q hv hp hp7 he

end TauCeti

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows
