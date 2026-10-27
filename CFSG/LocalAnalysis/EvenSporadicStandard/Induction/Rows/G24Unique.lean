module

public import CFSG.LieType.Multipliers.G24Bridge
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Multipliers


theorem untwisted_of_lieModel_g24 {X : Type} [Group X] (h : LieModel X .G2 0 2 2) :
    UntwistedChevalleyModel X .G2 (2 ^ 2) := by
  rcases h with ⟨ht, -⟩ | ⟨-, -, hm⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact hm.2
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

theorem nonempty_ringEquiv_F4' {K : Type} [Field K] (hK : Nat.card K = 4) :
    Nonempty (K ≃+* CFSG.Fischer.F4) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  exact ⟨FiniteField.ringEquivOfCardEq (by rw [Fintype.card_eq_nat_card, hK,
    CFSG.Fischer.F4.card])⟩

theorem lieModel_g24_equiv {A B : Type} [Group A] [Group B] (hA : LieModel A .G2 0 2 2)
    (hB : LieModel B .G2 0 2 2) : Nonempty (A ≃* B) := by
  obtain ⟨K, _, _, hK, ⟨eA⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2
    (untwisted_of_lieModel_g24 hA)
  obtain ⟨K', _, _, hK', ⟨eB⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2
    (untwisted_of_lieModel_g24 hB)
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hK4' : Nat.card K' = 4 := by rw [hK']; norm_num
  obtain ⟨σ⟩ := nonempty_ringEquiv_F4' hK4
  obtain ⟨σ'⟩ := nonempty_ringEquiv_F4' hK4'
  exact ⟨eA.trans ((G24.adjointEquiv σ hK4).trans ((G24.adjointEquiv σ' hK4').symm.trans
    eB.symm))⟩

end CFSG.EvenSporadicStandard.Induction
