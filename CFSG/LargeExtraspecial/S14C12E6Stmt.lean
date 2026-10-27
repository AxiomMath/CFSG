module

public import CFSG.LargeExtraspecial.S14C12TOrd
public import CFSG.LargeExtraspecial.S14C12Lit
public import CFSG.LargeExtraspecial.S14Claims

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open CFSG.Blueprint

@[expose] def TwoE6TwoCentralInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G], ChevalleyExceptionalModel G .twistedE6 2 1 →
    ∀ z : G, orderOf z = 2 → 2 ^ 36 ∣ Nat.card (centralizer ({z} : Set G)) →
      Nat.card (centralizer ({z} : Set G)) = 2 ^ 36 * 3 ^ 6 * 5 * 7 * 11

theorem mbar0_eq_top_of_twoCentral (hRS : ReifartSmithU62Input) (hAS : TwoE6TwoCentralInput)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) : Mbar0 S = ⊤ := by
  have hM := card_M_eq_of_U6 S hU
  rw [S.card_Q_eq, hw] at hM
  have hdvd : 2 ^ 36 ∣ Nat.card (centralizer ({S.z} : Set G)) := by
    change 2 ^ 36 ∣ Nat.card S.M
    rw [hM]
    exact Dvd.intro (280665 * (Mbar0 S).index) (by ring)
  have hC := hAS G (hRS G S hw hU) S.z S.orderOf_z hdvd
  change Nat.card S.M = _ at hC
  rw [hM] at hC
  refine Subgroup.index_eq_one.mp (Nat.eq_of_mul_eq_mul_left
    (show 0 < 2 ^ (1 + 2 * 10) * 9196830720 by norm_num) ?_)
  rw [hC]
  norm_num

theorem claim14_12U_of' (hRS : ReifartSmithU62Input) (hAS : TwoE6TwoCentralInput) :
    Claim14_12U := by
  intro G _ _ _ S g t c _ hc hocc _ _ _ _ _ hU
  have hw : S.width = 10 := by
    rw [hocc.2.1]
    rcases hc with rfl | rfl <;> rfl
  rw [mbar0_eq_top_of_twoCentral hRS hAS S hw hU, index_top]
  norm_num

end CFSG.LargeExtraspecial.S14
