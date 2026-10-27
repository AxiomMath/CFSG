module

public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.LieType.Ree.SuzukiOrder
import CFSG.Adapters.LieModelSmallOrders
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def LieModelOrders : Prop :=
  (∀ (X : Type) [Group X], LieModel X .PSL 3 2 2 → Nat.card X = 20160) ∧
    (∀ (X : Type) [Group X], SuzukiModel X 2 3 → Nat.card X = 29120) ∧
    ∀ (X : Type) [Group X], LieModel X .G2 0 2 2 → Nat.card X = 251596800

theorem card_of_lieModel_psl_three_two_two {X : Type} [Group X] (h : LieModel X .PSL 3 2 2) :
    Nat.card X = 20160 :=
  CFSG.Blueprint.LieModel.card_psl_three_four h

theorem card_of_suzukiModel_two_three {X : Type} [Group X]
    (h : SuzukiModel X 2 3) : Nat.card X = 29120 := by
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := h
  have ha1 : a = 1 := by omega
  subst ha1
  have hK' : Nat.card K = 2 ^ (2 * 1 + 1) := hK
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK']
  norm_num

theorem card_of_lieModel_g_two_two_two
    {X : Type} [Group X] (h : LieModel X .G2 0 2 2) :
    Nat.card X = 251596800 := by
  rcases h with ⟨ht, -⟩ | ⟨-, -, hm⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · have hc : Nat.card X = CFSG.Open.ordG2 (2 ^ 2) :=
      CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hm
    rw [hc]
    decide
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

theorem lieModelOrders :
    LieModelOrders :=
  ⟨fun _ _ h => card_of_lieModel_psl_three_two_two h,
    fun _ _ h => card_of_suzukiModel_two_three h,
    fun _ _ h => card_of_lieModel_g_two_two_two h⟩

end CFSG.EvenSporadicStandard.Induction
