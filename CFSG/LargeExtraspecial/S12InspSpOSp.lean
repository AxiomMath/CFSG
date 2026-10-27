module

public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.S12InspPSLLin
public import CFSG.LargeExtraspecial.Types
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.Fischer.Fi22Order

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Submodule QuadraticMap CFSG.RankThree.OrthogonalInvolutions S12InspPSL
open CFSG.Blueprint

namespace S12InspSpO

theorem card_of_lieModel_psp {X : Type} [Group X] {m : ℕ} (h : LieModel X .PSp m 2 1) :
    Nat.card X = 2 ^ (m ^ 2) * ∏ j ∈ Finset.Icc 1 m, (2 ^ (2 * j) - 1) := by
  rcases h with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hc
    have : Fintype K := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
      (by rw [← Nat.card_eq_fintype_card, hK])
    rw [Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo, hK, pow_one]
  all_goals exact absurd ht (by decide)

end S12InspSpO

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem spo_two_le_ncard_sing {t : S.O} (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) :
    2 ≤ {v | S.q v = 0}.ncard := by
  have : Finite S.Qt := Module.finite_of_finite (ZMod 2)
  have hne : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ ⊥ := by
    intro h
    have h2 := htA.2.2.2.1
    rw [h, finrank_bot] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hsub : ({0, v} : Set S.Qt) ⊆ {x | S.q x = 0} := by
    rintro x (rfl | rfl)
    · exact map_zero S.q
    · exact htA.2.2.2.2 _ hv
  calc 2 = ({0, v} : Set S.Qt).ncard := (Set.ncard_pair (Ne.symm hv0)).symm
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

end Setting

end CFSG.LargeExtraspecial
