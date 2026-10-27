module

public import CFSG.LargeExtraspecial.OutSixBasic
public import CFSG.LargeExtraspecial.OutSixUnitary
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

theorem card_outer_psl_two_dvd {n : ℕ} (hn : 3 ≤ n) :
    Nat.card (Outer (PSL(n, ZMod 2))) ∣ 2 := by
  rw [Nat.card_congr (equivalence
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL n (ZMod 2))).toEquiv]
  have h := UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound (k := ZMod 2)
    (p := 2) (f := 1) Nat.prime_two le_rfl hn (by rw [Nat.card_zmod, pow_one])
  simpa using h

theorem card_outer_timmesfeldPSU {n : ℕ} (hn : 4 ≤ n) :
    Nat.card (Outer (timmesfeldPSU n)) = 2 * Nat.gcd n 3 := by
  rw [Nat.card_congr (equivalence (timmesfeldPSUEquiv (n := n) (by omega))).toEquiv,
    (UnitaryHigher.unitary_full_diagonal_outer_order unitaryFieldData_two_one (n := n)
      (by omega) (fun h => by omega)).2.2.2.2.1]
  norm_num

theorem card_outer_timmesfeldPSU_six : Nat.card (Outer (timmesfeldPSU 6)) = 6 := by
  rw [card_outer_timmesfeldPSU (by norm_num)]
  norm_num

theorem index_dvd_two_of_mulEquiv_psl {X : Type*} [Group X] {n : ℕ} (hn : 3 ≤ n)
    (X₀ : Subgroup X) [X₀.Normal] (e : X₀ ≃* PSL(n, ZMod 2))
    (hC : centralizer (X₀ : Set X) ≤ X₀) : X₀.index ∣ 2 :=
  (index_dvd_card_outer_of_mulEquiv X₀ hC e).trans (card_outer_psl_two_dvd hn)

theorem outL62Input :
    ∀ (X : Type) [Group X] [Finite X] (X₀ : Subgroup X), X₀.Normal →
      Nonempty (X₀ ≃* PSL(6, ZMod 2)) → centralizer (X₀ : Set X) ≤ X₀ → X₀.index ≤ 2 := by
  intro X _ _ X₀ _ ⟨e⟩ hC
  exact Nat.le_of_dvd two_pos (index_dvd_two_of_mulEquiv_psl (by norm_num) X₀ e hC)

theorem outU62Input :
    ∀ (X : Type) [Group X] [Finite X] (X₀ : Subgroup X), X₀.Normal →
      Nonempty (X₀ ≃* timmesfeldPSU 6) → centralizer (X₀ : Set X) ≤ X₀ → X₀.index ∣ 6 := by
  intro X _ _ X₀ _ ⟨e⟩ hC
  exact card_outer_timmesfeldPSU_six ▸ index_dvd_card_outer_of_mulEquiv X₀ hC e

end CFSG.LargeExtraspecial.S14
