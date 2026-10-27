module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcOrder
public import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem card_outer_eq_of_surjective_ker {G A : Type} [Group G] [Group A] (Θ : MulAut G →* A)
    (hsurj : Function.Surjective Θ) (hker : Θ.ker = inner G) :
    Nat.card (Outer G) = Nat.card A :=
  Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective Θ hsurj)).toEquiv

theorem ordG2_le' (q : ℕ) : ordG2 q ≤ q ^ 14 := by
  unfold ordG2
  calc q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 6 * q ^ 6 * q ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul le_rfl (Nat.sub_le _ _)) (Nat.sub_le _ _)
    _ = q ^ 14 := by ring

section Orders


theorem card_mulAut_adjointQuotient_G2_le (K : Type) [Field K] [Finite K] {p e : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hK : Nat.card K = p ^ e) :
    Nat.card (MulAut (AdjointQuotient .G2 K)) ≤ 2 * e * Nat.card K ^ 14 := by
  have he : 1 ≤ e := one_le_of_card_eq K hK
  refine card_mulAut_adjointQuotient_le .G2 K (b := 2 * e) (N := 14) ?_ ?_
  · by_cases h3 : p = 3
    · subst h3
      have : CharP K 3 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Fact.out he hK
      obtain ⟨-, -, ⟨Θ, -, hsurj, hker⟩, -⟩ :=
        G2_three_exact_automorphism_normal_form (f := e) he K hK
      have h : Nat.card (Outer (adjointGroup .G2 K)) = _ :=
        card_outer_eq_of_surjective_ker Θ hsurj hker
      rw [h, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    · obtain ⟨-, Θ, -, hsurj, hker, -⟩ :=
        odd_F4_and_nonexceptional_G2_automorphism_normal_form Fact.out hp2 he K hK .G2
          (Or.inr ⟨rfl, h3⟩)
      rw [card_outer_eq_of_surjective_ker Θ hsurj hker,
        (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Fact.out K hK).1]
      omega
  · rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2]
    exact ordG2_le' _

theorem card_mulAut_adjointQuotient_F4_le (K : Type) [Field K] [Finite K] {p e : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hK : Nat.card K = p ^ e) :
    Nat.card (MulAut (AdjointQuotient .F4 K)) ≤ e * Nat.card K ^ 52 := by
  have he : 1 ≤ e := one_le_of_card_eq K hK
  refine card_mulAut_adjointQuotient_le .F4 K (b := e) (N := 52) ?_ ?_
  · obtain ⟨-, Θ, -, hsurj, hker, -⟩ :=
      odd_F4_and_nonexceptional_G2_automorphism_normal_form Fact.out hp2 he K hK .F4 (Or.inl rfl)
    rw [card_outer_eq_of_surjective_ker Θ hsurj hker,
      (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Fact.out K hK).1]
  · rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4]
    exact CFSG.RankThree.PartOne.F106.ordF4_le _

end Orders

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
