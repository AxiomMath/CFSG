module

public import CFSG.LieType.Chevalley.E7EvenRootCount
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2ConjDim
public import CFSG.RankThree.OddKernel.InvolutionDims

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.OddKernel (fixSpace)

private theorem neg_one_units_ne_one {L : Type} [Field L] (h2 : (2 : L) ≠ 0) :
    (-1 : Lˣ) ≠ 1 := by
  intro h
  have h1 : (-1 : L) = 1 := congrArg Units.val h
  exact h2 (by
    rw [← one_add_one_eq_two]
    exact neg_eq_iff_add_eq_zero.mp h1)

private theorem prod_zpow_neg_one {L : Type} [Field L]
    (S : Finset (Fin Tag.E7.rank)) (v : Fin Tag.E7.rank → ℤ) :
    (∏ i ∈ S, (-1 : Lˣ) ^ v i) = (-1 : Lˣ) ^ (∑ i ∈ S, v i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]

open scoped _root_.Classical in
private theorem rootChar_sign_eq {L : Type} [Field L]
    {a : Fin Tag.E7.rank → Lˣ} (ha : ∀ i, a i = 1 ∨ a i = -1)
    (v : Fin Tag.E7.rank → ℤ) :
    rootChar a v = (-1 : Lˣ) ^ (∑ i ∈ Finset.univ.filter (fun i => a i = -1), v i) := by
  classical
  rw [rootChar]
  rw [← Finset.prod_filter_mul_prod_filter_not (s := Finset.univ)
    (p := fun i => a i = -1) (f := fun i => a i ^ v i)]
  have hcompl : (∏ i ∈ Finset.univ.filter (fun i => ¬a i = -1), a i ^ v i) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    rw [Finset.mem_filter] at hi
    rcases ha i with h | h
    · rw [h, one_zpow]
    · exact absurd h hi.2
  rw [hcompl, mul_one]
  rw [show (∏ i ∈ Finset.univ.filter (fun i => a i = -1), a i ^ v i) =
      ∏ i ∈ Finset.univ.filter (fun i => a i = -1), (-1 : Lˣ) ^ v i from by
    apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]]
  exact prod_zpow_neg_one _ _

open scoped _root_.Classical in
private theorem rootChar_eq_one_iff_even {L : Type} [Field L] (h2 : (2 : L) ≠ 0)
    {a : Fin Tag.E7.rank → Lˣ} (ha : ∀ i, a i = 1 ∨ a i = -1)
    (v : Fin Tag.E7.rank → ℤ) :
    rootChar a v = 1 ↔ Even (∑ i ∈ Finset.univ.filter (fun i => a i = -1), v i) := by
  rw [rootChar_sign_eq ha v, neg_one_zpow_eq_ite]
  by_cases h : Even (∑ i ∈ Finset.univ.filter (fun i => a i = -1), v i)
  · simp [h]
  · simp [h, neg_one_units_ne_one h2]

section Sign

private theorem rootFinset_filter_card_eq_natCard (S : Finset (Fin Tag.E7.rank)) :
    Nat.card {α : {v : Fin Tag.E7.rank → ℤ // IsRoot .E7 v} // Even (∑ i ∈ S, α.1 i)} =
      ((rootFinset .E7).filter fun α => Even (∑ i ∈ S, α i)).card := by
  classical
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    { toFun := fun γ => ⟨γ.1.1, Finset.mem_filter.2 ⟨mem_rootFinset.2 γ.1.2, γ.2⟩⟩
      invFun := fun v => ⟨⟨v.1, mem_rootFinset.1 (Finset.mem_filter.1 v.2).1⟩,
        (Finset.mem_filter.1 v.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem e7_sign_fixed_finrank_ge {L : Type} [Field L] (h2 : (2 : L) ≠ 0)
    (a : Fin Tag.E7.rank → Lˣ) (ha : ∀ i, a i = 1 ∨ a i = -1) :
    63 ≤ Module.finrank L (fixSpace (rootDiag a)) := by
  classical
  let S : Finset (Fin Tag.E7.rank) := Finset.univ.filter fun i => a i = -1
  have hdim : Module.finrank L (LinearMap.ker (rootDiag a - 1)) =
      Tag.E7.rank + ((rootFinset .E7).filter fun α => rootChar a α = 1).card := by
    have h :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.finrank_ker_rootDiag_sub_one_card
        (τ := .E7) (K := L) a
    rw [h]
  have hfilter : ((rootFinset .E7).filter fun α => rootChar a α = 1) =
      ((rootFinset .E7).filter fun α => Even (∑ i ∈ S, α i)) := by
    apply Finset.filter_congr
    intro α _
    exact rootChar_eq_one_iff_even h2 ha α
  rw [hfilter] at hdim
  have hcard := e7_even_root_count_ge S
  rw [rootFinset_filter_card_eq_natCard S] at hcard
  have hmain : 63 ≤ Module.finrank L (LinearMap.ker (rootDiag a - 1)) := by
    rw [hdim]
    have hrank : Tag.E7.rank = 7 := rfl
    omega
  exact hmain

end Sign

end CFSG.LieType.Chevalley

end
