module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTailCriterion
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneOddDerivationE6
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneOddDerivationE7
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneOddDerivationE8
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneAnnihilatorTails
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneEInnerTwo

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_card_eq_two_pow_eClasses (K : Type*) [Field K] [Finite K] [CharP K 2] :
    ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

section Representatives


theorem list_prod_map_pinnedX_mem_adjointGroup {τ : Tag} {K : Type} [Field K]
    (F : List (Fin τ.rank → ℤ)) : (F.map fun σ => pinnedX τ K σ 1).prod ∈ adjointGroup τ K :=
  list_prod_mem fun _ hx => by
    obtain ⟨σ, -, rfl⟩ := List.mem_map.1 hx
    exact pinnedX_mem_adjointGroup _ _

@[expose] def innerRepsE6 (K : Type) [Field K] : Set (adjointGroup .E6 K) :=
  {⟨pinnedX .E6 K (highRoot .E6) 1, pinnedX_mem_adjointGroup _ _⟩,
    ⟨(oddDerivE6YFrame.map fun σ => pinnedX .E6 K σ 1).prod,
      list_prod_map_pinnedX_mem_adjointGroup _⟩,
    ⟨(oddDerivE6ZFrame.map fun σ => pinnedX .E6 K σ 1).prod,
      list_prod_map_pinnedX_mem_adjointGroup _⟩}

@[expose] def innerRepsE7 (K : Type) [Field K] : Set (adjointGroup .E7 K) :=
  {⟨pinnedX .E7 K (highRoot .E7) 1, pinnedX_mem_adjointGroup _ _⟩,
    ⟨(oddDerivE7YFrame.map fun σ => pinnedX .E7 K σ 1).prod,
      list_prod_map_pinnedX_mem_adjointGroup _⟩,
    ⟨(oddDerivE7ZFrame.map fun σ => pinnedX .E7 K σ 1).prod,
      list_prod_map_pinnedX_mem_adjointGroup _⟩,
    ⟨(oddDerivE7UFrame.map fun σ => pinnedX .E7 K σ 1).prod,
      list_prod_map_pinnedX_mem_adjointGroup _⟩,
    ⟨(oddDerivE7VFrame.map fun σ => pinnedX .E7 K σ 1).prod,
      list_prod_map_pinnedX_mem_adjointGroup _⟩}

@[expose] def innerRepsE8 (K : Type) [Field K] : Set (adjointGroup .E8 K) :=
  {⟨pinnedX .E8 K (highRoot .E8) 1, pinnedX_mem_adjointGroup _ _⟩,
    ⟨(oddDerivE8YFrame.map fun σ => pinnedX .E8 K σ 1).prod,
      list_prod_map_pinnedX_mem_adjointGroup _⟩,
    ⟨(oddDerivE8ZFrame.map fun σ => pinnedX .E8 K σ 1).prod,
      list_prod_map_pinnedX_mem_adjointGroup _⟩,
    ⟨(oddDerivE8UFrame.map fun σ => pinnedX .E8 K σ 1).prod,
      list_prod_map_pinnedX_mem_adjointGroup _⟩}

end Representatives

@[expose] def annihL_E7_u : List (Fin Tag.E7.rank → ℤ) :=
  [![0, 1, 1, 2, 2, 2, 1],
    ![1, 1, 1, 2, 2, 1, 1],
    ![1, 1, 2, 2, 1, 1, 1],
    ![1, 2, 2, 4, 3, 2, 1],
    ![1, 2, 3, 4, 3, 2, 1],
    ![2, 2, 3, 4, 3, 2, 1]]

theorem annListCheck_E7_u :
    annListCheck .E7 17 (oddDerivE7UDeriv.map Prod.fst) annihL_E7_u = true := by
  decide +kernel

@[expose] def annihL_E7_v : List (Fin Tag.E7.rank → ℤ) :=
  [![0, 1, 1, 2, 2, 2, 1],
    ![1, 1, 1, 2, 2, 1, 1],
    ![1, 1, 2, 2, 1, 1, 1],
    ![1, 2, 2, 3, 2, 1, 0],
    ![1, 2, 2, 3, 2, 1, 1],
    ![1, 2, 2, 3, 2, 2, 1],
    ![1, 2, 2, 3, 3, 2, 1],
    ![1, 2, 2, 4, 3, 2, 1],
    ![1, 2, 3, 4, 3, 2, 1],
    ![2, 2, 3, 4, 3, 2, 1]]

theorem annListCheck_E7_v :
    annListCheck .E7 17 (oddDerivE7VDeriv.map Prod.fst) annihL_E7_v = true := by
  decide +kernel

variable {K : Type} [Field K]


theorem innerCentralizerCriterion_E6_x [Finite K] [CharP K 2] :
    InnerCentralizerCriterion
      (⟨pinnedX .E6 K (highRoot .E6) 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .E6 K) := by
  obtain ⟨f, hf, hK⟩ := exists_card_eq_two_pow_eClasses K
  exact innerCentralizerCriterion_E6_longRoot hf hK

theorem innerCentralizerCriterion_E7_x [Finite K] [CharP K 2] :
    InnerCentralizerCriterion
      (⟨pinnedX .E7 K (highRoot .E7) 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .E7 K) := by
  obtain ⟨f, hf, hK⟩ := exists_card_eq_two_pow_eClasses K
  exact innerCentralizerCriterion_E7_longRoot hf hK

theorem innerCentralizerCriterion_E8_x [Finite K] [CharP K 2] :
    InnerCentralizerCriterion
      (⟨pinnedX .E8 K (highRoot .E8) 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .E8 K) := by
  obtain ⟨f, hf, hK⟩ := exists_card_eq_two_pow_eClasses K
  exact innerCentralizerCriterion_E8_longRoot hf hK


theorem innerCentralizerCriterion_E6_y [Finite K] [CharP K 2] :
    InnerCentralizerCriterion
      (⟨(oddDerivE6YFrame.map fun σ => pinnedX .E6 K σ 1).prod,
        list_prod_map_pinnedX_mem_adjointGroup _⟩ : adjointGroup .E6 K) :=
  innerCentralizerCriterion_E_of_heightSeries (Or.inl rfl) (h := 4) (by norm_num) (by decide)
    (heightSeries_le_closure_odd_E6_y rfl)
    fun _ hu hc _ => sq_eq_one_of_commute_heightSeries_E6_four hu hc

theorem innerCentralizerCriterion_E6_z [Finite K] [CharP K 2] :
    InnerCentralizerCriterion
      (⟨(oddDerivE6ZFrame.map fun σ => pinnedX .E6 K σ 1).prod,
        list_prod_map_pinnedX_mem_adjointGroup _⟩ : adjointGroup .E6 K) :=
  innerCentralizerCriterion_E_of_heightSeries (Or.inl rfl) (h := 5) (by norm_num) (by decide)
    (heightSeries_le_closure_odd_E6_z rfl)
    fun _ hu hc _ => sq_eq_one_of_commute_heightSeries_E6_five hu hc

theorem innerCentralizerCriterion_E7_y [Finite K] [CharP K 2] :
    InnerCentralizerCriterion
      (⟨(oddDerivE7YFrame.map fun σ => pinnedX .E7 K σ 1).prod,
        list_prod_map_pinnedX_mem_adjointGroup _⟩ : adjointGroup .E7 K) :=
  innerCentralizerCriterion_E_of_heightSeries (Or.inr (Or.inl rfl)) (h := 5) (by norm_num)
    (by decide) (heightSeries_le_closure_odd_E7_y rfl)
    fun _ hu hc _ => sq_eq_one_of_commute_heightSeries_E7_five hu hc

theorem innerCentralizerCriterion_E7_z [Finite K] [CharP K 2] :
    InnerCentralizerCriterion
      (⟨(oddDerivE7ZFrame.map fun σ => pinnedX .E7 K σ 1).prod,
        list_prod_map_pinnedX_mem_adjointGroup _⟩ : adjointGroup .E7 K) :=
  innerCentralizerCriterion_E_of_heightSeries (Or.inr (Or.inl rfl)) (h := 7) (by norm_num)
    (by decide) (heightSeries_le_closure_odd_E7_z rfl)
    fun _ hu hc _ => sq_eq_one_of_commute_heightSeries_E7_seven hu hc

theorem innerCentralizerCriterion_E7_u [Finite K] [CharP K 2] :
    InnerCentralizerCriterion
      (⟨(oddDerivE7UFrame.map fun σ => pinnedX .E7 K σ 1).prod,
        list_prod_map_pinnedX_mem_adjointGroup _⟩ : adjointGroup .E7 K) :=
  innerCentralizerCriterion_E_of_heightSeries_of_pinnedX (Or.inr (Or.inl rfl)) (h := 10)
    (S := {δ | δ ∈ oddDerivE7UDeriv.map Prod.fst}) (by norm_num) (by decide)
    (heightSeries_le_closure_odd_E7_u rfl)
    (fun _ hδ => rootSpan_le_closure_odd_E7_u
      (t := ⟨_, list_prod_map_pinnedX_mem_adjointGroup oddDerivE7UFrame⟩) rfl _
      (pinnedX_mem_rootSpan hδ 1))
    fun _ hz hc => sq_eq_one_of_commute_of_annListCheck (Or.inr (Or.inr (Or.inl rfl)))
      annListCheck_E7_u hz hc

theorem innerCentralizerCriterion_E7_v [Finite K] [CharP K 2] :
    InnerCentralizerCriterion
      (⟨(oddDerivE7VFrame.map fun σ => pinnedX .E7 K σ 1).prod,
        list_prod_map_pinnedX_mem_adjointGroup _⟩ : adjointGroup .E7 K) :=
  innerCentralizerCriterion_E_of_heightSeries_of_pinnedX (Or.inr (Or.inl rfl)) (h := 10)
    (S := {δ | δ ∈ oddDerivE7VDeriv.map Prod.fst}) (by norm_num) (by decide)
    (heightSeries_le_closure_odd_E7_v rfl)
    (fun _ hδ => rootSpan_le_closure_odd_E7_v
      (t := ⟨_, list_prod_map_pinnedX_mem_adjointGroup oddDerivE7VFrame⟩) rfl _
      (pinnedX_mem_rootSpan hδ 1))
    fun _ hz hc => sq_eq_one_of_commute_of_annListCheck (Or.inr (Or.inr (Or.inl rfl)))
      annListCheck_E7_v hz hc

theorem innerCentralizerCriterion_E8_y [Finite K] [CharP K 2] :
    InnerCentralizerCriterion
      (⟨(oddDerivE8YFrame.map fun σ => pinnedX .E8 K σ 1).prod,
        list_prod_map_pinnedX_mem_adjointGroup _⟩ : adjointGroup .E8 K) :=
  innerCentralizerCriterion_E_of_heightSeries (Or.inr (Or.inr rfl)) (h := 7) (by norm_num)
    (by decide) (heightSeries_le_closure_odd_E8_y rfl)
    fun _ hu hc _ => sq_eq_one_of_commute_heightSeries_E8_seven hu hc

theorem innerCentralizerCriterion_E8_z [Finite K] [CharP K 2] :
    InnerCentralizerCriterion
      (⟨(oddDerivE8ZFrame.map fun σ => pinnedX .E8 K σ 1).prod,
        list_prod_map_pinnedX_mem_adjointGroup _⟩ : adjointGroup .E8 K) :=
  innerCentralizerCriterion_E_of_heightSeries (Or.inr (Or.inr rfl)) (h := 11) (by norm_num)
    (by decide) (heightSeries_le_closure_odd_E8_z rfl)
    fun _ hu hc _ => sq_eq_one_of_commute_heightSeries_E8_eleven hu hc

theorem innerCentralizerCriterion_E8_u [Finite K] [CharP K 2] :
    InnerCentralizerCriterion
      (⟨(oddDerivE8UFrame.map fun σ => pinnedX .E8 K σ 1).prod,
        list_prod_map_pinnedX_mem_adjointGroup _⟩ : adjointGroup .E8 K) :=
  innerCentralizerCriterion_E_of_heightSeries (Or.inr (Or.inr rfl)) (h := 13) (by norm_num)
    (by decide) (heightSeries_le_closure_odd_E8_u rfl)
    fun _ hu hc _ => sq_eq_one_of_commute_heightSeries_E8_thirteen hu hc

theorem innerCentralizerCriterion_innerRepsE6 [Finite K] [CharP K 2] :
    ∀ s ∈ innerRepsE6 K, InnerCentralizerCriterion s := by
  rintro s (rfl | rfl | rfl)
  · exact innerCentralizerCriterion_E6_x
  · exact innerCentralizerCriterion_E6_y
  · exact innerCentralizerCriterion_E6_z

theorem innerCentralizerCriterion_innerRepsE7 [Finite K] [CharP K 2] :
    ∀ s ∈ innerRepsE7 K, InnerCentralizerCriterion s := by
  rintro s (rfl | rfl | rfl | rfl | rfl)
  · exact innerCentralizerCriterion_E7_x
  · exact innerCentralizerCriterion_E7_y
  · exact innerCentralizerCriterion_E7_z
  · exact innerCentralizerCriterion_E7_u
  · exact innerCentralizerCriterion_E7_v

theorem innerCentralizerCriterion_innerRepsE8 [Finite K] [CharP K 2] :
    ∀ s ∈ innerRepsE8 K, InnerCentralizerCriterion s := by
  rintro s (rfl | rfl | rfl | rfl)
  · exact innerCentralizerCriterion_E8_x
  · exact innerCentralizerCriterion_E8_y
  · exact innerCentralizerCriterion_E8_z
  · exact innerCentralizerCriterion_E8_u

theorem innerInvolutionInput_E6_of_classes [Finite K] [CharP K 2]
    (hrep : ∀ t : adjointGroup .E6 K, orderOf (MulAut.conj t) = 2 →
      ∃ ψ : MulAut (adjointGroup .E6 K), ∃ s ∈ innerRepsE6 K, ψ s = t) :
    InnerInvolutionInput (adjointGroup .E6 K) :=
  innerInvolutionInput_of_representatives innerCentralizerCriterion_innerRepsE6 hrep

theorem innerInvolutionInput_E7_of_classes [Finite K] [CharP K 2]
    (hrep : ∀ t : adjointGroup .E7 K, orderOf (MulAut.conj t) = 2 →
      ∃ ψ : MulAut (adjointGroup .E7 K), ∃ s ∈ innerRepsE7 K, ψ s = t) :
    InnerInvolutionInput (adjointGroup .E7 K) :=
  innerInvolutionInput_of_representatives innerCentralizerCriterion_innerRepsE7 hrep

theorem innerInvolutionInput_E8_of_classes [Finite K] [CharP K 2]
    (hrep : ∀ t : adjointGroup .E8 K, orderOf (MulAut.conj t) = 2 →
      ∃ ψ : MulAut (adjointGroup .E8 K), ∃ s ∈ innerRepsE8 K, ψ s = t) :
    InnerInvolutionInput (adjointGroup .E8 K) :=
  innerInvolutionInput_of_representatives innerCentralizerCriterion_innerRepsE8 hrep

theorem innerInvolutionInput_E6_of_classes' {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hrep : ∀ t : adjointGroup .E6 K, orderOf (MulAut.conj t) = 2 →
      ∃ ψ : MulAut (adjointGroup .E6 K), ∃ s ∈ innerRepsE6 K, ψ s = t) :
    InnerInvolutionInput (adjointGroup .E6 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  exact innerInvolutionInput_E6_of_classes hrep

theorem innerInvolutionInput_E7_of_classes' {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hrep : ∀ t : adjointGroup .E7 K, orderOf (MulAut.conj t) = 2 →
      ∃ ψ : MulAut (adjointGroup .E7 K), ∃ s ∈ innerRepsE7 K, ψ s = t) :
    InnerInvolutionInput (adjointGroup .E7 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  exact innerInvolutionInput_E7_of_classes hrep

theorem innerInvolutionInput_E8_of_classes' {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hrep : ∀ t : adjointGroup .E8 K, orderOf (MulAut.conj t) = 2 →
      ∃ ψ : MulAut (adjointGroup .E8 K), ∃ s ∈ innerRepsE8 K, ψ s = t) :
    InnerInvolutionInput (adjointGroup .E8 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  exact innerInvolutionInput_E8_of_classes hrep

end CFSG.SeitzReduction
