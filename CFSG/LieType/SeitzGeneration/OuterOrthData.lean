module

public import CFSG.LieType.SeitzGeneration.OuterOrthGeneric
public import CFSG.RankThree.PartOne.KC.LinearSubfieldInclusion
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescent
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldBY

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix Subgroup CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.Assembly.LowTwoRank (StatedProj StatedOmega StatedQuadOdd StatedQuadPlus
  StatedLieAdmissible StatedClassicalModel)

section Odd

variable {n ℓ f p : ℕ} {K : Type} [Field K] [Finite K]

theorem fieldAutData_odd (hpair : SubfieldPairOmegaOdd)
    (hadm : StatedLieAdmissible .POmegaOdd n ℓ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hp3 : 3 < p) (hpℓ : p ≠ ℓ) :
    FieldAutData (matrixProjectiveDerived (coordinateQuadOdd n K)) p := by
  classical
  obtain ⟨hℓ, hf, hn3, hℓ2⟩ := id hadm
  have hM : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadOdd n K))) .POmegaOdd n ℓ f :=
    ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hg : OrthogonalGates (coordinateQuadOdd n K) f :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaOdd (Or.inl rfl) n ℓ f hM
      K hK (MulEquiv.refl _)
  refine fieldAutData_matrixProjectiveDerived _ hℓ hf hK hp hp3 hg
    (fun σ _ => coordinateQuadOdd_fieldAut n σ) ?_ ?_
  · intro α hα
    obtain ⟨hE, hD⟩ := outer_mem_E_not_D hg hp hp3 hα
    have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent _ .POmegaOdd (Or.inl rfl)
      n ℓ f p hM hp hp3 hpℓ K hK (MulEquiv.refl _) α hE hD hα.1
    exact exists_conj_fieldAutT_of_descent _ hE hdesc (fun σ _ => coordinateQuadOdd_fieldAut n σ)
      (fun U Q₀ _ hdisp => by
        obtain ⟨ν, S₀, -, -, S, ν', hSQ, -, hSA, -⟩ := hdisp
        exact ⟨S, ν', hSQ, hSA⟩)
  · intro σ hσ
    obtain ⟨hpf, hcardk⟩ := card_semilinearFixedSubfield hℓ hf hK hσ
    obtain ⟨e, rfl⟩ := hpf
    have he : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · rw [h0, mul_zero] at hf
        omega
      · exact h0
    rw [Nat.mul_div_cancel_left e hp.pos] at hcardk
    have hK' : Nat.card K = ℓ ^ (e * p) := by rw [hK, mul_comm]
    have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
    obtain ⟨-, hconc⟩ :=
      orthogonal_prime_subfield_fixed_group_and_full_centralizer_unconditional .POmegaOdd
        (Or.inl rfl) n ℓ e p ⟨hℓ, he, hn3, hℓ2⟩ hp hp3 hpℓ K (semilinearFixedSubfield σ) hcardk hK'
        σ hσ hσk
    exact fixedGood_of_subfieldConclusion hconc
      (hpair n ℓ e p hn3 hℓ hℓ2 he hp hp3 hpℓ K (semilinearFixedSubfield σ) hcardk hK')

end Odd

section Plus

variable {n ℓ f p : ℕ} {K : Type} [Field K] [Finite K]

theorem fieldAutData_plus (hpair : SubfieldPairOmegaPlus)
    (hadm : StatedLieAdmissible .POmegaPlus n ℓ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hp3 : 3 < p) (hpℓ : p ≠ ℓ) :
    FieldAutData (matrixProjectiveDerived (coordinateQuadPlus n K)) p := by
  classical
  obtain ⟨hℓ, hf, hn4⟩ := id hadm
  have hM : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus n K))) .POmegaPlus n ℓ
      f := ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hg : OrthogonalGates (coordinateQuadPlus n K) f :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaPlus (Or.inr (Or.inl rfl))
      n ℓ f hM K hK (MulEquiv.refl _)
  refine fieldAutData_matrixProjectiveDerived _ hℓ hf hK hp hp3 hg
    (fun σ _ => coordinateQuadPlus_fieldAut n σ) ?_ ?_
  · intro α hα
    obtain ⟨hE, hD⟩ := outer_mem_E_not_D hg hp hp3 hα
    have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent _ .POmegaPlus
      (Or.inr (Or.inl rfl)) n ℓ f p hM hp hp3 hpℓ K hK (MulEquiv.refl _) α hE hD hα.1
    exact exists_conj_fieldAutT_of_descent _ hE hdesc (fun σ _ => coordinateQuadPlus_fieldAut n σ)
      (fun U Q₀ _ hdisp => by
        obtain ⟨ν, S₀, -, -, S, ν', hSQ, -, hSA, -⟩ := hdisp
        exact ⟨S, ν', hSQ, hSA⟩)
  · intro σ hσ
    obtain ⟨hpf, hcardk⟩ := card_semilinearFixedSubfield hℓ hf hK hσ
    obtain ⟨e, rfl⟩ := hpf
    have he : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · rw [h0, mul_zero] at hf
        omega
      · exact h0
    rw [Nat.mul_div_cancel_left e hp.pos] at hcardk
    have hK' : Nat.card K = ℓ ^ (e * p) := by rw [hK, mul_comm]
    have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
    obtain ⟨-, hconc⟩ :=
      orthogonal_prime_subfield_fixed_group_and_full_centralizer_unconditional .POmegaPlus
        (Or.inr (Or.inl rfl)) n ℓ e p ⟨hℓ, he, hn4⟩ hp hp3 hpℓ K (semilinearFixedSubfield σ)
        hcardk hK' σ hσ hσk
    exact fixedGood_of_subfieldConclusion hconc
      (hpair n ℓ e p hn4 hℓ he hp hp3 hpℓ K (semilinearFixedSubfield σ) hcardk hK')

end Plus

end CFSG.LieType.SeitzGeneration
