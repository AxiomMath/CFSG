module

public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LSpin
public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LConj
public import CFSG.ClassicalInvolution.Q3.Q3TWY1
public import CFSG.ClassicalInvolution.ModelFacts.TG3OrthTags

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.ModelFacts.TG3 CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Generic (conjSub)
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1


theorem s4LinkModelLeafAt_odd3 : S4LinkModelLeafAt (CompData.model .POmegaOdd 3) := by
  have hadm : StatedLieAdmissible .POmegaOdd 3 3 1 :=
    ⟨Nat.prime_three, le_rfl, le_rfl, by norm_num⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_three
  have hM : modelUniv .POmegaOdd 3 3 1 Nat.prime_three =
      ⟨spinGroup (quadOdd 3 (GaloisField 3 1)), oddDatum 3 (GaloisField 3 1)⟩ := rfl
  have hsingle : FundamentalSingleClass .POmegaOdd (modelUniv .POmegaOdd 3 3 1 Nat.prime_three).D :=
    fundamentalSingleClass .POmegaOdd 3 3 1 Nat.prime_three trivial hadm (by decide) (by decide)
  have hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 3 3 1 Nat.prime_three).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .POmegaOdd) trivial hadm (by decide)
      (by decide) hR
  have hfin : Finite (modelUniv .POmegaOdd 3 3 1 Nat.prime_three).K :=
    finite_modelUniv (t := .POmegaOdd) hp2 Nat.prime_three trivial hadm
  have hconj : ∀ R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 3 3 1 Nat.prime_three).D,
      ∀ g : (modelUniv .POmegaOdd 3 3 1 Nat.prime_three).K, conjSub g R ∈
        fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 3 3 1 Nat.prime_three).D :=
    fun R hR g => S4L.conjSub_mem_fundamentalSubgroups _ hR g
  show S4LinkModelLeafAt ⟨(modelUniv .POmegaOdd 3 3 1 Nat.prime_three).K,
    fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 3 3 1 Nat.prime_three).D⟩
  generalize modelUniv .POmegaOdd 3 3 1 Nat.prime_three = M at hM hsingle hsl2 hfin hconj ⊢
  subst hM
  have hdim : Module.finrank 𝔽₃ (Fin 3 ⊕ Fin 3 ⊕ Unit → 𝔽₃) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
  have : Group.IsPerfect (spinGroup (quadOdd 3 𝔽₃)) := isPerfect_spinGroup_quadOdd h2 le_rfl
  exact S4L.s4LinkModelLeafAt_of_spin (quadOdd 3 𝔽₃) _ (nondegenerate_polarBilin_quadOdd 3 _ h2)
    (by rw [hdim]) this (range_spinAction_quadOdd h2 le_rfl) (Q3TWY.centralQuot3_odd le_rfl)
    hconj hsingle hsl2 (fun F₁ F₂ h => hproj_odd F₁ F₂ h)

end CFSG.ClassicalInvolution.Q3.Q3AM
