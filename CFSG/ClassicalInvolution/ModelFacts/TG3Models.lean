module

public import CFSG.ClassicalInvolution.ModelFacts.TG3OrthTags
public import CFSG.ClassicalInvolution.Uniform.U5Model
public import CFSG.ClassicalInvolution.ModelFacts.CF3All
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.Q3CSBase
public import CFSG.ClassicalInvolution.Q3.Q3DThm5
public import CFSG.ClassicalInvolution.Q3.Q3TAxis
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap
public import CFSG.ClassicalInvolution.Uniform.U3Thm8
public import CFSG.ClassicalInvolution.Uniform.U5Alpha
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts.TG3

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1

section Ctx

variable {ι : Type} [Fintype ι] {Q : QuadraticForm 𝔽₃ (ι → 𝔽₃)}
  {𝓕 : Set (Subgroup (spinGroup Q))}

theorem compGen3Twin_of_ctx [Finite (spinGroup Q)] (c : SpinCtx3 Q 𝓕)
    (hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg 𝔽₃ * F₁.La (-1) → False) :
    CompGen3Twin (⟨spinGroup Q, 𝓕⟩ : Q3.CompData) := by
  intro X _ _ ψ hker R₁ hR₁ R₂ hR₂ h24₁ h24₂ hne hcomm z hz₁ hz₂ A hA hAle hzA
  exact twin_generation_orth c hproj ψ hker hR₁ hR₂ h24₁ h24₂ hne hcomm hz₁ hz₂ hA hAle hzA

end Ctx

section Models


theorem compGen3Twin_pOmegaOdd {n : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n 3 1) :
    CompGen3Twin (compModel 3 1 .POmegaOdd n) := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hM : modelUniv .POmegaOdd n 3 1 Fact.out =
      ⟨spinGroup (quadOdd n (GaloisField 3 1)), oddDatum n (GaloisField 3 1)⟩ := rfl
  have hsingle : FundamentalSingleClass .POmegaOdd (modelUniv .POmegaOdd n 3 1 Fact.out).D :=
    fundamentalSingleClass .POmegaOdd n 3 1 Fact.out trivial hadm (by decide) (by decide)
  have hG3 : ∀ R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n 3 1 Fact.out).D,
      Gen3 R := fun R hR =>
    gen3_of_mem_longestFundamental3 (t := .POmegaOdd) h3 trivial hadm (by decide) (by decide)
      (fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR)
  have hlong : ∀ k : Fin (modelUniv .POmegaOdd n 3 1 Fact.out).D.rank, k.val + 1 < n →
      IsLongestRoot (modelUniv .POmegaOdd n 3 1 Fact.out).D (Pi.single k 1) :=
    fun k hk => isLongestRoot_single .POmegaOdd n 3 1 Fact.out trivial hadm k hk
  have hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n 3 1 Fact.out).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .POmegaOdd) trivial hadm (by decide)
      (by decide) hR
  have hfin : Finite (modelUniv .POmegaOdd n 3 1 Fact.out).K :=
    finite_modelUniv (t := .POmegaOdd) hp2 Nat.prime_three trivial hadm
  show CompGen3Twin ⟨(modelUniv .POmegaOdd n 3 1 Fact.out).K,
    fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n 3 1 Fact.out).D⟩
  generalize modelUniv .POmegaOdd n 3 1 Fact.out = M at hM hsingle hG3 hlong hsl2 hfin ⊢
  subst hM
  have hn0 : 0 < n := by omega
  have : Finite (spinGroup (quadOdd n (GaloisField 3 1))) := hfin
  exact compGen3Twin_of_ctx (spinCtx3_odd hn3 ⟨0, hn0⟩ rfl hsingle
    (hlong ⟨0, hn0⟩ (by show 0 + 1 < n; omega)) hG3 hsl2) hproj_odd

theorem compGen3Twin_pOmegaMinus {n : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 3 1) :
    CompGen3Twin (compModel 3 1 .POmegaMinus n) := by
  have hn4 : 4 ≤ n := hadm.2.2
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hM : modelUniv .POmegaMinus n 3 1 Fact.out =
      ⟨spinGroup (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
        minusDatum n (minusCoeffs_irr 3 1)⟩ := rfl
  have hsingle : FundamentalSingleClass .POmegaMinus (modelUniv .POmegaMinus n 3 1 Fact.out).D :=
    fundamentalSingleClass .POmegaMinus n 3 1 Fact.out trivial hadm (by decide) (by decide)
  have hG3 : ∀ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n 3 1 Fact.out).D,
      Gen3 R := fun R hR =>
    gen3_of_mem_longestFundamental3 (t := .POmegaMinus) h3 trivial hadm (by decide) (by decide)
      (fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR)
  have hlong : ∀ k : Fin (modelUniv .POmegaMinus n 3 1 Fact.out).D.rank, k.val + 2 < n →
      IsLongestRoot (modelUniv .POmegaMinus n 3 1 Fact.out).D (Pi.single k 1) :=
    fun k hk => isLongestRoot_single .POmegaMinus n 3 1 Fact.out trivial hadm k hk
  have hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n 3 1 Fact.out).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .POmegaMinus) trivial hadm (by decide)
      (by decide) hR
  have hfin : Finite (modelUniv .POmegaMinus n 3 1 Fact.out).K :=
    finite_modelUniv (t := .POmegaMinus) hp2 Nat.prime_three trivial hadm
  show CompGen3Twin ⟨(modelUniv .POmegaMinus n 3 1 Fact.out).K,
    fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n 3 1 Fact.out).D⟩
  generalize modelUniv .POmegaMinus n 3 1 Fact.out = M at hM hsingle hG3 hlong hsl2 hfin ⊢
  subst hM
  have hn0 : 0 < n - 1 := by omega
  have : Finite (spinGroup (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1
    (minusCoeffs 3 1).2)) := hfin
  exact compGen3Twin_of_ctx (spinCtx3_minus (minusCoeffs_irr 3 1) hn4 ⟨0, hn0⟩ rfl hsingle
    (hlong ⟨0, hn0⟩ (by show 0 + 2 < n; omega)) hG3 hsl2)
    (fun F₁ F₂ h => hproj_minus (minusCoeffs_irr 3 1) hn4 F₁ F₂ h)

theorem compGen3Twin_pOmegaPlus {n : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n 3 1)
    (hn5 : 5 ≤ n) : CompGen3Twin (compModel 3 1 .POmegaPlus n) := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hM : modelUniv .POmegaPlus n 3 1 Fact.out =
      ⟨spinGroup (quadPlus n (GaloisField 3 1)), plusDatum n (GaloisField 3 1) hn3⟩ :=
    (rfl : modelUniv .POmegaPlus n 3 1 Fact.out =
      ModelFacts.modelUniv .POmegaPlus n 3 1 Fact.out).trans (modelUniv_POmegaPlus hn3)
  have hsingle : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus n 3 1 Fact.out).D :=
    fundamentalSingleClass .POmegaPlus n 3 1 Fact.out trivial hadm (by decide) (by decide)
  have hG3 : ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n 3 1 Fact.out).D,
      Gen3 R := fun R hR =>
    gen3_of_mem_longestFundamental3 (t := .POmegaPlus) h3 trivial hadm (by decide) (by decide)
      (fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR)
  have hlong : ∀ k : Fin (modelUniv .POmegaPlus n 3 1 Fact.out).D.rank,
      IsLongestRoot (modelUniv .POmegaPlus n 3 1 Fact.out).D (Pi.single k 1) :=
    fun k => isLongestRoot_single .POmegaPlus n 3 1 Fact.out trivial hadm k trivial
  have hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n 3 1 Fact.out).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .POmegaPlus) trivial hadm (by decide)
      (by decide) hR
  have hfin : Finite (modelUniv .POmegaPlus n 3 1 Fact.out).K :=
    finite_modelUniv (t := .POmegaPlus) hp2 Nat.prime_three trivial hadm
  show CompGen3Twin ⟨(modelUniv .POmegaPlus n 3 1 Fact.out).K,
    fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n 3 1 Fact.out).D⟩
  generalize modelUniv .POmegaPlus n 3 1 Fact.out = M at hM hsingle hG3 hlong hsl2 hfin ⊢
  subst hM
  have : Finite (spinGroup (quadPlus n (GaloisField 3 1))) := hfin
  exact compGen3Twin_of_ctx (spinCtx3_plus hn3 hn4 hsingle hlong hG3 hsl2) (hproj_plus hn5)

end Models

end CFSG.ClassicalInvolution.ModelFacts.TG3
