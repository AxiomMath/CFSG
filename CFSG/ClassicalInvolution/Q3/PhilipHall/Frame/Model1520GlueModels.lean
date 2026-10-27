module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520GlueSpin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Tags
public import CFSG.ClassicalInvolution.ModelFacts.TG3OrthTags
public import CFSG.ClassicalInvolution.ModelFacts.TG3Models

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal 
  CFSG.ClassicalInvolution.ModelFacts.TG3
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonalAut
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

section Models


private theorem model1520_odd_aux {n : ℕ} (hn3 : 3 ≤ n)
    (M : LieUniversal)
    (hM : M = ⟨spinGroup (quadOdd n 𝔽₃), oddDatum n 𝔽₃⟩)
    (hsingle : ModelFacts.FundamentalSingleClass .POmegaOdd M.D)
    (hG3 : ∀ R ∈ ModelFacts.fundamentalSubgroups .POmegaOdd M.D, ModelFacts.Gen3 R)
    (hlong : ∀ k : Fin M.D.rank, k.val + 1 < n → ModelFacts.IsLongestRoot M.D (Pi.single k 1))
    (hsl2 : ∀ R ∈ ModelFacts.fundamentalSubgroups .POmegaOdd M.D, Nonempty (R ≃* SL(2, 𝔽₃)))
    (hfin : Finite M.K) {G : Type} [Group G] [Finite G] {X : Subgroup G} (ψ : M.K →* ↥X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center M.K) {R : Subgroup M.K}
    (hR : R ∈ ModelFacts.fundamentalSubgroups .POmegaOdd M.D) (e : R ≃* SL(2, 𝔽₃)) :
    Model1520 X ((ψ (sl2Inv e) : ↥X) : G) := by
  subst hM
  have hodd := odd_natCard_galoisField_three
  have h3 : Nat.card 𝔽₃ = 3 := natCard_galoisField_three
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_three
  have hn0 : 0 < n := by omega
  have : Finite (spinGroup (quadOdd n 𝔽₃)) := hfin
  have ctx := spinCtx3_odd hn3 ⟨0, hn0⟩ rfl hsingle (hlong ⟨0, hn0⟩ (by show 0 + 1 < n; omega)) hG3
    hsl2
  have hQ := (regular_quadOdd (K := 𝔽₃) h2 hn3)
  have hOD : orthDerived (quadOdd n 𝔽₃) = elementaryGroup (quadOdd n 𝔽₃) :=
    (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ.1 hQ.2).1
  have hind : ∀ α : MulAut (ProjOrthDerived (quadOdd n 𝔽₃)),
      InducedBySemilinear (quadOdd n 𝔽₃) α := by
    intro α
    refine inducedBySemilinear_of_similarity (coordinateOddIsometry n 𝔽₃).toLinearEquiv 1
      (fun v => ?_) (inducedBySemilinear_of_image_eq_top (by omega) _
        (matrixProjectiveImage_eq_top_odd 𝔽₃ n hn3 (ringChar_ne_two_of_card_eq_three h3))) α
    rw [Units.val_one, one_mul]
    exact (coordinateOddIsometry n 𝔽₃).map_app v
  exact model1520_of_spinCtx3 ctx (isPerfect_spinGroup_quadOdd h2 hn3) hOD hind ψ hψ hker hR e

theorem model1520_of_modelUniv_odd {n : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n 3 1)
    {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (ψ : (ModelFacts.modelUniv .POmegaOdd n 3 1 Fact.out).K →* ↥X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (ModelFacts.modelUniv .POmegaOdd n 3 1 Fact.out).K)
    {R : Subgroup (ModelFacts.modelUniv .POmegaOdd n 3 1 Fact.out).K}
    (hR : R ∈ ModelFacts.fundamentalSubgroups .POmegaOdd (ModelFacts.modelUniv .POmegaOdd n 3 1 Fact.out).D)
    (e : R ≃* SL(2, 𝔽₃)) : Model1520 X ((ψ (sl2Inv e) : ↥X) : G) := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  refine model1520_odd_aux hn3 (ModelFacts.modelUniv .POmegaOdd n 3 1 Fact.out) rfl
    (ModelFacts.fundamentalSingleClass .POmegaOdd n 3 1 Fact.out trivial hadm (by decide) (by decide))
    (fun R hR => ModelFacts.gen3_of_mem_longestFundamental3 (t := .POmegaOdd) h3 trivial hadm (by decide)
      (by decide) (ModelFacts.fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR))
    (fun k hk => ModelFacts.isLongestRoot_single .POmegaOdd n 3 1 Fact.out trivial hadm k hk)
    (fun R hR => ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .POmegaOdd) trivial hadm
      (by decide) (by decide) hR)
    (ModelFacts.finite_modelUniv (t := .POmegaOdd) hp2 Nat.prime_three trivial hadm) ψ hψ hker hR e

private theorem model1520_minus_aux {n : ℕ} (hn4 : 4 ≤ n) (M : LieUniversal)
    (hM : M = ⟨spinGroup (quadMinus n 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
      minusDatum n (minusCoeffs_irr 3 1)⟩)
    (hsingle : ModelFacts.FundamentalSingleClass .POmegaMinus M.D)
    (hG3 : ∀ R ∈ ModelFacts.fundamentalSubgroups .POmegaMinus M.D, ModelFacts.Gen3 R)
    (hlong : ∀ k : Fin M.D.rank, k.val + 2 < n → ModelFacts.IsLongestRoot M.D (Pi.single k 1))
    (hsl2 : ∀ R ∈ ModelFacts.fundamentalSubgroups .POmegaMinus M.D,
      Nonempty (R ≃* SL(2, 𝔽₃)))
    (hfin : Finite M.K) {G : Type} [Group G] [Finite G] {X : Subgroup G} (ψ : M.K →* ↥X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center M.K) {R : Subgroup M.K}
    (hR : R ∈ ModelFacts.fundamentalSubgroups .POmegaMinus M.D) (e : R ≃* SL(2, 𝔽₃)) :
    Model1520 X ((ψ (sl2Inv e) : ↥X) : G) := by
  subst hM
  have h3 : Nat.card 𝔽₃ = 3 := natCard_galoisField_three
  have hirr := minusCoeffs_irr 3 1
  have hn0 : 0 < n - 1 := by omega
  have : Finite (spinGroup (quadMinus n 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) := hfin
  have ctx := spinCtx3_minus hirr hn4 ⟨0, hn0⟩ rfl hsingle
    (hlong ⟨0, hn0⟩ (by show 0 + 2 < n; omega)) hG3 hsl2
  have hQ := regular_quadMinus (K := 𝔽₃) (b := (minusCoeffs 3 1).1) (c := (minusCoeffs 3 1).2)
    hn4 hirr
  have hOD : orthDerived (quadMinus n 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) =
      elementaryGroup (quadMinus n 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) :=
    (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ.1 hQ.2).1
  have hind : ∀ α : MulAut (ProjOrthDerived
      (quadMinus n 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)),
      InducedBySemilinear (quadMinus n 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) α := by
    intro α
    refine inducedBySemilinear_of_similarity
      (coordinateMinusIsometry n 𝔽₃ (by omega) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toLinearEquiv
      1 (fun v => ?_) (inducedBySemilinear_of_image_eq_top (by omega) _
        (matrixProjectiveImage_eq_top_minus 𝔽₃ n hn4 _ _ hirr)) α
    rw [Units.val_one, one_mul]
    exact (coordinateMinusIsometry n 𝔽₃ (by omega) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2).map_app v
  exact model1520_of_spinCtx3 ctx (isPerfect_spinGroup_quadMinus hn4 hirr) hOD hind ψ hψ hker hR e

theorem model1520_of_modelUniv_minus {n : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 3 1)
    {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (ψ : (ModelFacts.modelUniv .POmegaMinus n 3 1 Fact.out).K →* ↥X)
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (ModelFacts.modelUniv .POmegaMinus n 3 1 Fact.out).K)
    {R : Subgroup (ModelFacts.modelUniv .POmegaMinus n 3 1 Fact.out).K}
    (hR : R ∈ ModelFacts.fundamentalSubgroups .POmegaMinus
      (ModelFacts.modelUniv .POmegaMinus n 3 1 Fact.out).D)
    (e : R ≃* SL(2, 𝔽₃)) : Model1520 X ((ψ (sl2Inv e) : ↥X) : G) := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  refine model1520_minus_aux hn4 (ModelFacts.modelUniv .POmegaMinus n 3 1 Fact.out) rfl
    (ModelFacts.fundamentalSingleClass .POmegaMinus n 3 1 Fact.out trivial hadm (by decide)
      (by decide))
    (fun R hR => ModelFacts.gen3_of_mem_longestFundamental3 (t := .POmegaMinus) h3 trivial hadm
      (by decide) (by decide)
      (ModelFacts.fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR))
    (fun k hk => ModelFacts.isLongestRoot_single .POmegaMinus n 3 1 Fact.out trivial hadm k hk)
    (fun R hR => ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .POmegaMinus)
      trivial hadm (by decide) (by decide) hR)
    (ModelFacts.finite_modelUniv (t := .POmegaMinus) hp2 Nat.prime_three trivial hadm) ψ hψ hker
    hR e

private theorem model1520_plus_aux {n : ℕ} (hn3 : 3 ≤ n) (hn4 : 4 ≤ n) (hn5 : 5 ≤ n)
    (M : LieUniversal) (hM : M = ⟨spinGroup (quadPlus n 𝔽₃), plusDatum n 𝔽₃ hn3⟩)
    (hsingle : ModelFacts.FundamentalSingleClass .POmegaPlus M.D)
    (hG3 : ∀ R ∈ ModelFacts.fundamentalSubgroups .POmegaPlus M.D, ModelFacts.Gen3 R)
    (hlong : ∀ k : Fin M.D.rank, ModelFacts.IsLongestRoot M.D (Pi.single k 1))
    (hsl2 : ∀ R ∈ ModelFacts.fundamentalSubgroups .POmegaPlus M.D, Nonempty (R ≃* SL(2, 𝔽₃)))
    (hfin : Finite M.K) {G : Type} [Group G] [Finite G] {X : Subgroup G} (ψ : M.K →* ↥X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center M.K) {R : Subgroup M.K}
    (hR : R ∈ ModelFacts.fundamentalSubgroups .POmegaPlus M.D) (e : R ≃* SL(2, 𝔽₃)) :
    Model1520 X ((ψ (sl2Inv e) : ↥X) : G) := by
  subst hM
  have h3 : Nat.card 𝔽₃ = 3 := natCard_galoisField_three
  have : Finite (spinGroup (quadPlus n 𝔽₃)) := hfin
  have ctx := spinCtx3_plus hn3 hn4 hsingle hlong hG3 hsl2
  have hQ := regular_quadPlus (K := 𝔽₃) hn3
  have hOD : orthDerived (quadPlus n 𝔽₃) = elementaryGroup (quadPlus n 𝔽₃) :=
    (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ.1 hQ.2).1
  have hind : ∀ α : MulAut (ProjOrthDerived (quadPlus n 𝔽₃)),
      InducedBySemilinear (quadPlus n 𝔽₃) α := by
    intro α
    refine inducedBySemilinear_of_similarity (coordinatePlusIsometry n 𝔽₃).toLinearEquiv 1
      (fun v => ?_) (inducedBySemilinear_of_image_eq_top (by omega) _
        (matrixProjectiveImage_eq_top_plus 𝔽₃ n hn5)) α
    rw [Units.val_one, one_mul]
    exact (coordinatePlusIsometry n 𝔽₃).map_app v
  exact model1520_of_spinCtx3 ctx (isPerfect_spinGroup_quadPlus hn3) hOD hind ψ hψ hker hR e

theorem model1520_of_modelUniv_plus {n : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n 3 1)
    (hn5 : 5 ≤ n) {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (ψ : (ModelFacts.modelUniv .POmegaPlus n 3 1 Fact.out).K →* ↥X)
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (ModelFacts.modelUniv .POmegaPlus n 3 1 Fact.out).K)
    {R : Subgroup (ModelFacts.modelUniv .POmegaPlus n 3 1 Fact.out).K}
    (hR : R ∈ ModelFacts.fundamentalSubgroups .POmegaPlus
      (ModelFacts.modelUniv .POmegaPlus n 3 1 Fact.out).D)
    (e : R ≃* SL(2, 𝔽₃)) : Model1520 X ((ψ (sl2Inv e) : ↥X) : G) := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  refine model1520_plus_aux hn3 hn4 hn5 (ModelFacts.modelUniv .POmegaPlus n 3 1 Fact.out)
    (ModelFacts.modelUniv_POmegaPlus hn3)
    (ModelFacts.fundamentalSingleClass .POmegaPlus n 3 1 Fact.out trivial hadm (by decide)
      (by decide))
    (fun R hR => ModelFacts.gen3_of_mem_longestFundamental3 (t := .POmegaPlus) h3 trivial hadm
      (by decide) (by decide)
      (ModelFacts.fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR))
    (fun k => ModelFacts.isLongestRoot_single .POmegaPlus n 3 1 Fact.out trivial hadm k trivial)
    (fun R hR => ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .POmegaPlus)
      trivial hadm (by decide) (by decide) hR)
    (ModelFacts.finite_modelUniv (t := .POmegaPlus) hp2 Nat.prime_three trivial hadm) ψ hψ hker
    hR e

end Models

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux
