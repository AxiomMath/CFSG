module

public import CFSG.ClassicalInvolution.Q3.Q3T7E9OrthModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7E9

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.ModelFacts (Gen3)
open CFSG.ClassicalInvolution.ModelFacts.OrthAut (IsHypFam hypComb hypComb_injective map_hypComb)
open CFSG.ClassicalInvolution.Models.Transfer
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Count

variable {F : Type} [Field F] [Finite F]

theorem false_of_orth_quadMinus_four' (h2 : (2 : F) ≠ 0) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (F₀ F₁ : OFrame (quadMinus 4 F b c)) (h : F₁.span ≤ F₀.perp) : False := by
  classical
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have h4 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hv := isHypFam_of_orth F₀ F₁ h
  set v : Fin 4 → Bool → (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) := fun (i : Fin 4) (s : Bool) =>
      if s then ![F₀.e₁, F₀.e₂, F₁.e₁, F₁.e₂] i else ![F₀.f₁, F₀.f₂, F₁.f₁, F₁.f₂] i with hvdef
  let e' : Fin 4 × Bool ≃ Fin 4 ⊕ Fin 4 :=
    (Equiv.prodComm (Fin 4) Bool).trans (Equiv.boolProdEquivSum (Fin 4))
  let ψ₀ : (Fin 4 ⊕ Fin 4 → F) →ₗ[F] (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) :=
    (hypComb v).comp (LinearMap.funLeft F F e')
  have hψQ : ∀ w, quadMinus 4 F b c (ψ₀ w) = quadPlus 4 F w := by
    intro w
    show quadMinus 4 F b c (hypComb v (w ∘ e')) = _
    rw [map_hypComb hv, quadPlus_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    show w (e' (i, true)) * w (e' (i, false)) = _
    simp [e', Equiv.boolProdEquivSum, mul_comm]
  have hinj : Function.Injective ψ₀ :=
    (hypComb_injective hv).comp (LinearMap.funLeft_injective_of_surjective F F e' e'.surjective)
  have hdim : Module.finrank F (Fin 4 ⊕ Fin 4 → F) =
      Module.finrank F (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
    simp
  have hsurj : Function.Surjective ψ₀ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  have hcard : Nat.card {w : Fin 4 ⊕ Fin 4 → F // quadPlus 4 F w = 0} =
      Nat.card {x : (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) // quadMinus 4 F b c x = 0} :=
    Nat.card_congr ((Equiv.ofBijective ψ₀ ⟨hinj, hsurj⟩).subtypeEquiv fun w => by
      rw [show (Equiv.ofBijective ψ₀ ⟨hinj, hsurj⟩) w = ψ₀ w from rfl, hψQ w])
  have e1 : (Nat.card {w : Fin 4 ⊕ Fin 4 → F // quadPlus 4 F w = 0} : ℤ) =
      1 + ((Nat.card F : ℤ) ^ 4 - 1) * ((Nat.card F : ℤ) ^ 3 + 1) :=
    CFSG.ClassicalInvolution.card_singular_quadPlus 3
  have e2 : (Nat.card {x : (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) // quadMinus 4 F b c x = 0} :
      ℤ) = 1 + ((Nat.card F : ℤ) ^ 4 + 1) * ((Nat.card F : ℤ) ^ 3 - 1) :=
    CFSG.ClassicalInvolution.card_singular_quadMinus_of_two_ne_zero h2 hirr 3
  rw [hcard] at e1
  have hq : (2 : ℤ) ≤ (Nat.card F : ℤ) := by exact_mod_cast h4
  have key : ((Nat.card F : ℤ) ^ 4 - 1) * ((Nat.card F : ℤ) ^ 3 + 1) -
      ((Nat.card F : ℤ) ^ 4 + 1) * ((Nat.card F : ℤ) ^ 3 - 1) =
      2 * ((Nat.card F : ℤ) ^ 3 * ((Nat.card F : ℤ) - 1)) := by ring
  have hpos : 0 < (Nat.card F : ℤ) ^ 3 * ((Nat.card F : ℤ) - 1) :=
    mul_pos (pow_pos (by linarith) 3) (by linarith)
  linarith

end Count


theorem e189ModelAt_three_odd {n : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n 3 1) :
    E189ModelAt 3 1 .POmegaOdd n := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hodd := odd_card_galoisField_of_ne_two (p := 3) (e := 1) (by norm_num) le_rfl
  have h2 : (2 : GaloisField 3 1) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have hdim : Module.finrank (GaloisField 3 1) (Fin n ⊕ Fin n ⊕ Unit → GaloisField 3 1) =
      2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  have hgen : ∀ R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n 3 1 Fact.out).D,
      Gen3 R := fun R hR =>
    gen3_of_mem_fundamentalSubgroups_three (by simp [IsFundTag]) hadm (by decide) (by decide) hR
  show E189AtFam (spinGroup (quadOdd n (GaloisField 3 1)))
    (fundamentalSubgroups .POmegaOdd (oddDatum n (GaloisField 3 1)))
  refine e189AtFam_spin_of_ne8_three hodd (nondegenerate_polarBilin_quadOdd n _ h2) (by omega)
    (by omega) (centerScalar_quadOdd h2 hn3) _ hgen ?_ (fundCorr_odd_of_odd (by norm_num) le_rfl
      hadm).1
  intro R hR g
  exact conjSub_mem_fundamentalSubgroups hR g

theorem e189ModelAt_three_plus {n : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n 3 1) :
    E189ModelAt 3 1 .POmegaPlus n := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  have hodd := odd_card_galoisField_of_ne_two (p := 3) (e := 1) (by norm_num) le_rfl
  have hdim : Module.finrank (GaloisField 3 1) (Fin n ⊕ Fin n → GaloisField 3 1) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hgen : ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n 3 1 Fact.out).D,
      Gen3 R := fun R hR =>
    gen3_of_mem_fundamentalSubgroups_three (by simp [IsFundTag]) hadm (by decide) (by decide) hR
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus n (GaloisField 3 1)),
      plusDatum n (GaloisField 3 1) hn3⟩ → (∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, Gen3 R) →
      E189AtFam M.K (fundamentalSubgroups .POmegaPlus M.D) := by
    intro M hM hG
    subst hM
    by_cases hn : n = 4
    · subst hn
      exact e189AtFam_spin_of_eight_three hodd (nondegenerate_polarBilin_quadPlus 4 _)
        (by omega) (centerScalar_quadPlus hn3) _ hG
        (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
        (fundCorr_plus_of_odd (by norm_num) le_rfl hadm hn4).1
    · exact e189AtFam_spin_of_ne8_three hodd (nondegenerate_polarBilin_quadPlus n _) (by omega)
        (by omega) (centerScalar_quadPlus hn3) _ hG
        (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
        (fundCorr_plus_of_odd (by norm_num) le_rfl hadm hn4).1
  exact key _ (CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus hn3) hgen

theorem e189ModelAt_three_minus {n : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 3 1) :
    E189ModelAt 3 1 .POmegaMinus n := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hodd := odd_card_galoisField_of_ne_two (p := 3) (e := 1) (by norm_num) le_rfl
  have h2 : (2 : GaloisField 3 1) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have hdim : Module.finrank (GaloisField 3 1)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 3 1) = 2 * (n - 1) + 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    ring
  have hgen : ∀ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n 3 1 Fact.out).D,
      Gen3 R := fun R hR =>
    gen3_of_mem_fundamentalSubgroups_three (by simp [IsFundTag]) hadm (by decide) (by decide) hR
  show E189AtFam
    (spinGroup (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))
    (fundamentalSubgroups .POmegaMinus (Twisted.minusDatum n (minusCoeffs_irr 3 1)))
  by_cases hn : n = 4
  · subst hn
    refine e189AtFam_spin_of_noOrth_three hodd
      (nondegenerate_polarBilin_quadMinus_of_finite 4 _ (minusCoeffs_irr 3 1)) (by omega)
      (centerScalar_quadMinus le_rfl (minusCoeffs_irr 3 1))
      (fun F₀ F₁ hF => false_of_orth_quadMinus_four' h2 (minusCoeffs_irr 3 1) F₀ F₁ hF) _ hgen ?_
      (fundCorr_minus_of_odd (by norm_num) le_rfl hadm).1
    intro R hR g
    exact conjSub_mem_fundamentalSubgroups hR g
  · refine e189AtFam_spin_of_ne8_three hodd
      (nondegenerate_polarBilin_quadMinus_of_finite n _ (minusCoeffs_irr 3 1)) (by omega)
      (by omega) (centerScalar_quadMinus hn4 (minusCoeffs_irr 3 1)) _ hgen ?_
      (fundCorr_minus_of_odd (by norm_num) le_rfl hadm).1
    intro R hR g
    exact conjSub_mem_fundamentalSubgroups hR g

end CFSG.ClassicalInvolution.Q3.Q3T7E9
