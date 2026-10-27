module

public import CFSG.ClassicalInvolution.Asc77.AscIHSectE
public import CFSG.ClassicalInvolution.Q3.Q3TIYDefs
public import CFSG.ClassicalInvolution.Q3.Q3TWY1
public import CFSG.ClassicalInvolution.Q3.Q3TY13

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)


section Ctx

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem noThree3_of_ctx {tY : StatedLieTag} {nY : ℕ} {X : Type} [Group X]
    {D : UniversalRootDatum X} (hM : modelUniv tY nY 3 1 Nat.prime_three = ⟨X, D⟩)
    (hodd : Odd (Nat.card F)) (π : X →* (V ≃ₗ[F] V)) {Z' : Subgroup (V ≃ₗ[F] V)}
    (cq : Q3W.CentralQuot3 π (fundamentalSubgroups tY D) (fundSet Q) Z')
    (hsame : ∀ (R₀ R₁ : Subgroup (V ≃ₗ[F] V)) (i₀ i₁ : V ≃ₗ[F] V), IsFundamental Q R₀ i₀ →
      IsFundamental Q R₁ i₁ → Commutes R₀ R₁ → i₁ = i₀) :
    ∀ A ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
      ∀ B ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
      ∀ S ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
        A ≠ B → A ≠ S → B ≠ S → Commutes A B → Commutes A S → False := by
  generalize modelUniv tY nY 3 1 Nat.prime_three = M at hM ⊢
  subst hM
  intro A hA B hB S hS hAB hAS hBS cAB cAS
  exact Asc77.false_of_commuting_three_fundSet hodd hsame (cq.map_mem A hA) (cq.map_mem B hB)
    (cq.map_mem S hS) (fun h => hAB (cq.map_inj hA hB h)) (fun h => hAS (cq.map_inj hA hS h))
    (fun h => hBS (cq.map_inj hB hS h)) ((cq.commutes_iff hA).mpr cAB)
    ((cq.commutes_iff hA).mpr cAS)

end Ctx

theorem noThree3_odd :
    ∀ A ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 3 3 1 Nat.prime_three).D,
      ∀ B ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 3 3 1 Nat.prime_three).D,
      ∀ S ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 3 3 1 Nat.prime_three).D,
        A ≠ B → A ≠ S → B ≠ S → Commutes A B → Commutes A S → False := by
  have hdim : Module.finrank (GaloisField 3 1) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField 3 1) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
  exact noThree3_of_ctx (tY := .POmegaOdd) (nY := 3)
    (X := spinGroup (quadOdd 3 (GaloisField 3 1))) (D := oddDatum 3 (GaloisField 3 1)) rfl
    Q3W.odd_gf3 (spinAction (quadOdd 3 (GaloisField 3 1))) (Q3TWY.centralQuot3_odd le_rfl)
    (fun _ _ _ _ h₀ h₁ hc => commuting_same_involution Q3W.odd_gf3 (by omega) h₀ h₁ hc)

theorem noThree3_minus :
    ∀ A ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus 4 3 1 Nat.prime_three).D,
      ∀ B ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus 4 3 1 Nat.prime_three).D,
      ∀ S ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus 4 3 1 Nat.prime_three).D,
        A ≠ B → A ≠ S → B ≠ S → Commutes A B → Commutes A S → False := by
  have hadm : StatedLieAdmissible .POmegaMinus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hNo : ∀ F₀ F₁ : Models.OrthogonalPairs.Frame
      (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
      F₁.span ≤ F₀.perp → False := fun F₀ F₁ hF =>
    ModelFacts.TG3.false_of_orth_quadMinus_four3 Q3W.two_ne_zero_gf3 (minusCoeffs_irr 3 1)
      (by rw [Q3W.card_gf3]; norm_num) F₀ F₁ hF
  exact noThree3_of_ctx (tY := .POmegaMinus) (nY := 4)
    (X := spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))
    (D := Twisted.minusDatum 4 (minusCoeffs_irr 3 1)) rfl Q3W.odd_gf3
    (spinAction (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))
    (Q3TY.centralQuot3_minus hadm) (fun R₀ R₁ i₀ i₁ h₀ h₁ hc => by
      rcases Gaps.orth_or_twin Q3W.odd_gf3 h₀ h₁ hc with horth | heq
      · exfalso
        obtain ⟨F₀, rfl, rfl⟩ := h₀
        obtain ⟨F₁, rfl, rfl⟩ := h₁
        exact hNo F₀ F₁ (span_le_perp_of_negSpace Q3W.odd_gf3 horth)
      · exact heq)

theorem smallNoThree3 : SmallNoThree3 := by
  intro t k hadm hsmall A hA B hB S hS hAB hAS hBS cAB cAS cBS
  rcases hsmall with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Asc77.noThree_psp2 (p := 3) (e := 1) (by norm_num) hadm hA hB hS hAB hAS hBS cAB cAS cBS
  · exact Asc77.noThree_psl4 (p := 3) (e := 1) (by norm_num) hA hB hS hAB hAS hBS cAB cAS cBS
  · exact Asc77.noThree_psu4 (p := 3) (e := 1) (by norm_num) hadm hA hB hS hAB hAS hBS cAB cAS
      cBS
  · exact noThree3_odd A hA B hB S hS hAB hAS hBS cAB cAS
  · exact noThree3_minus A hA B hB S hS hAB hAS hBS cAB cAS

end CFSG.ClassicalInvolution.Q3.Q3TIY
