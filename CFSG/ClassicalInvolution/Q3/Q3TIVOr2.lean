module

public import CFSG.ClassicalInvolution.Q3.Q3TIVDefs
public import CFSG.ClassicalInvolution.Q3.Q3TIVOr1
public import CFSG.ClassicalInvolution.Q3.Q3TWY1
public import CFSG.ClassicalInvolution.Q3.Q3TY13
public import CFSG.ClassicalInvolution.ModelFacts.TG3OrthTags
public import CFSG.ClassicalInvolution.Q3.Q3VF4Row
public import CFSG.LieType.Chevalley.E7SupportedBruhat

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIV

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.Asc77.S28 (SameOrOrth sameOrOrth_of_lt_eight sameOrOrth_of_nine_le
  sameOrOrth_of_noOrth sameOrOrth_of_eight)
open scoped MatrixGroups


section Ctx

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

theorem twinProductCentral3_of_ctx {tY : StatedLieTag} {nY : ℕ} {X : Type} [Group X]
    {D : UniversalRootDatum X} (hM : modelUniv tY nY 3 1 Nat.prime_three = ⟨X, D⟩)
    (hodd : Odd (Nat.card F)) (π : X →* (V ≃ₗ[F] V)) {Z' : Subgroup (V ≃ₗ[F] V)}
    (cq : Q3W.CentralQuot3 π (fundamentalSubgroups tY D) (fundSet Q) Z')
    (hperf : Group.IsPerfect (modelUniv tY nY 3 1 Nat.prime_three).K)
    (hsl : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
      Nonempty (R ≃* SL(2, F)))
    (hsame : SameOrOrth Q) : TwinProductCentral3 tY nY := by
  unfold TwinProductCentral3
  generalize modelUniv tY nY 3 1 Nat.prime_three = M at hM hperf hsl ⊢
  subst hM
  exact twinProductCentral_orth3 hodd π cq (commutator_top_of_isPerfect hperf) hsl hsame

end Ctx

theorem twinProductCentral3_odd {n : ℕ} (hn : 3 ≤ n) : TwinProductCentral3 .POmegaOdd n := by
  have hadm : StatedLieAdmissible .POmegaOdd n 3 1 := ⟨Nat.prime_three, le_rfl, hn, by norm_num⟩
  have hdim : Module.finrank (GaloisField 3 1) (Fin n ⊕ Fin n ⊕ Unit → GaloisField 3 1) =
      2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  have hsame : SameOrOrth (quadOdd n (GaloisField 3 1)) := by
    by_cases h3 : n = 3
    · exact sameOrOrth_of_lt_eight Q3W.odd_gf3 (by rw [hdim]; omega)
    · exact sameOrOrth_of_nine_le Q3W.odd_gf3
        (nondegenerate_polarBilin_quadOdd n (GaloisField 3 1) Q3W.two_ne_zero_gf3)
        (by rw [hdim]; omega)
  have hperf : Group.IsPerfect (modelUniv .POmegaOdd n 3 1 Nat.prime_three).K :=
    perfectK_of_admissible Nat.prime_three trivial hadm
  have hsl : ∀ R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n 3 1 Nat.prime_three).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3) (by norm_num)
      (t := .POmegaOdd) trivial hadm (by decide) (by decide) hR
  exact twinProductCentral3_of_ctx (tY := .POmegaOdd) (nY := n)
    (X := spinGroup (quadOdd n (GaloisField 3 1))) (D := oddDatum n (GaloisField 3 1)) rfl
    Q3W.odd_gf3 (spinAction (quadOdd n (GaloisField 3 1))) (Q3TWY.centralQuot3_odd hn) hperf hsl
    hsame

theorem twinProductCentral3_minus {n : ℕ} (hn : 4 ≤ n) : TwinProductCentral3 .POmegaMinus n := by
  have hadm : StatedLieAdmissible .POmegaMinus n 3 1 := ⟨Nat.prime_three, le_rfl, hn⟩
  have hdim : Module.finrank (GaloisField 3 1)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 3 1) = 2 * (n - 1) + 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    ring
  have hsame : SameOrOrth (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2) := by
    by_cases h4 : n = 4
    · subst h4
      exact sameOrOrth_of_noOrth Q3W.odd_gf3 (fun F₀ F₁ hF =>
        ModelFacts.TG3.false_of_orth_quadMinus_four3 Q3W.two_ne_zero_gf3 (minusCoeffs_irr 3 1)
          (by rw [Q3W.card_gf3]; norm_num) F₀ F₁ hF)
    · exact sameOrOrth_of_nine_le Q3W.odd_gf3
        (nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 3 1) (minusCoeffs_irr 3 1))
        (by rw [hdim]; omega)
  have hperf : Group.IsPerfect (modelUniv .POmegaMinus n 3 1 Nat.prime_three).K :=
    perfectK_of_admissible Nat.prime_three trivial hadm
  have hsl : ∀ R ∈ fundamentalSubgroups .POmegaMinus
      (modelUniv .POmegaMinus n 3 1 Nat.prime_three).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3) (by norm_num)
      (t := .POmegaMinus) trivial hadm (by decide) (by decide) hR
  exact twinProductCentral3_of_ctx (tY := .POmegaMinus) (nY := n)
    (X := spinGroup (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))
    (D := Twisted.minusDatum n (minusCoeffs_irr 3 1)) rfl Q3W.odd_gf3
    (spinAction (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))
    (Q3TY.centralQuot3_minus hadm) hperf hsl hsame

theorem twinProductCentral3_plus {n : ℕ} (hn : 4 ≤ n) : TwinProductCentral3 .POmegaPlus n := by
  have hn3 : 3 ≤ n := by omega
  have hadm : StatedLieAdmissible .POmegaPlus n 3 1 := ⟨Nat.prime_three, le_rfl, hn⟩
  have hdim : Module.finrank (GaloisField 3 1) (Fin n ⊕ Fin n → GaloisField 3 1) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hsame : SameOrOrth (quadPlus n (GaloisField 3 1)) := by
    by_cases h4 : n = 4
    · exact sameOrOrth_of_eight Q3W.odd_gf3 (by rw [hdim]; omega)
    · exact sameOrOrth_of_nine_le Q3W.odd_gf3
        (nondegenerate_polarBilin_quadPlus n (GaloisField 3 1)) (by rw [hdim]; omega)
  have hperf : Group.IsPerfect (modelUniv .POmegaPlus n 3 1 Nat.prime_three).K :=
    perfectK_of_admissible Nat.prime_three trivial hadm
  have hsl : ∀ R ∈ fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus n 3 1 Nat.prime_three).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3) (by norm_num)
      (t := .POmegaPlus) trivial hadm (by decide) (by decide) hR
  exact twinProductCentral3_of_ctx (tY := .POmegaPlus) (nY := n)
    (X := spinGroup (quadPlus n (GaloisField 3 1))) (D := plusDatum n (GaloisField 3 1) hn3)
    (modelUniv_POmegaPlus_eq (p := 3) (f := 1) hn3) Q3W.odd_gf3
    (spinAction (quadPlus n (GaloisField 3 1))) (Q3TY.centralQuot3_plus hn) hperf hsl hsame

end CFSG.ClassicalInvolution.Q3.Q3TIV
