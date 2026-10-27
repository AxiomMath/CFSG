module

public import CFSG.ClassicalInvolution.Q3.Q3T8E4Gen
public import CFSG.ClassicalInvolution.Q3.Q3TIYPOutAll
public import CFSG.ClassicalInvolution.Q3.Q3URDict
public import CFSG.ClassicalInvolution.Q3.Q3URStd

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement


variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem sq_dichotomy_of_twin_pair {n : ℕ} (hn : CITBelowT (.sl2 3 1) n) (hih : IH8T 3 1 n)
    (hlt : Nat.card X < n) (hΦ : HypOmegaModU (.sl2 3 1) Φ)
    (hO : classicalInvolutionOddCore X = ⊥) (hgen : omegaGen Φ = ⊤)
    (hA : ∀ L ∈ Φ, AEmpty Φ L) (hdisc : ¬ T3.DStarConnected Φ) {A B : Subgroup X}
    (hAΦ : A ∈ Φ) (hB : B ∈ omegaNbr Φ A) {x₀ : X} (hxA : IsUniqueInvolution A x₀)
    (hxB : IsUniqueInvolution B x₀) (α : MulAut X) (hα4 : α * α * (α * α) = 1)
    (hαA : ∀ a ∈ A, α a * a⁻¹ ∈ oddCoreOf A) (hαB : ∀ b ∈ B, α b * b⁻¹ ∈ oddCoreOf B) :
    α * α = 1 ∨ α * α = MulAut.conj x₀ := by
  obtain ⟨t, k, htag, ⟨M⟩⟩ := E4G3.e4_tag3 hn hih hlt hΦ hO hgen hA hdisc hAΦ hB
  have hcen : x₀ * x₀ ∈ Subgroup.center X := by
    rw [hxA.sq]
    exact Subgroup.one_mem _
  rcases htag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h4 | ⟨rfl, rfl⟩ | h6
  ·
    have hG2 : StatedLieTag.PSp ≠ .G2 := by decide
    have hD4 : StatedLieTag.PSp ≠ .trialityD4 := by decide
    have hnpsl : ¬ (StatedLieTag.PSp = .PSL ∧ (2 : ℕ) = 2) := by simp
    have hSperf : Group.IsPerfect (modelUniv .PSp 2 3 1 Fact.out).K :=
      Group.isPerfect_def.2
        (ModelFacts.modelClauseZero .PSp 2 3 1 Fact.out trivial M.admissible).1.1
    obtain ⟨R, R', y, y', hR, hR', hAR, hBR, hy, hy', hP⟩ :=
      E4G3.e4_pair_of_model3 hΦ M hG2 hD4 hnpsl hSperf hAΦ hB hxA hxB hcen
    have hex := exactMembers_of_ih8Model M hΦ hG2 hD4
    have hαA' : ∀ a ∈ A, α a = a := fun a ha => by
      have h1 := hαA a ha
      rw [oddCoreOf_eq_bot_of_exact hex hAΦ, Subgroup.mem_bot, mul_inv_eq_one] at h1
      exact h1
    have hαB' : ∀ b ∈ B, α b = b := fun b hb => by
      have h1 := hαB b hb
      rw [oddCoreOf_eq_bot_of_exact hex hB.1, Subgroup.mem_bot, mul_inv_eq_one] at h1
      exact h1
    have key := Q3TIY.sqDichotomyC_psp2 X M.ψ M.surj M.ker_le_center R R' (M.cls_sub hR)
      (M.cls_sub hR') hP.ne y y' hP.hy hP.hy2 hP.hy1 hP.hy' hP.hy'2 hP.hy'1
      (hy.trans hy'.symm) α hα4 (fun r hr => hαA' _ (hAR ▸ Subgroup.mem_map_of_mem _ hr))
      (fun r hr => hαB' _ (hBR ▸ Subgroup.mem_map_of_mem _ hr))
    rwa [hy] at key
  ·
    have hG2 : StatedLieTag.PSL ≠ .G2 := by decide
    have hD4 : StatedLieTag.PSL ≠ .trialityD4 := by decide
    have hnpsl : ¬ (StatedLieTag.PSL = .PSL ∧ (4 : ℕ) = 2) := by simp
    have hSperf : Group.IsPerfect (modelUniv .PSL 4 3 1 Fact.out).K :=
      Group.isPerfect_def.2
        (ModelFacts.modelClauseZero .PSL 4 3 1 Fact.out trivial M.admissible).1.1
    obtain ⟨R, R', y, y', hR, hR', hAR, hBR, hy, hy', hP⟩ :=
      E4G3.e4_pair_of_model3 hΦ M hG2 hD4 hnpsl hSperf hAΦ hB hxA hxB hcen
    have hex := exactMembers_of_ih8Model M hΦ hG2 hD4
    have hαA' : ∀ a ∈ A, α a = a := fun a ha => by
      have h1 := hαA a ha
      rw [oddCoreOf_eq_bot_of_exact hex hAΦ, Subgroup.mem_bot, mul_inv_eq_one] at h1
      exact h1
    have hαB' : ∀ b ∈ B, α b = b := fun b hb => by
      have h1 := hαB b hb
      rw [oddCoreOf_eq_bot_of_exact hex hB.1, Subgroup.mem_bot, mul_inv_eq_one] at h1
      exact h1
    have key := Q3TIY.sqDichotomyC_psl4 M.admissible X M.ψ M.surj M.ker_le_center R R'
      (M.cls_sub hR) (M.cls_sub hR') hP.ne y y' hP.hy hP.hy2 hP.hy1 hP.hy' hP.hy'2 hP.hy'1
      (hy.trans hy'.symm) α hα4 (fun r hr => hαA' _ (hAR ▸ Subgroup.mem_map_of_mem _ hr))
      (fun r hr => hαB' _ (hBR ▸ Subgroup.mem_map_of_mem _ hr))
    rwa [hy] at key
  · exact absurd (E4G3.dstarConnected_psu43 hΦ M) hdisc
  · exact absurd (E4G3.dstarConnected_spin_of_pair3 hΦ M (Or.inl h4) hAΦ hB hxA hxB hcen) hdisc
  · exact absurd (E4G3.dstarConnected_spin8plus3 hΦ M) hdisc
  · exact absurd (E4G3.dstarConnected_spin_of_pair3 hΦ M (Or.inr h6) hAΦ hB hxA hxB hcen) hdisc

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
