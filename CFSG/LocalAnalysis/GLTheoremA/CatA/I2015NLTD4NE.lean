module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLTD4NB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLTD4ND
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA.MI CFSG.LocalAnalysis.GLTheoremA.FR
  CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem td4n_noLocalTwo_of_core {p : ℕ} (hp : p.Prime) {R : Type} [Group R] [Finite R] {f : MulAut R}
    {E : Subgroup R} (hEC : E ≤ FP.fixSub f) (hE : IsSimpleGroup ↥E)
    (hperf : ∀ T : Subgroup R, T ≤ FP.fixSub f → ⁅T, T⁆ = T → T ≤ E)
    (hN : ∀ U : Subgroup R, U ≠ ⊥ → IsPGroup 2 ↥U → ¬ E ≤ Subgroup.normalizer (U : Set R)) :
    NoLocalTwo p f := by
  intro J J₀ hJ hJ₀ hcov U hU hU2 hN'
  rw [fpFixSub_eq_fixSub] at hEC hperf
  have hJE : J = E := eq_core_of_glaPComponent (p := p) hE hEC hperf hJ
  subst hJE
  have hbot := primeCoreOf_eq_bot_of_simple hp hJ hE
  rw [hbot, sup_bot_eq] at hcov
  subst hcov
  exact hN U hU hU2 hN'

section Main


theorem i2015NLOnTD4Outer_holds : I2015NLOnTD4Outer := by
  intro S _ _ hchev hTD4 β hβ3 hβout
  by_cases hex : ∃ J, GLAPComponent 3 (fixSub β) J
  swap
  · intro J _ hJ
    exact (hex ⟨J, hJ⟩).elim
  obtain ⟨J, hJ⟩ := hex
  have hJ' : GLAPComponent 3 (FP.fixSub β) J := by
    rw [fpFixSub_eq_fixSub]
    exact hJ
  have hT : ∃ T : Subgroup S, T ≤ FP.fixSub β ∧ ⁅T, T⁆ = T ∧ T ≠ ⊥ :=
    ⟨J, hJ'.1, glaPComponent_perfect hJ', glaPComponent_ne_bot' hJ'⟩
  obtain ⟨K, _, _, _, σ, hσ3, e, E, hEC, hE, hna, hperf, hN⟩ :=
    td4n_core hchev hTD4 hβ3 hβout hT
  exact td4n_noLocalTwo_of_core Nat.prime_three hEC hE hperf
    (td4n_no_normalized_two σ hσ3 e hE hna hN)

end Main

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
