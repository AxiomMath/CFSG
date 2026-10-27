module

public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2Tags

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem fundamentalSL2_of_isFundTag {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {t : StatedLieTag}
    {n e : ℕ} (hfund : Generic.IsFundTag t) (hadm : StatedLieAdmissible t n p e) :
    FundamentalSL2 p t n e := by
  cases t with
  | PSL =>
    by_cases hn : n = 2
    · subst hn
      exact fundamentalSL2_PSL_two p e hadm
    · exact fundamentalSL2_PSL n p e hadm (by have := hadm.2.2.1; omega)
  | PSU => exact fundamentalSL2_PSU n p e hp2 hadm
  | PSp => exact fundamentalSL2_PSp n p e hadm
  | POmegaOdd => exact fundamentalSL2_POmegaOdd n p e hadm
  | POmegaPlus => exact fundamentalSL2_POmegaPlus n p e hadm
  | POmegaMinus => exact fundamentalSL2_POmegaMinus n p e hp2 hadm
  | G2 => exact fundamentalSL2_G2 n p e hadm
  | F4 =>
    obtain rfl : n = 0 := hadm.2.2
    exact fundamentalSL2_F4 p e hadm
  | E6 =>
    obtain rfl : n = 0 := hadm.2.2
    exact fundamentalSL2_E6 p e hadm
  | E7 =>
    obtain rfl : n = 0 := hadm.2.2
    exact fundamentalSL2_E7 p e hadm
  | E8 =>
    obtain rfl : n = 0 := hadm.2.2
    exact fundamentalSL2_E8 p e hadm
  | twistedE6 =>
    obtain rfl : n = 0 := hadm.2.2
    exact fundamentalSL2_twistedE6 p e hadm
  | trialityD4 => exact fundamentalSL2_trialityD4 n p e hadm
  | twistedB2 | twistedG2 | twistedF4 | Tits => exact absurd hfund (by simp [Generic.IsFundTag])

theorem nonempty_equiv_sl2_of_mem_fundamentalSubgroups {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {t : StatedLieTag} {n e : ℕ} (hfund : Generic.IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) {R : Subgroup (Generic.modelUniv t n p e Fact.out).K}
    (hR : R ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D) :
    Nonempty (R ≃* SL(2, GaloisField p e)) := by
  obtain ⟨g, γ, hγ, rfl⟩ := hR
  rcases hγ with h | ⟨h, -⟩ | ⟨h, -⟩
  · exact fundamentalSL2_of_isFundTag hp2 hfund hadm g γ h
  · exact absurd h hG2
  · exact absurd h hD4

end CFSG.ClassicalInvolution.ModelFacts
