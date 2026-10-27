module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SOInputs
public import Certificates.Certificate27141

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Sporadic.SuzOddCore CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.EvenSporadicStandard.Solomon78


theorem exists_orderOf_eight_suzM : ∃ g : ↥suzM, orderOf g = 8 := by
  have h := Certificates.certificate27141
  simp only [suzOrderEightCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hl, h8⟩, h4⟩ := h
  have hR : Rep 1782 suzArrO8 (suzWord suzWordO8) := by
    unfold suzArrO8
    exact rep_suzArr (lettersOK_mono (by norm_num) hl)
  have hx2 := rep_compA hR hR
  have hx4 := rep_compA hx2 hx2
  have hx8 := rep_compA hx4 hx4
  have e8 := (eqA_iff hx8 rep_idA).1 h8
  have e4 : (suzWord suzWordO8 * suzWord suzWordO8) * (suzWord suzWordO8 * suzWord suzWordO8) ≠ 1 :=
    fun hh => by
      have := (eqA_iff hx4 rep_idA).2 hh
      rw [this] at h4
      exact absurd h4 (by decide)
  set x := suzWord suzWordO8 with hx
  have hp4 : x ^ 4 = x * x * (x * x) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  have hp8 : x ^ 8 = x * x * (x * x) * (x * x * (x * x)) := by
    rw [show (8 : ℕ) = 4 + 4 from rfl, pow_add, hp4]
  have h4' : ¬ x ^ 4 = 1 := by
    rw [hp4]
    exact e4
  have h8' : x ^ 8 = 1 := by
    rw [hp8]
    exact e8
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf x = 8 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 2) (by simpa using h4') (by simpa using h8')
    simpa using this
  refine ⟨⟨x, suzWord_mem (lettersOK_mono (by norm_num) hl)⟩, ?_⟩
  rw [Subgroup.orderOf_mk]
  exact hord

theorem suz_sporadicOrderEight : SporadicOrderEight .Suz := by
  obtain ⟨g, hg⟩ := exists_orderOf_eight_suzM
  obtain ⟨e⟩ := suz_equiv_of_isSporadic (X := Carrier .Suz) ⟨MulEquiv.refl _⟩
  exact ⟨e.symm g, by rw [MulEquiv.orderOf_eq]; exact hg⟩

end CFSG.EvenSporadicStandard.Induction
