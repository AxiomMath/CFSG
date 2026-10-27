module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodE7Four
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.ExcFiveToralAux.GoodRootOdd

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross Polynomial
open scoped Matrix

set_option linter.unusedSectionVars false

theorem not_dvd_blocks_E7_four {p : ℕ} (h5 : 5 ≤ p) :
    ∀ d ∈ ([1, 1, 2, 4, 4] : List ℕ), d ≠ 4 → ¬ p ∣ d := by
  intro d hd hd4 hpd
  have hd' : d = 1 ∨ d = 2 ∨ d = 4 := by simpa using hd
  rcases hd' with rfl | rfl | rfl
  · exact absurd (Nat.le_of_dvd (by norm_num) hpd) (by omega)
  · exact absurd (Nat.le_of_dvd (by norm_num) hpd) (by omega)
  · exact hd4 rfl

theorem not_dvd_div_degrees_E7_four {p : ℕ} (h5 : 5 ≤ p) :
    ∀ d ∈ degreesE Tag.E7, 4 ∣ d → ¬ p ∣ d / 4 := by
  intro d hd h4 hpd
  have hd' : d = 2 ∨ d = 6 ∨ d = 8 ∨ d = 10 ∨ d = 12 ∨ d = 14 ∨ d = 18 := by
    simpa [degreesE] using hd
  rcases hd' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exact absurd (Nat.le_of_dvd (by norm_num) hpd) (by omega)
  · omega
  · exact absurd (Nat.le_of_dvd (by norm_num) hpd) (by omega)
  · omega
  · omega

theorem e7Four_eq_five_of_orderOf_two_eq_four {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (h : orderOf (((2 : ℕ)) : ZMod p) = 4) : p = 5 := by
  have h1 : ((2 : ℕ) : ZMod p) ^ 4 = 1 := by
    rw [← h]
    exact pow_orderOf_eq_one _
  have h2 : ((15 : ℕ) : ZMod p) = 0 := by
    push_cast at h1 ⊢
    linear_combination h1
  have h3 : p ∣ 15 := (ZMod.natCast_eq_zero_iff 15 p).1 h2
  have h4 : p ≤ 15 := Nat.le_of_dvd (by norm_num) h3
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

section Rigid

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem setupRigid_E7_four_odd (S : LangSetup .E7 L p) (hp5 : 5 ≤ p) (hAlg : S.IsAlgebraic)
    (hq3 : 3 ≤ S.D.q) (he : orderOf ((S.D.q : ℕ) : ZMod p) = 4) (hρ : RhoIs S e7FourBMat) :
    SetupRigid S :=
  setupRigid_E7_of_goodRoots S (by omega) hAlg
    (goodRootsGenerate_of_classCheck_odd S (Or.inr (Or.inr (Or.inl rfl))) (toMat_cartanList _) hρ
      hq3 (by omega) he e7FourB_classCheck)

end Rigid

theorem langTorusAtAlgM_E7_four_odd (hF : FrobeniusOnRoots) :
    LangTorusAtAlgM .E7 (fun p c => 5 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 4) e7FourBMat :=
  langTorusAtAlgM_E7_of_adjoint e7FourBMat fun K _ _ p hp (h5 : 5 ≤ p) hpK he => by
    obtain ⟨L, hF', hA', S, hq, hAlg, hρ, hsyl, hequiv⟩ :=
      exists_lang_untw_of_blocks_alg_rho hF 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp (by omega) hpK
      (IsWeylMatrix.of_word Tag.E7 e7FourBWord) [1, 1, 2, 4, 4] e7FourB_charpoly e7FourB_pow he
      (not_dvd_blocks_E7_four h5) (not_dvd_div_degrees_E7_four h5) (by decide)
      (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 K).1
    refine ⟨L, hF', hA', S, hq, hAlg, fun γ hγ => ?_, hsyl, hequiv⟩
    rw [hρ γ hγ, e7FourB_wordMat]

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
