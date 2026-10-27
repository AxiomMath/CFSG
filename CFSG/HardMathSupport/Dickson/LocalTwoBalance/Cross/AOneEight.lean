module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Split
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_5_2L2Main

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.DefChar
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem localTwoCrossFamAt_three_A_one_eight :
    LocalTwoCrossFamAt 3 .A fun idx =>
      ∃ q : TauCeti.PrimePower, idx.1 = .A 1 q ∧ q.card = 8 := by
  intro idx _ hR _ _
  obtain ⟨q, hq, hq8⟩ := hR
  obtain ⟨i, hi⟩ := idx
  obtain rfl : i = .A 1 q := hq
  obtain ⟨p, f, hp, hf⟩ := q
  have hpow : p ^ f = 2 ^ 3 := by
    have h8 : p ^ f = 8 := (TauCeti.PrimePower.card_def _).symm.trans hq8
    exact h8.trans (by norm_num)
  have hp2 : p = 2 := by
    have hdvd : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 from hpow ▸ dvd_pow_self p hf.ne')
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd
  subst hp2
  have hf3 : f = 3 := Nat.pow_right_injective (le_refl 2) hpow
  subst hf3
  have e1 := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 ⟨2, 3, hp, hf⟩ hi
  have e2 : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3) :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 2
        (GaloisField 2 3)).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLTwoEquivSL (GaloisField 2 3))
  have e3 : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3) ≃*
      ↥(StatedSL 2 (GaloisField 2 3)) :=
    (l2opStatedSLEquiv 2 (GaloisField 2 3)).symm
  have hcard : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
  have hL2 : IsLocallyBalancedAbs 3 2 ↥(StatedSL 2 (GaloisField 2 3)) :=
    isLocallyBalancedAbs_L2OddPow _ ⟨GaloisField 2 3, inferInstance, inferInstance, 3,
      by norm_num, by norm_num, hcard, ⟨MulEquiv.refl _⟩⟩
  exact IsLocallyBalancedAbs.of_mulEquiv (e1.trans (e2.trans e3)) hL2

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
