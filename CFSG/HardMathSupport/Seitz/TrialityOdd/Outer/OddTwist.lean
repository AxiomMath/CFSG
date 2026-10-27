module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Outer.OddComm
public import CFSG.RankThree.PartOne.SEITZ8.D4Triple
public import CFSG.RankThree.PartOne.SEITZ7.D4AB

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.SEITZ7 CFSG.RankThree.PartOne.SEITZ8

variable {K : Type} [Field K] (σ : K →+* K)

theorem rhoPerm_check : rhoPerm (nd 0) = nd 1 ∧ rhoPerm (nd 1) = nd 3 ∧ rhoPerm (nd 3) = nd 0 ∧
    rhoPerm (nd 2) = nd 2 := by
  decide +kernel

theorem twistC_xd0 (c : K) : twistC .D4 K σ (xd 0 c) = xd 1 (σ c) := by
  have := twistC_xPar_single σ (nd 0) c
  rw [rhoPerm_check.1] at this
  simpa [xd, d4Root_simple_0, d4Root_simple_1] using this

theorem twistC_xd1 (c : K) : twistC .D4 K σ (xd 1 c) = xd 3 (σ c) := by
  have := twistC_xPar_single σ (nd 1) c
  rw [rhoPerm_check.2.1] at this
  simpa [xd, d4Root_simple_1, d4Root_simple_3] using this

theorem twistC_xd2 (c : K) : twistC .D4 K σ (xd 2 c) = xd 2 (σ c) := by
  have := twistC_xPar_single σ (nd 2) c
  rw [rhoPerm_check.2.2.2] at this
  simpa [xd, d4Root_simple_2] using this

theorem twistSign_5 : twistSign σ (d4Root 5) = 1 := by
  have h5 : twistC .D4 K σ (xd 5 (-1 : K)) =
      xd 7 (twistSign σ (d4Root 5) * σ (-1)) := by
    have := twistC_xPar σ (SEITZ8.isRoot_d4 (by norm_num : 5 < 24)) (-1 : K)
    rw [rho_dict.2.2.2.2.2.1] at this
    exact this
  have hs := congrArg (twistC .D4 K σ) (swapO_0_2 (K := K) 1 1)
  simp only [map_mul, twistC_xd0, twistC_xd2, mul_one, map_one] at hs
  rw [h5] at hs
  have h2 := swapO_1_2 (K := K) 1 1
  simp only [mul_one] at h2
  have h3 := mul_right_cancel (hs.symm.trans h2)
  have h4 := xPar_injective (SEITZ8.isRoot_d4 (by norm_num : 7 < 24)) h3
  simp only [map_neg, map_one, mul_neg, mul_one, neg_inj] at h4
  exact h4

theorem twistSign_7 : twistSign σ (d4Root 7) = -1 := by
  have h7 : twistC .D4 K σ (xd 7 (-1 : K)) =
      xd 9 (twistSign σ (d4Root 7) * σ (-1)) := by
    have := twistC_xPar σ (SEITZ8.isRoot_d4 (by norm_num : 7 < 24)) (-1 : K)
    rw [rho_dict.2.2.2.2.2.2.1] at this
    exact this
  have hs := congrArg (twistC .D4 K σ) (swapO_1_2 (K := K) 1 1)
  simp only [map_mul, twistC_xd1, twistC_xd2, mul_one, map_one] at hs
  rw [h7] at hs
  have h2 := swapO_3_2 (K := K) 1 1
  simp only [mul_one] at h2
  have h3 := mul_right_cancel (hs.symm.trans h2)
  have h4 := xPar_injective (SEITZ8.isRoot_d4 (by norm_num : 9 < 24)) h3
  simp only [map_neg, map_one, mul_neg, mul_one] at h4
  exact neg_eq_iff_eq_neg.1 h4

theorem xOrbit_0 (a : K) :
    xOrbit σ (d4Root 0) a = xd 0 a * xd 1 (σ a) * xd 3 (σ (σ a)) := by
  have h0 := twistSign_single σ (nd 0)
  have h1 := twistSign_single σ (nd 1)
  rw [← d4Root_simple_0] at h0
  rw [← d4Root_simple_1] at h1
  simp only [xOrbit, rho_dict.2.2.2.1, rho_dict.2.2.2.2.1, h0, h1]
  simp [xd]

end CFSG.HardMathSupport.Seitz.TrialityOdd
