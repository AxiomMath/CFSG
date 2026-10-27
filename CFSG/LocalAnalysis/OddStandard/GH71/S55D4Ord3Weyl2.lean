module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4Ord3Weyl

public section

namespace CFSG.OddStandard.GH71.S55

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KGD CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

theorem d4_tab_parity_all : ∀ e ∈ d4WeylTab, d4MatT e ^ 3 = 1 → d4MatT e ≠ 1 →
    ¬ (d4ParityFix (d4MatT e) d4ParA ∧ d4ParityFix (d4MatT e) d4ParB) := by
  decide +kernel

theorem d4_weyl_moves_sign_all {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    {w : WeylGroup TwistTag.D4.tag} (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) :
    weylTuple w (d4Sign K d4ParA) ≠ d4Sign K d4ParA ∨
      weylTuple w (d4Sign K d4ParB) ≠ d4Sign K d4ParB := by
  obtain ⟨e, he, hwe⟩ := exists_mem_d4WeylTab w
  have hpow : ∀ (n : ℕ) (v : Fin TwistTag.D4.tag.rank → ℤ), (w ^ n) • v = d4MatT e ^ n *ᵥ v :=
    fun n v => pow_smul_eq_d4Mat_pow_mulVec w hwe n v
  have hent : ∀ (n : ℕ) (i j : Fin TwistTag.D4.tag.rank),
      ((w ^ n) • (Pi.single j 1 : Fin TwistTag.D4.tag.rank → ℤ)) i = (d4MatT e ^ n) i j := by
    intro n i j
    rw [hpow]
    exact mulVec_single_one_apply' _ i j
  have hM3 : d4MatT e ^ 3 = 1 := by
    ext i j
    rw [← hent 3 i j, hw3, one_smul, Matrix.one_apply, Pi.single_apply]
  have hM1 : d4MatT e ≠ 1 := by
    intro h
    apply hw1
    refine FaithfulSMul.eq_of_smul_eq_smul (α := Fin TwistTag.D4.tag.rank → ℤ) fun v => ?_
    rw [one_smul, ← pow_one w, hpow, pow_one, h, Matrix.one_mulVec]
  have hpar := d4_tab_parity_all e he hM3 hM1
  have hwinv : w⁻¹ = w ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact hw3
  have hfix : ∀ c : Fin TwistTag.D4.tag.rank → ℤ,
      weylTuple w (d4Sign K c) = d4Sign K c → d4ParityFix (d4MatT e) c := by
    intro c hc i
    have h := congrFun hc i
    simp only [weylTuple] at h
    rw [rootChar_d4Sign] at h
    have hc' : ∀ j, (w⁻¹ • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ)) j =
        (d4MatT e ^ 2) j i := fun j => by
      rw [hwinv]
      exact hent 2 j i
    simp only [hc'] at h
    exact (neg_one_zpow_eq_iff h2 _ _).1 h
  by_contra hcon
  push Not at hcon
  exact hpar ⟨hfix _ hcon.1, hfix _ hcon.2⟩

end CFSG.OddStandard.GH71.S55
