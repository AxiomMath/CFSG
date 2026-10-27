module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2G1Mat

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint CFSG.Open

theorem two_ne_zero_of_natCard_eq_pow_three {K : Type} [Field K] [Finite K] {k : ℕ} (hk : 0 < k)
    (h : Nat.card K = 3 ^ k) : (2 : K) ≠ 0 := by
  intro h2
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hcard⟩ := FiniteField.card K 2
  rw [← Nat.card_eq_fintype_card] at hcard
  have hpow : 2 ^ (n : ℕ) = 3 ^ k := by rw [← hcard, h]
  have hne : (n : ℕ) ≠ 0 := n.pos.ne'
  have hodd : Odd (3 ^ k) := (Nat.odd_pow_iff hk.ne').mpr (by decide)
  have heven : Even (2 ^ (n : ℕ)) := Nat.even_pow.mpr ⟨even_two, hne⟩
  rw [hpow] at heven
  exact Nat.not_even_iff_odd.mpr hodd heven

private theorem not_injective_of_statedClassicalModel_psl2 {X : Type} [Group X] {k : ℕ}
    (hk : 0 < k) (h : StatedClassicalModel X .PSL 2 3 k) :
    ∀ f : QuaternionGroup 2 →* X, ¬ Function.Injective f := by
  dsimp only [StatedClassicalModel] at h
  obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  intro f hf
  exact (not_injective_quaternion_statedProj
      (two_ne_zero_of_natCard_eq_pow_three hk hKcard) (e.toMonoidHom.comp f))
    (e.injective.comp hf)

theorem asc82NoQ8InL2_holds : Asc82NoQ8InL2 := by
  intro X _ hX f hf
  rcases hX with h | h
  · exact not_injective_of_statedClassicalModel_psl2 (by norm_num)
      (LieModel.statedClassicalModel_of_ne_zero (by norm_num) h) f hf
  · exact not_injective_of_statedClassicalModel_psl2 (by norm_num)
      (LieModel.statedClassicalModel_of_ne_zero (by norm_num) h) f hf

end CFSG.OddStandard.SmallF3.Omega
