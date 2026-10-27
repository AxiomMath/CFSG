module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameCondBasic

public section

namespace CFSG.EvenSporadicStandard.TwoFi22

open CFSG.EvenSporadicStandard.Wong77.Module

theorem hammingNorm_eq_coord_zero_add (v : Word) :
    hammingNorm v =
      (if v 0 ≠ 0 then 1 else 0) + ∑ i : Fin 22, (if v i.succ ≠ 0 then 1 else 0) := by
  rw [hammingNorm, Finset.card_filter, Fin.sum_univ_succ]

namespace GoodFrame

@[expose] def rho : Word →+ Word where
  toFun w := Function.update w 0 (∑ i, w i)
  map_zero' := by
    funext i
    by_cases hi : i = 0 <;> simp [hi]
  map_add' v w := by
    funext i
    by_cases hi : i = 0
    · subst hi
      simp [Finset.sum_add_distrib]
    · simp [Function.update_of_ne hi]

theorem rho_apply_zero (w : Word) : rho w 0 = ∑ i, w i := by
  simp [rho]

theorem rho_apply_of_ne (w : Word) {i : Fin 23} (hi : i ≠ 0) : rho w i = w i := by
  simp [rho, Function.update_of_ne hi]

theorem rho_rho (w : Word) : rho (rho w) = w := by
  funext i
  by_cases hi : i = 0
  · subst hi
    have h1 : ∑ i, w i = w 0 + ∑ i : Fin 22, w i.succ := Fin.sum_univ_succ w
    have h2 : ∑ i, rho w i = rho w 0 + ∑ i : Fin 22, w i.succ := by
      rw [Fin.sum_univ_succ]
      simp only [rho_apply_of_ne _ (Fin.succ_ne_zero _)]
    rw [rho_apply_zero (rho w), h2, rho_apply_zero w, h1, add_assoc, CharTwo.add_self_eq_zero,
      add_zero]
  · rw [rho_apply_of_ne _ hi, rho_apply_of_ne _ hi]

theorem rho_single_zero : rho (Pi.single 0 1) = Pi.single 0 1 := by
  funext i
  by_cases hi : i = 0
  · subst hi
    simp [rho_apply_zero]
  · rw [rho_apply_of_ne _ hi]

theorem rho_single_ne {i : Fin 23} (hi : i ≠ 0) :
    rho (Pi.single i 1) = Pi.single 0 1 + Pi.single i 1 := by
  funext j
  by_cases hj : j = 0
  · subst hj
    simp [rho_apply_zero, Pi.single_apply, hi.symm]
  · rw [rho_apply_of_ne _ hj]
    simp [Pi.single_apply, hj]

theorem rho_allOnes : rho allOnes = allOnes := by
  funext i
  by_cases hi : i = 0
  · subst hi
    rw [rho_apply_zero]
    decide
  · rw [rho_apply_of_ne _ hi]

theorem seven_le_hammingNorm_rho {c : Word} (hc : 7 ≤ hammingNorm c) :
    7 ≤ hammingNorm (rho c) := by
  have h1 := hammingNorm_eq_coord_zero_add c
  have h2 : hammingNorm (rho c) =
      (if ∑ i, c i ≠ 0 then 1 else 0) + ∑ i : Fin 22, (if c i.succ ≠ 0 then 1 else 0) := by
    rw [hammingNorm_eq_coord_zero_add]
    simp only [rho_apply_zero, rho_apply_of_ne _ (Fin.succ_ne_zero _)]
  generalize ∑ i : Fin 22, (if c i.succ ≠ 0 then 1 else 0) = S at h1 h2
  by_cases hS7 : 7 ≤ S
  · rw [h2]
    omega
  · by_cases hc0 : c 0 = 0
    · simp [hc0] at h1
      omega
    · simp only [ne_eq, hc0, not_false_eq_true, ite_true] at h1
      have hsum : ∑ i, c i ≠ 0 := by
        rw [← hammingNorm_cast c, show hammingNorm c = 7 by omega]
        decide
      simp only [ne_eq, hsum, not_false_eq_true, ite_true] at h2
      omega

variable {X : Type*} [Group X] (F : GoodFrame X)

@[expose] def twist : GoodFrame X where
  φ := F.φ.comp (AddMonoidHom.toMultiplicative rho)
  ker_weight w hw := by
    have hw' : F.φ (Multiplicative.ofAdd (rho w)) = 1 := hw
    rcases F.ker_weight (rho w) hw' with h0 | h7
    · left
      rw [← rho_rho w, h0, map_zero]
    · right
      have := seven_le_hammingNorm_rho h7
      rwa [rho_rho] at this
  prod_ones := by
    show F.φ (Multiplicative.ofAdd (rho allOnes)) = 1
    rw [rho_allOnes]
    exact F.prod_ones

theorem twist_wprod (w : Word) : F.twist.wprod w = F.wprod (rho w) := rfl

theorem twist_pt_zero : F.twist.pt 0 = F.pt 0 := by
  have h := F.twist_wprod (Pi.single 0 1)
  rw [rho_single_zero] at h
  exact h

theorem twist_pt_ne {i : Fin 23} (hi : i ≠ 0) : F.twist.pt i = F.pt 0 * F.pt i := by
  have h := F.twist_wprod (Pi.single i 1)
  rw [rho_single_ne hi, wprod_add] at h
  exact h

end GoodFrame

end CFSG.EvenSporadicStandard.TwoFi22
