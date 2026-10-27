module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112Perm

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem sec11_lam_repr (f : (Fin 6 → ZMod 2) → ZMod 2) (h0 : f 0 = 0)
    (hadd : ∀ v w : Fin 6 → ZMod 2, ∑ i, v i = 0 → ∑ i, w i = 0 → f (v + w) = f v + f w) :
    ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 →
      f v = sec11Lam (fun i : Fin 5 => f (Pi.single 0 1 + Pi.single i.succ 1)) v := by
  intro v hv
  set u : Fin 5 → (Fin 6 → ZMod 2) := fun i => Pi.single 0 1 + Pi.single i.succ 1 with hu
  have hue : ∀ i : Fin 5, ∑ j, u i j = 0 := by
    intro i
    simp only [hu]
    revert i
    decide +kernel
  have hzm : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hsm : ∀ (a : ZMod 2) (x : Fin 6 → ZMod 2), ∑ j, x j = 0 → ∑ j, (a • x) j = 0 := by
    intro a x hx
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, hx, mul_zero]
  have hsmul : ∀ (a : ZMod 2) (x : Fin 6 → ZMod 2), f (a • x) = a * f x := by
    intro a x
    rcases hzm a with rfl | rfl
    · simp [h0]
    · simp
  have heven : ∀ s : Finset (Fin 5), ∑ k, (∑ i ∈ s, v i.succ • u i) k = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      simp only [Pi.add_apply, Finset.sum_add_distrib]
      rw [ih, hsm _ _ (hue a), add_zero]
  have hsum : ∀ s : Finset (Fin 5),
      f (∑ i ∈ s, v i.succ • u i) = ∑ i ∈ s, v i.succ * f (u i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [h0]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd _ _ (hsm _ _ (hue a)) (heven s),
        hsmul, ih]
  have hdec := sec11_decomp v hv
  calc f v = f (∑ i : Fin 5, v i.succ • u i) := by rw [← hdec]
    _ = ∑ i : Fin 5, v i.succ * f (u i) := hsum Finset.univ
    _ = sec11Lam (fun i : Fin 5 => f (Pi.single 0 1 + Pi.single i.succ 1)) v := by
      unfold sec11Lam
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end CFSG.OddStandard.SmallF3.Omega
