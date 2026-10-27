module

public import CFSG.CGT.PushingUpLit.CGT6X.ExtNatCoh

public section

namespace CFSG.CGT.PushingUpLit.CGT6X

open CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6.TwoEight CFSG.SL2MinimalFaithful

variable (n : ℕ) [NeZero n]

omit [NeZero n] in
theorem wd_ext (a b : Wd (Fz n) (Fq (2 * n))) (h1 : a.1 = b.1) (h2 : a.2.1 = b.2.1)
    (h3 : a.2.2 = b.2.2) : a = b := Prod.ext h1 (Prod.ext h2 h3)

omit [NeZero n] in
theorem fz_add_self (a : Fz n) : a + a = 0 := by
  have : (2 : Fz n) = 0 := CharP.cast_eq_zero _ 2
  linear_combination a * this

omit [NeZero n] in
theorem fq_add_self (a : Fq (2 * n)) : a + a = 0 := by
  have := two_eq_zero_Fq n
  linear_combination a * this

theorem unip_add_self (x : Fq (2 * n)) (w : Wd (Fz n) (Fq (2 * n))) :
    minusHom n (unipotent x) w + w =
      (Bval n x w.2.1 + Qval n x * w.2.2, (w.2.2 : Fq (2 * n)) * x, 0) := by
  rw [minusHom_unip']
  refine wd_ext n _ _ ?_ ?_ ?_
  · show w.1 + Bval n x w.2.1 + Qval n x * w.2.2 + w.1 = _
    linear_combination fz_add_self n w.1
  · show w.2.1 + (w.2.2 : Fq (2 * n)) * x + w.2.1 = _
    linear_combination fq_add_self n w.2.1
  · show w.2.2 + w.2.2 = 0
    exact fz_add_self n _

theorem lower_apply (x : Fq (2 * n)) (w : Wd (Fz n) (Fq (2 * n))) :
    minusHom n (lowerUnipotent (sigR n x)) w =
      (w.1, w.2.1 + (w.1 : Fq (2 * n)) * x, w.2.2 + Bval n x w.2.1 + Qval n x * w.1) := by
  rw [minusHom_lower, lamPerm_apply]
  rfl

theorem exists_B_eq (y : Fq (2 * n)) (hy : y ≠ 0) (t : Fz n) :
    ∃ x : Fq (2 * n), Bval n x y = t := by
  obtain ⟨x, hx⟩ := B_surj (minusData n) hy t
  exact ⟨x, (B_symm (minusData n) x y).trans hx⟩

theorem natModule_irreducible (W : Subgroup (NMod n))
    (hW : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n)), ∀ m ∈ W, rhoW n A m ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  let P : Wd (Fz n) (Fq (2 * n)) → Prop := fun w => Multiplicative.ofAdd w ∈ W
  have hPadd : ∀ a b, P a → P b → P (a + b) := fun a b ha hb => by
    show Multiplicative.ofAdd (a + b) ∈ W
    rw [ofAdd_add]
    exact W.mul_mem ha hb
  have hPA : ∀ A w, P w → P (minusHom n A w) := fun A w hw => hW A _ hw
  have hstep : ∀ w, P w → ∀ x, P (minusHom n (unipotent x) w + w) := fun w hw x =>
    hPadd _ _ (hPA _ w hw) hw
  have hA : ∀ w : Wd (Fz n) (Fq (2 * n)), P w → w.2.2 ≠ 0 → ∀ t : Fz n, P (t, 0, 0) := by
    intro w hw hs t
    have hsK : (w.2.2 : Fq (2 * n)) ≠ 0 := fun h => hs (Subtype.ext h)
    have hw₁ := hstep w hw ((w.2.2 : Fq (2 * n))⁻¹)
    rw [unip_add_self] at hw₁
    obtain ⟨x₂, hx₂⟩ := exists_B_eq n 1 one_ne_zero t
    have hw₂ := hstep _ hw₁ x₂
    rw [unip_add_self] at hw₂
    have e : (Bval n x₂ ((w.2.2 : Fq (2 * n)) * (w.2.2 : Fq (2 * n))⁻¹) +
        Qval n x₂ * 0, ((0 : Fz n) : Fq (2 * n)) * x₂, 0) =
        ((t, 0, 0) : Wd (Fz n) (Fq (2 * n))) := by
      refine wd_ext n _ _ ?_ ?_ ?_
      · show Bval n x₂ ((w.2.2 : Fq (2 * n)) * (w.2.2 : Fq (2 * n))⁻¹) + Qval n x₂ * 0 = t
        rw [mul_inv_cancel₀ hsK, mul_zero, add_zero, hx₂]
      · simp
      · rfl
    simpa only [e] using hw₂
  have hB : ∀ w : Wd (Fz n) (Fq (2 * n)), P w → w.2.2 = 0 → w.2.1 ≠ 0 →
      ∀ t : Fz n, P (t, 0, 0) := by
    intro w hw hs hy t
    obtain ⟨x, hx⟩ := exists_B_eq n w.2.1 hy t
    have hw₁ := hstep w hw x
    rw [unip_add_self] at hw₁
    have e : (Bval n x w.2.1 + Qval n x * w.2.2, (w.2.2 : Fq (2 * n)) * x, 0) =
        ((t, 0, 0) : Wd (Fz n) (Fq (2 * n))) := by
      refine wd_ext n _ _ ?_ ?_ ?_
      · show Bval n x w.2.1 + Qval n x * w.2.2 = t
        rw [hs, mul_zero, add_zero, hx]
      · show (w.2.2 : Fq (2 * n)) * x = 0
        rw [hs]
        simp
      · rfl
    simpa only [e] using hw₁
  have hC : ∀ w : Wd (Fz n) (Fq (2 * n)), P w → w.2.2 = 0 → w.2.1 = 0 → w.1 ≠ 0 →
      ∀ t : Fz n, P (t, 0, 0) := by
    intro w hw hs hy hp t
    have hw' := hPA (lowerUnipotent (sigR n 1)) w hw
    rw [lower_apply] at hw'
    refine hA _ hw' ?_ t
    show w.2.2 + Bval n 1 w.2.1 + Qval n 1 * w.1 ≠ 0
    have hB0 : Bval n 1 w.2.1 = 0 := by
      rw [hy]
      exact Subtype.ext (by simp [coe_Bval])
    have hQ1 : Qval n 1 = 1 := Subtype.ext (by simp [coe_Qval])
    rw [hs, hB0, hQ1]
    simpa using hp
  obtain ⟨m, hm, hm1⟩ : ∃ m ∈ W, m ≠ 1 := by
    by_contra h
    push Not at h
    exact hbot ((Subgroup.eq_bot_iff_forall W).2 h)
  have hw : P (Multiplicative.toAdd m) := by
    show Multiplicative.ofAdd (Multiplicative.toAdd m) ∈ W
    rwa [ofAdd_toAdd]
  have hNS : ∀ t : Fz n, P (t, 0, 0) := by
    intro t
    set w := Multiplicative.toAdd m with hwdef
    by_cases hs : w.2.2 = 0
    · by_cases hy : w.2.1 = 0
      · by_cases hp : w.1 = 0
        · exfalso
          apply hm1
          have : w = 0 := wd_ext n _ _ hp hy hs
          rw [← ofAdd_toAdd m, ← hwdef, this]
          rfl
        · exact hC w hw hs hy hp t
      · exact hB w hw hs hy t
    · exact hA w hw hs t
  have hB0 : ∀ x : Fq (2 * n), Bval n x 0 = 0 := fun x => Subtype.ext (by simp [coe_Bval])
  have h5 : ∀ x : Fq (2 * n), P (0, x, Qval n x) := by
    intro x
    have h1 := hPA (lowerUnipotent (sigR n x)) (1, 0, 0) (hNS 1)
    rw [lower_apply] at h1
    have h2 := hPadd _ _ h1 (hNS 1)
    have e : (((1, 0, 0) : Wd (Fz n) (Fq (2 * n))).1,
        ((1, 0, 0) : Wd (Fz n) (Fq (2 * n))).2.1 +
          (((1, 0, 0) : Wd (Fz n) (Fq (2 * n))).1 : Fq (2 * n)) * x,
        ((1, 0, 0) : Wd (Fz n) (Fq (2 * n))).2.2 +
          Bval n x ((1, 0, 0) : Wd (Fz n) (Fq (2 * n))).2.1 +
          Qval n x * ((1, 0, 0) : Wd (Fz n) (Fq (2 * n))).1) +
          ((1, 0, 0) : Wd (Fz n) (Fq (2 * n))) =
        ((0, x, Qval n x) : Wd (Fz n) (Fq (2 * n))) := by
      refine wd_ext n _ _ ?_ ?_ ?_
      · exact fz_add_self n 1
      · show (0 : Fq (2 * n)) + ((1 : Fz n) : Fq (2 * n)) * x + 0 = x
        simp
      · show (0 : Fz n) + Bval n x 0 + Qval n x * 1 + 0 = Qval n x
        rw [hB0]
        simp
    simpa only [e] using h2
  have h6 : ∀ t : Fz n, P (0, 0, t) := by
    intro t
    obtain ⟨x, hx⟩ := exists_B_eq n 1 one_ne_zero t
    have h := hPadd _ _ (hPadd _ _ (h5 x) (h5 1)) (h5 (x + 1))
    have hQ : Qval n (x + 1) = Qval n x + Qval n 1 + t := by
      rw [← hx]
      exact (minusData n).Q_add x 1
    have e : ((0, x, Qval n x) : Wd (Fz n) (Fq (2 * n))) + (0, 1, Qval n 1) +
        (0, x + 1, Qval n (x + 1)) = ((0, 0, t) : Wd (Fz n) (Fq (2 * n))) := by
      refine wd_ext n _ _ ?_ ?_ ?_
      · show (0 : Fz n) + 0 + 0 = 0
        simp
      · show x + 1 + (x + 1) = 0
        linear_combination fq_add_self n x + fq_add_self n 1
      · show Qval n x + Qval n 1 + Qval n (x + 1) = t
        rw [hQ]
        linear_combination (Qval n x + Qval n 1) * (CharP.cast_eq_zero (Fz n) 2)
    simpa only [e] using h
  have h7 : ∀ y : Fq (2 * n), P (0, y, 0) := by
    intro y
    have h := hPadd _ _ (h5 y) (h6 (Qval n y))
    have e : ((0, y, Qval n y) : Wd (Fz n) (Fq (2 * n))) + (0, 0, Qval n y) =
        ((0, y, 0) : Wd (Fz n) (Fq (2 * n))) := by
      refine wd_ext n _ _ ?_ ?_ ?_
      · show (0 : Fz n) + 0 = 0
        simp
      · show y + 0 = y
        simp
      · exact fz_add_self n _
    simpa only [e] using h
  refine (Subgroup.eq_top_iff' W).2 fun m' => ?_
  have hall : ∀ w : Wd (Fz n) (Fq (2 * n)), P w := by
    intro w
    have h := hPadd _ _ (hPadd _ _ (hNS w.1) (h7 w.2.1)) (h6 w.2.2)
    have e : ((w.1, 0, 0) : Wd (Fz n) (Fq (2 * n))) + (0, w.2.1, 0) + (0, 0, w.2.2) = w := by
      refine wd_ext n _ _ ?_ ?_ ?_
      · show w.1 + 0 + 0 = w.1
        simp
      · show 0 + w.2.1 + 0 = w.2.1
        simp
      · show 0 + 0 + w.2.2 = w.2.2
        simp
    simpa only [e] using h
  have h : Multiplicative.ofAdd (Multiplicative.toAdd m') ∈ W := hall _
  rwa [ofAdd_toAdd] at h

end CFSG.CGT.PushingUpLit.CGT6X
