module

public import CFSG.CGT.PushingUpLit.CGT6X.ExtNatScalar
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightMinus

public section

namespace CFSG.CGT.PushingUpLit.CGT6X

open CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6.TwoEight CFSG.SL2MinimalFaithful

variable (n : ℕ) [NeZero n]

theorem minusHom_diag (t : Fq (2 * n)) (ht : t ≠ 0) (p : Fz n) (y : Fq (2 * n)) (s : Fz n) :
    minusHom n (diagSL t ht) (p, y, s) =
      (Qval n t * p, t * (sigR n t)⁻¹ * y, (Qval n t)⁻¹ * s) := by
  obtain ⟨e1, e2, e3⟩ := minusHom_entries n (diagSL t ht) p s y
  have hσt : sigR n t ≠ 0 := by
    intro h
    exact ht ((sigR n).injective (h.trans (map_zero _).symm))
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ (Subtype.ext ?_))
  · rw [e1]
    simp [coe_diagSL, cstar_apply, Matrix.mul_apply, Fin.sum_univ_two, coe_Qval]
    ring
  · rw [e2]
    simp [coe_diagSL, cstar_apply, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · rw [e3]
    simp [coe_diagSL, cstar_apply, Matrix.mul_apply, Fin.sum_univ_two, coe_Qval]
    field_simp

theorem minusHom_diag' (t : Fq (2 * n)) (ht : t ≠ 0) (w : Wd (Fz n) (Fq (2 * n))) :
    minusHom n (diagSL t ht) w =
      (Qval n t * w.1, t * (sigR n t)⁻¹ * w.2.1, (Qval n t)⁻¹ * w.2.2) := by
  obtain ⟨p, y, s⟩ := w
  exact minusHom_diag n t ht p y s

theorem minusHom_unip' (x : Fq (2 * n)) (w : Wd (Fz n) (Fq (2 * n))) :
    minusHom n (unipotent x) w =
      (w.1 + Bval n x w.2.1 + Qval n x * w.2.2, w.2.1 + (w.2.2 : Fq (2 * n)) * x, w.2.2) := by
  rw [minusHom_unip, sigPerm_apply]
  rfl

theorem natScalar (F : Fq (2 * n) → Wd (Fz n) (Fq (2 * n)))
    (hadd : ∀ x y, F (x + y) = F x + minusHom n (unipotent x) (F y))
    (htor : ∀ (t : Fq (2 * n)) (ht : t ≠ 0) (x : Fq (2 * n)),
      F (t * t * x) = minusHom n (diagSL t ht) (F x)) :
    (∀ x y, (((F (x + y)).2.2 : Fz n) : Fq (2 * n)) =
        ((F x).2.2 : Fq (2 * n)) + ((F y).2.2 : Fq (2 * n))) ∧
    (∀ x y, (F (x + y)).2.1 = (F x).2.1 + (F y).2.1 + ((F y).2.2 : Fq (2 * n)) * x) ∧
    (∀ x y, (((F (x + y)).1 : Fz n) : Fq (2 * n)) =
        ((F x).1 : Fq (2 * n)) + ((F y).1 : Fq (2 * n)) +
          (x * sigR n (F y).2.1 + sigR n x * (F y).2.1) +
          x * sigR n x * ((F y).2.2 : Fq (2 * n))) ∧
    (∀ t : Fq (2 * n), t ≠ 0 → ∀ x : Fq (2 * n),
      (((F (t * t * x)).2.2 : Fz n) : Fq (2 * n)) = (t * sigR n t)⁻¹ * ((F x).2.2 : Fq (2 * n))) ∧
    (∀ t : Fq (2 * n), t ≠ 0 → ∀ x : Fq (2 * n),
      (F (t * t * x)).2.1 = t * (sigR n t)⁻¹ * (F x).2.1) ∧
    (∀ t : Fq (2 * n), t ≠ 0 → ∀ x : Fq (2 * n),
      (((F (t * t * x)).1 : Fz n) : Fq (2 * n)) = t * sigR n t * ((F x).1 : Fq (2 * n))) := by
  refine ⟨fun x y => ?_, fun x y => ?_, fun x y => ?_, fun t ht x => ?_, fun t ht x => ?_,
    fun t ht x => ?_⟩
  · have := congrArg (fun w : Wd (Fz n) (Fq (2 * n)) => ((w.2.2 : Fz n) : Fq (2 * n)))
      (hadd x y)
    simpa [minusHom_unip'] using this
  · have := congrArg (fun w : Wd (Fz n) (Fq (2 * n)) => w.2.1) (hadd x y)
    simpa [minusHom_unip', add_assoc] using this
  · have := congrArg (fun w : Wd (Fz n) (Fq (2 * n)) => ((w.1 : Fz n) : Fq (2 * n)))
      (hadd x y)
    simpa [minusHom_unip', coe_Bval, coe_Qval, add_assoc] using this
  · have := congrArg (fun w : Wd (Fz n) (Fq (2 * n)) => ((w.2.2 : Fz n) : Fq (2 * n)))
      (htor t ht x)
    simpa [minusHom_diag', coe_Qval] using this
  · have := congrArg (fun w : Wd (Fz n) (Fq (2 * n)) => w.2.1) (htor t ht x)
    simpa [minusHom_diag'] using this
  · have := congrArg (fun w : Wd (Fz n) (Fq (2 * n)) => ((w.1 : Fz n) : Fq (2 * n)))
      (htor t ht x)
    simpa [minusHom_diag', coe_Qval] using this

theorem minusHom_zero' (A : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))) :
    minusHom n A (0 : Wd (Fz n) (Fq (2 * n))) = 0 := by
  have h := minusHom_isAdd n A (0 : Wd (Fz n) (Fq (2 * n))) 0
  rw [add_zero] at h
  exact left_eq_add.1 h

theorem natKey (F : Fq (2 * n) → Wd (Fz n) (Fq (2 * n)))
    (hadd : ∀ x y, F (x + y) = F x + minusHom n (unipotent x) (F y))
    (htor : ∀ (t : Fq (2 * n)) (ht : t ≠ 0) (x : Fq (2 * n)),
      F (t * t * x) = minusHom n (diagSL t ht) (F x)) :
    ∃ m₀ : Wd (Fz n) (Fq (2 * n)),
      (∀ (t : Fq (2 * n)) (ht : t ≠ 0), minusHom n (diagSL t ht) m₀ = m₀) ∧
      ∀ x, F x = minusHom n (unipotent x) m₀ - m₀ := by
  obtain ⟨hS, hY, hP, hSt, hYt, hPt⟩ := natScalar n F hadd htor
  have hS0 := scalar_S n (fun x => ((F x).2.2 : Fq (2 * n))) hS hSt
  by_cases hn : n = 1
  · obtain ⟨d, hdσ, -, hYd, hPd⟩ := scalar_one n hn (fun x => ((F x).1 : Fq (2 * n)))
      (fun x => (F x).2.1) (fun x => ((F x).2.2 : Fq (2 * n))) hS hY hP hSt hYt hPt
    refine ⟨(0, 0, ⟨d, (mem_Fz n d).2 hdσ⟩), ?_, fun x => ?_⟩
    · intro t ht
      rw [minusHom_diag']
      have hq : ((Qval n t : Fz n) : Fq (2 * n)) = 1 := by
        rw [coe_Qval]
        exact mul_sigR_eq_one_of_one n hn ht
      have hq' : Qval n t = 1 := Subtype.ext (by rw [hq]; rfl)
      simp [hq']
    · rw [minusHom_unip']
      refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ (Subtype.ext ?_))
      · have := hPd x
        simp only [Prod.fst_sub] at *
        simp [coe_Bval, coe_Qval]
        simpa [mul_comm] using this
      · have := hYd x
        simpa [mul_comm] using this
      · have := hS0 x
        simpa using this
  · have hn2 : 2 ≤ n := by have := NeZero.ne n; omega
    have hY' : ∀ x y, (F (x + y)).2.1 = (F x).2.1 + (F y).2.1 := fun x y => by
      rw [hY x y, hS0 y, zero_mul, add_zero]
    have hY0 := scalar_Y n hn2 (fun x => (F x).2.1) hY' hYt
    have hP' : ∀ x y, (((F (x + y)).1 : Fz n) : Fq (2 * n)) =
        ((F x).1 : Fq (2 * n)) + ((F y).1 : Fq (2 * n)) := fun x y => by
      rw [hP x y, hS0 y, hY0 y, map_zero]
      simp
    have hP0 := scalar_P n (fun x => ((F x).1 : Fq (2 * n))) hP' hPt
    refine ⟨0, fun t ht => ?_, fun x => ?_⟩
    · exact minusHom_zero' n _
    · rw [minusHom_zero', sub_zero]
      exact Prod.ext (Subtype.ext (hP0 x)) (Prod.ext (hY0 x) (Subtype.ext (hS0 x)))

end CFSG.CGT.PushingUpLit.CGT6X
