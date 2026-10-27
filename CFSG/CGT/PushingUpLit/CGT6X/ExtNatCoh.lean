module

public import CFSG.CGT.PushingUpLit.CGT6X.ExtNat
public import CFSG.CGT.PushingUpLit.CGT6X.ExtBorel

public section

namespace CFSG.CGT.PushingUpLit.CGT6X

open CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6.TwoEight CFSG.SL2MinimalFaithful

variable (n : ℕ) [NeZero n]

abbrev NMod : Type := Multiplicative (Wd (Fz n) (Fq (2 * n)))

omit [NeZero n] in
theorem wd_add_self (w : Wd (Fz n) (Fq (2 * n))) : w + w = 0 := by
  have h2 : ∀ x : Fq (2 * n), x + x = 0 := fun x => by
    have := two_eq_zero_Fq n
    linear_combination x * this
  refine Prod.ext (Subtype.ext (h2 _)) (Prod.ext (h2 _) (Subtype.ext (h2 _)))

omit [NeZero n] in
theorem NMod_sq (v : NMod n) : v ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, two_nsmul]
  exact wd_add_self n _

noncomputable instance :
    MulDistribMulAction (Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))) (NMod n) where
  smul A v := Multiplicative.ofAdd (minusHom n A (Multiplicative.toAdd v))
  one_smul v := by
    show Multiplicative.ofAdd (minusHom n 1 (Multiplicative.toAdd v)) = v
    rw [map_one]
    rfl
  mul_smul A B v := by
    show Multiplicative.ofAdd (minusHom n (A * B) (Multiplicative.toAdd v)) =
      Multiplicative.ofAdd (minusHom n A (minusHom n B (Multiplicative.toAdd v)))
    rw [map_mul]
    rfl
  smul_mul A v w := by
    show Multiplicative.ofAdd (minusHom n A (Multiplicative.toAdd v + Multiplicative.toAdd w)) = _
    rw [minusHom_isAdd n A, ofAdd_add]
    rfl
  smul_one A := by
    show Multiplicative.ofAdd (minusHom n A (0 : Wd (Fz n) (Fq (2 * n)))) = 1
    rw [minusHom_zero']
    rfl

@[expose] noncomputable def rhoW :
    Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n)) →* MulAut (NMod n) :=
  MulDistribMulAction.toMulAut _ _

theorem rhoW_apply (A : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))) (v : NMod n) :
    rhoW n A v = Multiplicative.ofAdd (minusHom n A (Multiplicative.toAdd v)) := rfl

theorem h1_nat {c : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n)) → NMod n}
    (hc : IsCocycle (rhoW n) c) : IsCoboundary (rhoW n) c := by
  refine coboundary_of_borel (NMod_sq n) (rhoW n) ?_ hc
  intro f _ hfadd hftor
  obtain ⟨m₀, hfix, hcob⟩ := natKey n (fun x => Multiplicative.toAdd (f x))
    (fun x y => by
      have := congrArg Multiplicative.toAdd (hfadd x y)
      simpa [rhoW_apply] using this)
    (fun t ht x => by
      have := congrArg Multiplicative.toAdd (hftor t ht x)
      simpa [rhoW_apply] using this)
  refine ⟨Multiplicative.ofAdd m₀, fun t ht => ?_, fun x => ?_⟩
  · rw [rhoW_apply]
    exact congrArg Multiplicative.ofAdd (hfix t ht)
  · apply Multiplicative.toAdd.injective
    rw [hcob x, toAdd_mul, toAdd_inv, rhoW_apply, toAdd_ofAdd, toAdd_ofAdd]
    exact sub_eq_add_neg _ _

end CFSG.CGT.PushingUpLit.CGT6X
