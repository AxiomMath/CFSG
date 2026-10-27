module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.Basic

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar

section Descent

variable {G Y : Type*} [Group G] [Group Y]

@[expose] noncomputable def restrictAut (j : Y →* G) (hj : Function.Injective j) (θ : MulAut G)
    (h1 : ∀ y, ∃ y', j y' = θ (j y)) (h2 : ∀ y, ∃ y', j y' = θ⁻¹ (j y)) : MulAut Y :=
  { toFun := fun y => Classical.choose (h1 y)
    invFun := fun y => Classical.choose (h2 y)
    left_inv := fun y => hj (by
      show j (Classical.choose (h2 (Classical.choose (h1 y)))) = j y
      rw [Classical.choose_spec (h2 _), Classical.choose_spec (h1 y)]
      simp)
    right_inv := fun y => hj (by
      show j (Classical.choose (h1 (Classical.choose (h2 y)))) = j y
      rw [Classical.choose_spec (h1 _), Classical.choose_spec (h2 y)]
      simp)
    map_mul' := fun x y => hj (by
      have e1 := Classical.choose_spec (h1 (x * y))
      have e2 := Classical.choose_spec (h1 x)
      have e3 := Classical.choose_spec (h1 y)
      show j (Classical.choose (h1 (x * y))) = j (Classical.choose (h1 x) * Classical.choose (h1 y))
      rw [map_mul j (Classical.choose (h1 x)) (Classical.choose (h1 y)), e1, e2, e3, map_mul,
        map_mul]) }

theorem restrictAut_spec (j : Y →* G) (hj : Function.Injective j) (θ : MulAut G)
    (h1 : ∀ y, ∃ y', j y' = θ (j y)) (h2 : ∀ y, ∃ y', j y' = θ⁻¹ (j y)) (y : Y) :
    j (restrictAut j hj θ h1 h2 y) = θ (j y) :=
  Classical.choose_spec (h1 y)

theorem restrictAut_pow_spec (j : Y →* G) (hj : Function.Injective j) (θ : MulAut G)
    (h1 : ∀ y, ∃ y', j y' = θ (j y)) (h2 : ∀ y, ∃ y', j y' = θ⁻¹ (j y)) (n : ℕ) (y : Y) :
    j ((restrictAut j hj θ h1 h2 ^ n) y) = (θ ^ n) (j y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ', MulAut.mul_apply, MulAut.mul_apply, restrictAut_spec, ih]

theorem restrictAut_orderOf_dvd (j : Y →* G) (hj : Function.Injective j) (θ : MulAut G)
    (h1 : ∀ y, ∃ y', j y' = θ (j y)) (h2 : ∀ y, ∃ y', j y' = θ⁻¹ (j y)) :
    orderOf (restrictAut j hj θ h1 h2) ∣ orderOf θ := by
  refine orderOf_dvd_of_pow_eq_one (MulEquiv.ext fun y => hj ?_)
  rw [restrictAut_pow_spec, pow_orderOf_eq_one]
  rfl

theorem faithfulAt_of_descent (x : MulAut G) (j : Y →* G) (hj : Function.Injective j)
    (hfixed : ∀ y, x (j y) = j y) (hrange : ∀ w, x w = w → ∃ y, j y = w)
    (φ : MulAut Y) (Θ : MulAut G) (hΘ : ∀ y, j (φ y) = Θ (j y))
    (hφ : FaithfulAt 3 φ) (hx : FaithfulAt 3 x)
    (θ : MulAut G) (hθ3 : Nat.Coprime 3 (orderOf θ)) (hθx : θ * x = x * θ)
    (hθΘ : θ * Θ = Θ * θ) (hθfix : ∀ y, φ y = y → θ (j y) = j y) : θ = 1 := by
  have hθx' : ∀ w, x (θ w) = θ (x w) := fun w => (congrArg (fun e : MulAut G => e w) hθx).symm
  have hinv : θ⁻¹ * x = x * θ⁻¹ :=
    calc θ⁻¹ * x = θ⁻¹ * (x * θ) * θ⁻¹ := by group
      _ = θ⁻¹ * (θ * x) * θ⁻¹ := by rw [hθx]
      _ = x * θ⁻¹ := by group
  have hθx'' : ∀ w, x (θ⁻¹ w) = θ⁻¹ (x w) := fun w =>
    (congrArg (fun e : MulAut G => e w) hinv).symm
  have h1 : ∀ y, ∃ y', j y' = θ (j y) := fun y => hrange _ (by rw [hθx', hfixed])
  have h2 : ∀ y, ∃ y', j y' = θ⁻¹ (j y) := fun y => hrange _ (by rw [hθx'', hfixed])
  have hζ3 : Nat.Coprime 3 (orderOf (restrictAut j hj θ h1 h2)) :=
    Nat.Coprime.coprime_dvd_right (restrictAut_orderOf_dvd j hj θ h1 h2) hθ3
  have hζφ : restrictAut j hj θ h1 h2 * φ = φ * restrictAut j hj θ h1 h2 :=
    MulEquiv.ext fun y => hj (by
      change j (restrictAut j hj θ h1 h2 (φ y)) = j (φ (restrictAut j hj θ h1 h2 y))
      rw [restrictAut_spec, hΘ, hΘ, restrictAut_spec]
      exact congrArg (fun e : MulAut G => e (j y)) hθΘ)
  have hζfix : ∀ t ∈ fixSub φ, restrictAut j hj θ h1 h2 t = t := fun t ht =>
    hj (by rw [restrictAut_spec]; exact hθfix t (mem_fixSub.1 ht))
  have hζ1 : restrictAut j hj θ h1 h2 = 1 := hφ _ hζ3 hζφ hζfix
  refine hx θ hθ3 hθx fun w hw => ?_
  obtain ⟨y, rfl⟩ := hrange w (mem_fixSub.1 hw)
  have h := restrictAut_spec j hj θ h1 h2 y
  rw [hζ1] at h
  exact h.symm

end Descent

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
