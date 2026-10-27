module

public import CFSG.GF2Type.Smith1979.GammaU.Group

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU

abbrev G12 : Type := V12 ≃ₗ[ZMod 2] V12

@[expose] def omegaPow (c : ZMod 3) (p : ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 :=
  if c = 0 then p else if c = 1 then (p.2, p.1 + p.2) else (p.1 + p.2, p.1)

theorem omegaPow_add : ∀ (c c' : ZMod 3) (p : ZMod 2 × ZMod 2),
    omegaPow (c + c') p = omegaPow c (omegaPow c' p) := by decide

theorem omegaPow_zero (p : ZMod 2 × ZMod 2) : omegaPow 0 p = p := by simp [omegaPow]

theorem omegaPow_add_pair : ∀ (c : ZMod 3) (p p' : ZMod 2 × ZMod 2),
    omegaPow c (p + p') = omegaPow c p + omegaPow c p' := by decide

theorem omegaPow_eq_zero_iff : ∀ (c : ZMod 3) (p : ZMod 2 × ZMod 2), omegaPow c p = 0 ↔ p = 0 := by
  decide

@[expose] def diagFun (c : Fin 6 → ZMod 3) (x : V12) : V12 :=
  Fin.append (fun i => (omegaPow (c i) (x (lo i), x (hi i))).1)
    (fun i => (omegaPow (c i) (x (lo i), x (hi i))).2)

theorem diagFun_lo (c : Fin 6 → ZMod 3) (x : V12) (i : Fin 6) :
    diagFun c x (lo i) = (omegaPow (c i) (x (lo i), x (hi i))).1 :=
  Fin.append_left _ _ i

theorem diagFun_hi (c : Fin 6 → ZMod 3) (x : V12) (i : Fin 6) :
    diagFun c x (hi i) = (omegaPow (c i) (x (lo i), x (hi i))).2 :=
  Fin.append_right _ _ i

@[expose] def diagLin (c : Fin 6 → ZMod 3) : V12 →ₗ[ZMod 2] V12 where
  toFun := diagFun c
  map_add' x y := by
    refine ext_lo_hi (fun i => ?_) (fun i => ?_)
    · simp only [Pi.add_apply, diagFun_lo]
      have := omegaPow_add_pair (c i) (x (lo i), x (hi i)) (y (lo i), y (hi i))
      exact congrArg Prod.fst this
    · simp only [Pi.add_apply, diagFun_hi]
      have := omegaPow_add_pair (c i) (x (lo i), x (hi i)) (y (lo i), y (hi i))
      exact congrArg Prod.snd this
  map_smul' a x := by
    have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases h a with rfl | rfl
    · simp only [RingHom.id_apply, zero_smul]
      refine ext_lo_hi (fun i => ?_) (fun i => ?_)
      · have := (omegaPow_eq_zero_iff (c i) (0, 0)).2 rfl
        simp only [Pi.zero_apply, diagFun_lo]
        exact congrArg Prod.fst this
      · have := (omegaPow_eq_zero_iff (c i) (0, 0)).2 rfl
        simp only [Pi.zero_apply, diagFun_hi]
        exact congrArg Prod.snd this
    · simp

theorem diagLin_zero : diagLin (0 : Fin 6 → ZMod 3) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  refine ext_lo_hi (fun i => ?_) (fun i => ?_)
  · show diagFun 0 x (lo i) = x (lo i)
    rw [diagFun_lo]
    simp [omegaPow_zero]
  · show diagFun 0 x (hi i) = x (hi i)
    rw [diagFun_hi]
    simp [omegaPow_zero]

theorem diagLin_add (c c' : Fin 6 → ZMod 3) :
    diagLin (c + c') = diagLin c ∘ₗ diagLin c' := by
  refine LinearMap.ext fun x => ?_
  refine ext_lo_hi (fun i => ?_) (fun i => ?_)
  · show diagFun (c + c') x (lo i) = diagFun c (diagFun c' x) (lo i)
    simp only [diagFun_lo, diagFun_hi, Pi.add_apply, omegaPow_add]
  · show diagFun (c + c') x (hi i) = diagFun c (diagFun c' x) (hi i)
    simp only [diagFun_lo, diagFun_hi, Pi.add_apply, omegaPow_add]

@[expose] def diagE (c : Fin 6 → ZMod 3) : G12 :=
  LinearEquiv.ofLinear (diagLin c) (diagLin (-c))
    (by rw [← diagLin_add, add_neg_cancel, diagLin_zero])
    (by rw [← diagLin_add, neg_add_cancel, diagLin_zero])

@[simp] theorem diagE_apply (c : Fin 6 → ZMod 3) (x : V12) : diagE c x = diagFun c x := rfl


@[expose] def permFun (π : Equiv.Perm (Fin 6)) (x : V12) : V12 :=
  Fin.append (fun i => x (lo (π.symm i))) (fun i => x (hi (π.symm i)))

theorem permFun_lo (π : Equiv.Perm (Fin 6)) (x : V12) (i : Fin 6) :
    permFun π x (lo i) = x (lo (π.symm i)) :=
  Fin.append_left _ _ i

theorem permFun_hi (π : Equiv.Perm (Fin 6)) (x : V12) (i : Fin 6) :
    permFun π x (hi i) = x (hi (π.symm i)) :=
  Fin.append_right _ _ i

@[expose] def permLin (π : Equiv.Perm (Fin 6)) : V12 →ₗ[ZMod 2] V12 where
  toFun := permFun π
  map_add' x y := by
    refine ext_lo_hi (fun i => ?_) (fun i => ?_)
    · simp only [Pi.add_apply, permFun_lo]
    · simp only [Pi.add_apply, permFun_hi]
  map_smul' a x := by
    refine ext_lo_hi (fun i => ?_) (fun i => ?_)
    · simp only [Pi.smul_apply, permFun_lo, RingHom.id_apply]
    · simp only [Pi.smul_apply, permFun_hi, RingHom.id_apply]

theorem permLin_one : permLin (1 : Equiv.Perm (Fin 6)) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  refine ext_lo_hi (fun i => ?_) (fun i => ?_)
  · show permFun 1 x (lo i) = x (lo i)
    rw [permFun_lo]; rfl
  · show permFun 1 x (hi i) = x (hi i)
    rw [permFun_hi]; rfl

theorem permLin_mul (π π' : Equiv.Perm (Fin 6)) :
    permLin (π * π') = permLin π ∘ₗ permLin π' := by
  refine LinearMap.ext fun x => ?_
  refine ext_lo_hi (fun i => ?_) (fun i => ?_)
  · show permFun (π * π') x (lo i) = permFun π (permFun π' x) (lo i)
    rw [permFun_lo, permFun_lo, permFun_lo]
    simp [Equiv.Perm.mul_def, Equiv.symm_trans_apply]
  · show permFun (π * π') x (hi i) = permFun π (permFun π' x) (hi i)
    rw [permFun_hi, permFun_hi, permFun_hi]
    simp [Equiv.Perm.mul_def, Equiv.symm_trans_apply]

@[expose] def permE (π : Equiv.Perm (Fin 6)) : G12 :=
  LinearEquiv.ofLinear (permLin π) (permLin π⁻¹)
    (by rw [← permLin_mul, mul_inv_cancel, permLin_one])
    (by rw [← permLin_mul, inv_mul_cancel, permLin_one])

@[simp] theorem permE_apply (π : Equiv.Perm (Fin 6)) (x : V12) : permE π x = permFun π x := rfl

@[expose] def frobFun (x : V12) : V12 :=
  Fin.append (fun i => x (lo i) + x (hi i)) (fun i => x (hi i))

theorem frobFun_lo (x : V12) (i : Fin 6) : frobFun x (lo i) = x (lo i) + x (hi i) :=
  Fin.append_left _ _ i

theorem frobFun_hi (x : V12) (i : Fin 6) : frobFun x (hi i) = x (hi i) :=
  Fin.append_right _ _ i

@[expose] def frobLin : V12 →ₗ[ZMod 2] V12 where
  toFun := frobFun
  map_add' x y := by
    refine ext_lo_hi (fun i => ?_) (fun i => ?_)
    · simp only [Pi.add_apply, frobFun_lo]; ring
    · simp only [Pi.add_apply, frobFun_hi]
  map_smul' a x := by
    refine ext_lo_hi (fun i => ?_) (fun i => ?_)
    · simp only [Pi.smul_apply, frobFun_lo, smul_eq_mul, RingHom.id_apply]; ring
    · simp only [Pi.smul_apply, frobFun_hi, RingHom.id_apply]

theorem frobLin_frobLin : frobLin ∘ₗ frobLin = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
  refine ext_lo_hi (fun i => ?_) (fun i => ?_)
  · show frobFun (frobFun x) (lo i) = x (lo i)
    rw [frobFun_lo, frobFun_lo, frobFun_hi, add_assoc, h2, add_zero]
  · show frobFun (frobFun x) (hi i) = x (hi i)
    rw [frobFun_hi, frobFun_hi]

@[expose] def frobE : G12 :=
  LinearEquiv.ofLinear frobLin frobLin frobLin_frobLin frobLin_frobLin

@[simp] theorem frobE_apply (x : V12) : frobE x = frobFun x := rfl

@[expose] def theta0e : G12 :=
  LinearEquiv.ofLinear theta0 (theta0 ∘ₗ theta0)
    (LinearMap.ext fun x => theta0_theta0_theta0 x)
    (LinearMap.ext fun x => by
      show theta0 (theta0 (theta0 x)) = x
      exact theta0_theta0_theta0 x)

@[simp] theorem theta0e_apply (x : V12) : theta0e x = theta0 x := rfl

@[expose] def plane (i : Fin 6) : Submodule (ZMod 2) V12 where
  carrier := {x | ∀ j : Fin 6, j ≠ i → x (lo j) = 0 ∧ x (hi j) = 0}
  zero_mem' := fun j _ => ⟨rfl, rfl⟩
  add_mem' := fun {x y} hx hy j hj => by
    obtain ⟨h1, h2⟩ := hx j hj
    obtain ⟨h3, h4⟩ := hy j hj
    exact ⟨by rw [Pi.add_apply, h1, h3, add_zero], by rw [Pi.add_apply, h2, h4, add_zero]⟩
  smul_mem' := fun a x hx j hj => by
    obtain ⟨h1, h2⟩ := hx j hj
    exact ⟨by rw [Pi.smul_apply, h1, smul_zero], by rw [Pi.smul_apply, h2, smul_zero]⟩

theorem mem_plane_iff (i : Fin 6) (x : V12) :
    x ∈ plane i ↔ ∀ j : Fin 6, j ≠ i → x (lo j) = 0 ∧ x (hi j) = 0 := Iff.rfl

end CFSG.GF2Type.Smith1979.IdxFour
