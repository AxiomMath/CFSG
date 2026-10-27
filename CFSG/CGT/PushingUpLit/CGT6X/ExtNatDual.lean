module

public import CFSG.CGT.PushingUpLit.CGT6X.ExtDual
public import CFSG.CGT.PushingUpLit.CGT6X.ExtNatCoh

public section

namespace CFSG.CGT.PushingUpLit.CGT6X

open CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6.TwoEight

variable (n : ℕ) [NeZero n]

@[expose] noncomputable def polarW (w w' : Wd (Fz n) (Fq (2 * n))) : Fz n :=
  w.1 * w'.2.2 + w'.1 * w.2.2 + (minusData n).B w.2.1 w'.2.1

theorem polarW_add_left (w w₁ w' : Wd (Fz n) (Fq (2 * n))) :
    polarW n (w + w₁) w' = polarW n w w' + polarW n w₁ w' := by
  simp only [polarW, Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
  ring

theorem polarW_add_right (w w' w₁ : Wd (Fz n) (Fq (2 * n))) :
    polarW n w (w' + w₁) = polarW n w w' + polarW n w w₁ := by
  simp only [polarW, Prod.fst_add, Prod.snd_add, map_add]
  ring

theorem polarW_comm (w w' : Wd (Fz n) (Fq (2 * n))) : polarW n w w' = polarW n w' w := by
  simp only [polarW]
  rw [B_symm (minusData n) w.2.1 w'.2.1]
  ring

omit [NeZero n] in
theorem two_eq_zero_Fz : (2 : Fz n) = 0 := CharP.cast_eq_zero _ 2

theorem polarW_eq (w w' : Wd (Fz n) (Fq (2 * n))) :
    polarW n w w' = Qt (minusData n) (w + w') + Qt (minusData n) w + Qt (minusData n) w' := by
  have h2 := two_eq_zero_Fz n
  simp only [polarW, Qt, Prod.fst_add, Prod.snd_add]
  rw [(minusData n).Q_add]
  linear_combination (-(w.1 * w.2.2 + w'.1 * w'.2.2 + (minusData n).Q w.2.1 +
    (minusData n).Q w'.2.1)) * h2

theorem polarW_inv (A : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n)))
    (w w' : Wd (Fz n) (Fq (2 * n))) :
    polarW n (minusHom n A w) (minusHom n A w') = polarW n w w' := by
  rw [polarW_eq, polarW_eq, ← minusHom_isAdd n A, minusHom_Q, minusHom_Q, minusHom_Q]

theorem polarW_smul_right (c : Fz n) (w w' : Wd (Fz n) (Fq (2 * n))) :
    polarW n w (c • w') = c * polarW n w w' := by
  simp only [polarW, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, B_smul_right]
  ring

theorem polarW_nondeg (w : Wd (Fz n) (Fq (2 * n))) (hw : w ≠ 0) :
    ∃ w' : Wd (Fz n) (Fq (2 * n)), polarW n w w' ≠ 0 := by
  obtain ⟨p, y, s⟩ := w
  by_cases hs : s = 0
  · by_cases hp : p = 0
    · have hy : y ≠ 0 := by
        rintro rfl
        exact hw (by rw [hs, hp]; rfl)
      obtain ⟨y', hy'⟩ := B_eq_zero_of_ne (minusData n) hy
      refine ⟨(0, y', 0), ?_⟩
      simpa [polarW, hs, hp] using hy'
    · exact ⟨(0, 0, 1), by simpa [polarW, hs] using hp⟩
  · exact ⟨(1, 0, 0), by simpa [polarW] using hs⟩

@[expose] def Vec : Type := Wd (Fz n) (Fq (2 * n))

noncomputable instance : AddCommGroup (Vec n) :=
  inferInstanceAs (AddCommGroup (Wd (Fz n) (Fq (2 * n))))

instance : Finite (Vec n) := inferInstanceAs (Finite (Wd (Fz n) (Fq (2 * n))))

omit [NeZero n] in
theorem vec_add_self (w : Vec n) : w + w = 0 := wd_add_self n w

noncomputable instance : Module (ZMod 2) (Vec n) :=
  AddCommGroup.zmodModule (fun w => by rw [two_nsmul]; exact vec_add_self n w)

instance : Module.Finite (ZMod 2) (Vec n) := Module.Finite.of_finite

@[expose] def Vec.toW (w : Vec n) : Wd (Fz n) (Fq (2 * n)) := w

@[expose] def Vec.ofW (w : Wd (Fz n) (Fq (2 * n))) : Vec n := w

omit [NeZero n] in
theorem Vec.toW_add (a b : Vec n) : (a + b).toW = a.toW + b.toW := rfl

omit [NeZero n] in
theorem Vec.toW_zero : (0 : Vec n).toW = 0 := rfl

omit [NeZero n] in
theorem Vec.toW_ofW (w : Wd (Fz n) (Fq (2 * n))) : (Vec.ofW n w).toW = w := rfl

omit [NeZero n] in
theorem exists_eps : ∃ ε : Fz n →+ ZMod 2, ε 1 = 1 :=
  exists_addMonoidHom_eq_one (A := Fz n) (fun a => by
    have := two_eq_zero_Fz n
    linear_combination a * this) one_ne_zero

theorem polarW_zero_left (w : Wd (Fz n) (Fq (2 * n))) : polarW n 0 w = 0 := by
  simp [polarW]

theorem polarW_zero_right (w : Wd (Fz n) (Fq (2 * n))) : polarW n w 0 = 0 := by
  simp [polarW]

theorem zmod_two_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

@[expose] noncomputable def bilVec (ε : Fz n →+ ZMod 2) : LinearMap.BilinForm (ZMod 2) (Vec n) :=
  LinearMap.mk₂ (ZMod 2) (fun w w' : Vec n => ε (polarW n w.toW w'.toW))
    (fun w₁ w₂ w' => by
      show ε (polarW n (w₁ + w₂).toW w'.toW) = _
      rw [Vec.toW_add, polarW_add_left, map_add])
    (fun c w w' => by
      rcases zmod_two_cases c with rfl | rfl
      · simp only [zero_smul]
        show ε (polarW n (0 : Vec n).toW w'.toW) = _
        rw [Vec.toW_zero, polarW_zero_left, map_zero]
      · simp only [one_smul])
    (fun w w₁ w₂ => by
      show ε (polarW n w.toW (w₁ + w₂).toW) = _
      rw [Vec.toW_add, polarW_add_right, map_add])
    (fun c w w' => by
      rcases zmod_two_cases c with rfl | rfl
      · simp only [zero_smul]
        show ε (polarW n w.toW (0 : Vec n).toW) = _
        rw [Vec.toW_zero, polarW_zero_right, map_zero]
      · simp only [one_smul])

theorem bilVec_apply (ε : Fz n →+ ZMod 2) (w w' : Vec n) :
    bilVec n ε w w' = ε (polarW n w.toW w'.toW) := rfl

theorem bilVec_nondeg (ε : Fz n →+ ZMod 2) (hε : ε 1 = 1) : (bilVec n ε).Nondegenerate := by
  have hleft : ∀ w : Vec n, (∀ w', bilVec n ε w w' = 0) → w = 0 := by
    intro w hw
    by_contra hne
    have hne' : w.toW ≠ 0 := hne
    obtain ⟨w₁, hw₁⟩ := polarW_nondeg n w.toW hne'
    have h := hw (Vec.ofW n ((polarW n w.toW w₁)⁻¹ • w₁))
    rw [bilVec_apply, Vec.toW_ofW, polarW_smul_right, inv_mul_cancel₀ hw₁, hε] at h
    exact one_ne_zero h
  refine ⟨hleft, fun w hw => hleft w (fun w' => ?_)⟩
  rw [bilVec_apply, polarW_comm]
  have := hw w'
  rwa [bilVec_apply] at this

theorem exists_dual_repr (ε : Fz n →+ ZMod 2) (hε : ε 1 = 1)
    (φ : Dual (NMod n)) :
    ∃ m : NMod n, ∀ v : NMod n, φ v = Multiplicative.ofAdd
      (ε (polarW n (Multiplicative.toAdd m) (Multiplicative.toAdd v))) := by
  let f : Vec n → ZMod 2 := fun w => Multiplicative.toAdd (φ (Multiplicative.ofAdd w.toW))
  have hadd : ∀ a b : Vec n, f (a + b) = f a + f b := fun a b => by
    show Multiplicative.toAdd (φ (Multiplicative.ofAdd (a + b).toW)) = _
    rw [Vec.toW_add, ofAdd_add, map_mul, toAdd_mul]
  have hzero : f 0 = 0 := by
    show Multiplicative.toAdd (φ (Multiplicative.ofAdd (0 : Vec n).toW)) = 0
    rw [Vec.toW_zero, ofAdd_zero, map_one]
    rfl
  let ℓ : Module.Dual (ZMod 2) (Vec n) :=
    { toFun := f
      map_add' := hadd
      map_smul' := fun c w => by
        rcases zmod_two_cases c with rfl | rfl
        · simp only [RingHom.id_apply, zero_smul]
          exact hzero
        · simp only [RingHom.id_apply, one_smul] }
  obtain ⟨m, hm⟩ : ∃ m : Vec n, ∀ w : Vec n, bilVec n ε m w = ℓ w :=
    ⟨((bilVec n ε).toDual (bilVec_nondeg n ε hε)).symm ℓ, fun w => by
      have := LinearEquiv.apply_symm_apply ((bilVec n ε).toDual (bilVec_nondeg n ε hε)) ℓ
      exact congrArg (fun f => f w) this⟩
  refine ⟨Multiplicative.ofAdd m.toW, fun v => ?_⟩
  have h := hm (Vec.ofW n (Multiplicative.toAdd v))
  rw [bilVec_apply, Vec.toW_ofW] at h
  rw [toAdd_ofAdd]
  have h' : Multiplicative.toAdd (φ v) = ε (polarW n m.toW (Multiplicative.toAdd v)) := h.symm
  exact (ofAdd_toAdd (φ v)).symm.trans (congrArg Multiplicative.ofAdd h')

@[expose] noncomputable def iotaFun (ε : Fz n →+ ZMod 2) (m : NMod n) : Dual (NMod n) where
  toFun v := Multiplicative.ofAdd
    (ε (polarW n (Multiplicative.toAdd m) (Multiplicative.toAdd v)))
  map_one' := by
    show Multiplicative.ofAdd (ε (polarW n (Multiplicative.toAdd m) 0)) = 1
    rw [polarW_zero_right, map_zero]
    rfl
  map_mul' v v' := by
    show Multiplicative.ofAdd (ε (polarW n (Multiplicative.toAdd m)
      (Multiplicative.toAdd v + Multiplicative.toAdd v'))) = _
    rw [polarW_add_right, map_add, ofAdd_add]

theorem iotaFun_apply (ε : Fz n →+ ZMod 2) (m v : NMod n) :
    iotaFun n ε m v = Multiplicative.ofAdd
      (ε (polarW n (Multiplicative.toAdd m) (Multiplicative.toAdd v))) := rfl

@[expose] noncomputable def iotaHom (ε : Fz n →+ ZMod 2) : NMod n →* Dual (NMod n) where
  toFun := iotaFun n ε
  map_one' := by
    refine MonoidHom.ext fun v => ?_
    rw [iotaFun_apply, dual_one_apply, toAdd_one, polarW_zero_left, map_zero]
    rfl
  map_mul' m m' := by
    refine MonoidHom.ext fun v => ?_
    rw [iotaFun_apply, dual_mul_apply, iotaFun_apply, iotaFun_apply, toAdd_mul, polarW_add_left,
      map_add, ofAdd_add]

theorem iotaHom_apply (ε : Fz n →+ ZMod 2) (m v : NMod n) :
    iotaHom n ε m v = Multiplicative.ofAdd
      (ε (polarW n (Multiplicative.toAdd m) (Multiplicative.toAdd v))) := rfl

theorem iotaHom_bijective (ε : Fz n →+ ZMod 2) (hε : ε 1 = 1) :
    Function.Bijective (iotaHom n ε) := by
  refine ⟨(injective_iff_map_eq_one (iotaHom n ε)).2 fun m hm => ?_, fun φ => ?_⟩
  ·
    have hz : ∀ w : Vec n, bilVec n ε (Vec.ofW n (Multiplicative.toAdd m)) w = 0 := by
      intro w
      have := congrArg (fun f : Dual (NMod n) => f (Multiplicative.ofAdd w.toW)) hm
      simp only [iotaHom_apply, toAdd_ofAdd, dual_one_apply] at this
      have h0 : Multiplicative.ofAdd (ε (polarW n (Multiplicative.toAdd m) w.toW)) =
          (1 : Multiplicative (ZMod 2)) := this
      exact congrArg Multiplicative.toAdd h0
    have := (bilVec_nondeg n ε hε).1 _ hz
    exact Multiplicative.toAdd.injective this
  · obtain ⟨m, hm⟩ := exists_dual_repr n ε hε φ
    exact ⟨m, MonoidHom.ext fun v => (iotaHom_apply n ε m v).trans (hm v).symm⟩

@[expose] noncomputable def iotaN (ε : Fz n →+ ZMod 2) (hε : ε 1 = 1) : NMod n ≃* Dual (NMod n) :=
  MulEquiv.ofBijective (iotaHom n ε) (iotaHom_bijective n ε hε)

theorem iotaN_apply (ε : Fz n →+ ZMod 2) (hε : ε 1 = 1) (m : NMod n) :
    iotaN n ε hε m = iotaHom n ε m := rfl

theorem polar_rhoW (A : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))) (m v : NMod n) :
    polarW n (Multiplicative.toAdd (rhoW n A m)) (Multiplicative.toAdd v) =
      polarW n (Multiplicative.toAdd m) (Multiplicative.toAdd (rhoW n A⁻¹ v)) := by
  have hv : Multiplicative.toAdd v =
      minusHom n A (Multiplicative.toAdd (rhoW n A⁻¹ v)) := by
    show Multiplicative.toAdd v = minusHom n A (minusHom n A⁻¹ (Multiplicative.toAdd v))
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  conv_lhs => rw [hv]
  exact polarW_inv n A (Multiplicative.toAdd m) _

theorem iotaN_equivariant (ε : Fz n →+ ZMod 2) (hε : ε 1 = 1)
    (A : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))) (m : NMod n) :
    iotaN n ε hε (rhoW n A m) = dualAct (rhoW n) A (iotaN n ε hε m) := by
  refine MonoidHom.ext fun v => ?_
  rw [iotaN_apply, iotaN_apply, dualAct_apply, iotaHom_apply, iotaHom_apply, polar_rhoW]

theorem h1_natDual {c : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n)) → Dual (NMod n)}
    (hc : IsCocycle (dualAct (rhoW n)) c) : IsCoboundary (dualAct (rhoW n)) c := by
  obtain ⟨ε, hε⟩ := exists_eps n
  exact isCoboundary_dual_of_equiv (iotaN n ε hε) (iotaN_equivariant n ε hε)
    (fun c hc => h1_nat n hc) hc

end CFSG.CGT.PushingUpLit.CGT6X
