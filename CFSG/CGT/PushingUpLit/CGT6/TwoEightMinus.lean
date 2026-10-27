module

public import CFSG.CGT.PushingUpLit.CGT6.TwoEightGlue
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightIndex
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightAct
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightCard
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightNat
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightSL
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightMinusField

public section

namespace CFSG.CGT.PushingUpLit.CGT6.TwoEight

open Matrix

section Minus

variable (n : ℕ) [NeZero n]

@[expose] noncomputable def Bval (x y : Fq (2 * n)) : Fz n :=
  ⟨x * sigR n y + sigR n x * y, by
    rw [mem_Fz, map_add, map_mul, map_mul, sigR_sigR, sigR_sigR]
    ring⟩

@[expose] noncomputable def Qval (x : Fq (2 * n)) : Fz n :=
  ⟨x * sigR n x, by
    rw [mem_Fz, map_mul, sigR_sigR]
    exact mul_comm _ _⟩

theorem coe_Bval (x y : Fq (2 * n)) :
    (Bval n x y : Fq (2 * n)) = x * sigR n y + sigR n x * y := rfl

theorem coe_Qval (x : Fq (2 * n)) : (Qval n x : Fq (2 * n)) = x * sigR n x := rfl

@[expose] noncomputable def minusB : LinearMap.BilinForm (Fz n) (Fq (2 * n)) :=
  LinearMap.mk₂ (Fz n) (Bval n)
    (fun x₁ x₂ y => Subtype.ext (by simp only [coe_Bval, map_add, AddMemClass.coe_add]; ring))
    (fun c x y => Subtype.ext (by
      simp only [coe_Bval, Fz_smul, map_mul, sigR_Fz, smul_eq_mul, MulMemClass.coe_mul]; ring))
    (fun x y₁ y₂ => Subtype.ext (by simp only [coe_Bval, map_add, AddMemClass.coe_add]; ring))
    (fun c x y => Subtype.ext (by
      simp only [coe_Bval, Fz_smul, map_mul, sigR_Fz, smul_eq_mul, MulMemClass.coe_mul]; ring))

theorem minusB_apply (x y : Fq (2 * n)) : minusB n x y = Bval n x y := rfl

theorem coe_Bval_mul (x v : Fq (2 * n)) :
    (Bval n x (x * v) : Fq (2 * n)) = x * sigR n x * (v + sigR n v) := by
  rw [coe_Bval, map_mul]
  ring

@[expose] noncomputable def minusData : Data (Fz n) (Fq (2 * n)) where
  B := minusB n
  Q := Qval n
  alt x := Subtype.ext (by
    rw [minusB_apply, coe_Bval, mul_comm (sigR n x) x]
    exact F_add_self _)
  nondeg := by
    have key : ∀ x : Fq (2 * n), (∀ y, minusB n x y = 0) → x = 0 := by
      intro x hx
      by_contra hx0
      obtain ⟨w, hw⟩ := exists_sigR_ne n
      have h1 := hx (x * w)
      have h2 : ((minusB n x (x * w) : Fz n) : Fq (2 * n)) = 0 := by rw [h1]; rfl
      rw [minusB_apply, coe_Bval_mul] at h2
      have hσx : sigR n x ≠ 0 := fun h => hx0 (by
        have := congrArg (sigR n) h
        rwa [sigR_sigR, map_zero] at this)
      have hsum : w + sigR n w ≠ 0 := fun h => hw (by
        have : sigR n w = -w := by linear_combination h
        rw [this, CharTwo.neg_eq])
      exact mul_ne_zero (mul_ne_zero hx0 hσx) hsum h2
    refine ⟨key, fun y hy => key y fun x => ?_⟩
    have h3 := congrArg Subtype.val (hy x)
    rw [minusB_apply, coe_Bval] at h3
    rw [minusB_apply]
    apply Subtype.ext
    rw [coe_Bval]
    linear_combination h3
  Q_smul c x := Subtype.ext (by
    simp only [coe_Qval, Fz_smul, map_mul, sigR_Fz, MulMemClass.coe_mul]
    push_cast
    ring)
  Q_add x y := Subtype.ext (by
    simp only [minusB_apply, coe_Qval, coe_Bval, map_add, AddMemClass.coe_add]
    ring)

@[expose] noncomputable def cstar (X : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) :
    Matrix (Fin 2) (Fin 2) (Fq (2 * n)) :=
  (X.map (sigR n))ᵀ

omit [NeZero n] in
theorem cstar_apply (X : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) (i j : Fin 2) :
    cstar n X i j = sigR n (X j i) := rfl

omit [NeZero n] in
theorem cstar_mul (X Y : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) :
    cstar n (X * Y) = cstar n Y * cstar n X := by
  simp only [cstar, Matrix.map_mul, Matrix.transpose_mul]

theorem cstar_cstar (X : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) : cstar n (cstar n X) = X := by
  ext i j
  simp only [cstar_apply, sigR_sigR]

omit [NeZero n] in
theorem cstar_one : cstar n (1 : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) = 1 := by
  rw [cstar, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

omit [NeZero n] in
theorem mem_hermSub_iff (M : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) :
    M ∈ hermSub n ↔ cstar n M = M := by
  constructor
  · intro h
    ext i j
    rw [cstar_apply]
    exact (h i j).symm
  · intro h i j
    have := congrArg (fun X : Matrix (Fin 2) (Fin 2) (Fq (2 * n)) => X i j) h
    exact this.symm

theorem herm_act_mem (A : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))) (M : hermSub n) :
    (A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) * M.1 *
      cstar n (A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) ∈ hermSub n := by
  rw [mem_hermSub_iff]
  have hM : cstar n M.1 = M.1 := (mem_hermSub_iff n _).mp M.2
  simp only [cstar_mul, cstar_cstar, hM, Matrix.mul_assoc]

@[expose] noncomputable def minusAct (A : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n)))
    (m : Multiplicative (hermSub n)) : Multiplicative (hermSub n) :=
  Multiplicative.ofAdd ⟨_, herm_act_mem n A (Multiplicative.toAdd m)⟩

theorem omegaMinusAct_eq (A : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n)))
    (m : Multiplicative (hermSub n)) : omegaMinusAct n A m = minusAct n A m := by
  have h := herm_act_mem n A (Multiplicative.toAdd m)
  unfold omegaMinusAct minusAct
  split
  · rfl
  · rename_i h'
    exact absurd h h'

theorem minusAct_one (m : Multiplicative (hermSub n)) : minusAct n 1 m = m := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  show ((1 : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))) : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) *
    (Multiplicative.toAdd m).1 * cstar n ((1 : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))) :
      Matrix (Fin 2) (Fin 2) (Fq (2 * n))) = (Multiplicative.toAdd m).1
  rw [Matrix.SpecialLinearGroup.coe_one, cstar_one, Matrix.one_mul, Matrix.mul_one]

theorem minusAct_mul (A B : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n)))
    (m : Multiplicative (hermSub n)) : minusAct n (A * B) m = minusAct n A (minusAct n B m) := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  show ((A * B : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))) :
      Matrix (Fin 2) (Fin 2) (Fq (2 * n))) * (Multiplicative.toAdd m).1 *
    cstar n ((A * B : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))) :
      Matrix (Fin 2) (Fin 2) (Fq (2 * n))) =
    (A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) * ((B : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) *
      (Multiplicative.toAdd m).1 * cstar n (B : Matrix (Fin 2) (Fin 2) (Fq (2 * n)))) *
      cstar n (A : Matrix (Fin 2) (Fin 2) (Fq (2 * n)))
  rw [Matrix.SpecialLinearGroup.coe_mul, cstar_mul]
  simp only [Matrix.mul_assoc]

theorem herm_mk_mem (p : Fz n) (y : Fq (2 * n)) (s : Fz n) :
    (!![(p : Fq (2 * n)), y; sigR n y, (s : Fq (2 * n))] :
      Matrix (Fin 2) (Fin 2) (Fq (2 * n))) ∈ hermSub n := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact (sigR_Fz n p).symm
  · exact (sigR_sigR n y).symm
  · rfl
  · exact (sigR_Fz n s).symm

@[expose] noncomputable def minusCoord : hermSub n ≃+ Wd (Fz n) (Fq (2 * n)) where
  toFun M := (⟨M.1 0 0, (M.2 0 0).symm⟩, M.1 0 1, ⟨M.1 1 1, (M.2 1 1).symm⟩)
  invFun w := ⟨!![(w.1 : Fq (2 * n)), w.2.1; sigR n w.2.1, (w.2.2 : Fq (2 * n))],
    herm_mk_mem n w.1 w.2.1 w.2.2⟩
  left_inv M := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · exact (M.2 1 0).symm
    · rfl
  right_inv w := by
    rcases w with ⟨p, y, s⟩
    rfl
  map_add' M M' := rfl

theorem coe_minusCoord_symm (w : Wd (Fz n) (Fq (2 * n))) :
    ((minusCoord n).symm w).1 =
      !![(w.1 : Fq (2 * n)), w.2.1; sigR n w.2.1, (w.2.2 : Fq (2 * n))] := rfl

@[expose] noncomputable def minusKappa : Multiplicative (hermSub n) ≃ Wd (Fz n) (Fq (2 * n)) :=
  Multiplicative.toAdd.trans (minusCoord n).toEquiv

theorem omegaMinusAct_one (m : Multiplicative (hermSub n)) : omegaMinusAct n 1 m = m := by
  rw [omegaMinusAct_eq, minusAct_one]

theorem omegaMinusAct_mul (A B : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n)))
    (m : Multiplicative (hermSub n)) :
    omegaMinusAct n (A * B) m = omegaMinusAct n A (omegaMinusAct n B m) := by
  simp only [omegaMinusAct_eq, minusAct_mul]

@[expose] noncomputable def minusHom :
    Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n)) →*
      Equiv.Perm (Wd (Fz n) (Fq (2 * n))) :=
  actPerm (omegaMinusAct n) (omegaMinusAct_one n) (omegaMinusAct_mul n) (minusKappa n)

theorem minusHom_apply (A : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))) (M : hermSub n) :
    minusHom n A (minusCoord n M) =
      minusCoord n ⟨(A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) * M.1 *
        cstar n (A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))), herm_act_mem n A M⟩ := by
  have := actPerm_apply (omegaMinusAct n) (omegaMinusAct_one n) (omegaMinusAct_mul n)
    (minusKappa n) A (Multiplicative.ofAdd M)
  rw [omegaMinusAct_eq] at this
  exact this

theorem minusHom_val (A : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n)))
    (w : Wd (Fz n) (Fq (2 * n))) :
    minusHom n A w = minusCoord n ⟨(A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) *
      ((minusCoord n).symm w).1 * cstar n (A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))),
      herm_act_mem n A _⟩ := by
  have := minusHom_apply n A ((minusCoord n).symm w)
  rwa [AddEquiv.apply_symm_apply] at this

theorem minusHom_entries (A : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))) (p s : Fz n)
    (y : Fq (2 * n)) :
    ((minusHom n A (p, y, s)).1 : Fq (2 * n)) =
      ((A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) * !![(p : Fq (2 * n)), y; sigR n y,
        (s : Fq (2 * n))] * cstar n (A : Matrix (Fin 2) (Fin 2) (Fq (2 * n)))) 0 0 ∧
    (minusHom n A (p, y, s)).2.1 =
      ((A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) * !![(p : Fq (2 * n)), y; sigR n y,
        (s : Fq (2 * n))] * cstar n (A : Matrix (Fin 2) (Fin 2) (Fq (2 * n)))) 0 1 ∧
    ((minusHom n A (p, y, s)).2.2 : Fq (2 * n)) =
      ((A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) * !![(p : Fq (2 * n)), y; sigR n y,
        (s : Fq (2 * n))] * cstar n (A : Matrix (Fin 2) (Fin 2) (Fq (2 * n)))) 1 1 := by
  rw [minusHom_val]
  exact ⟨rfl, rfl, rfl⟩

open CFSG.SL2MinimalFaithful in
theorem minusHom_unip (x : Fq (2 * n)) : minusHom n (unipotent x) = sigPerm (minusData n) x := by
  ext ⟨p, y, s⟩ : 1
  obtain ⟨e1, e2, e3⟩ := minusHom_entries n (unipotent x) p s y
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ (Subtype.ext ?_))
  · rw [e1]
    show _ = (p : Fq (2 * n)) + (x * sigR n y + sigR n x * y) + x * sigR n x * (s : Fq (2 * n))
    simp only [coe_unipotent, cstar_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, map_one]
    ring
  · rw [e2]
    show _ = y + (s : Fq (2 * n)) * x
    simp only [coe_unipotent, cstar_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, map_zero, map_one]
    ring
  · rw [e3]
    show _ = (s : Fq (2 * n))
    simp only [coe_unipotent, cstar_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, map_zero, map_one]
    ring

theorem minusHom_lower (x : Fq (2 * n)) :
    minusHom n (lowerUnipotent (sigR n x)) = lamPerm (minusData n) x := by
  ext ⟨p, y, s⟩ : 1
  obtain ⟨e1, e2, e3⟩ := minusHom_entries n (lowerUnipotent (sigR n x)) p s y
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ (Subtype.ext ?_))
  · rw [e1]
    show _ = (p : Fq (2 * n))
    simp only [coe_lowerUnipotent, cstar_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, map_zero, map_one]
    ring
  · rw [e2]
    show _ = y + (p : Fq (2 * n)) * x
    simp only [coe_lowerUnipotent, cstar_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, map_one, sigR_sigR]
    ring
  · rw [e3]
    show _ = (s : Fq (2 * n)) + (x * sigR n y + sigR n x * y) + x * sigR n x * (p : Fq (2 * n))
    simp only [coe_lowerUnipotent, cstar_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, map_one, sigR_sigR]
    ring

theorem coe_Qt (w : Wd (Fz n) (Fq (2 * n))) :
    ((Qt (minusData n) w : Fz n) : Fq (2 * n)) = (((minusCoord n).symm w).1).det := by
  rcases w with ⟨p, y, s⟩
  have h : ((Qt (minusData n) (p, y, s) : Fz n) : Fq (2 * n)) =
      (p : Fq (2 * n)) * s + y * sigR n y := rfl
  rw [h, coe_minusCoord_symm, Matrix.det_fin_two_of, CharTwo.sub_eq_add]

theorem minusHom_Q (A : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n)))
    (w : Wd (Fz n) (Fq (2 * n))) : Qt (minusData n) (minusHom n A w) = Qt (minusData n) w := by
  apply Subtype.ext
  rw [coe_Qt, coe_Qt, minusHom_val, AddEquiv.symm_apply_apply]
  show ((A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) * ((minusCoord n).symm w).1 *
    cstar n (A : Matrix (Fin 2) (Fin 2) (Fq (2 * n)))).det = _
  have hc : (cstar n (A : Matrix (Fin 2) (Fin 2) (Fq (2 * n)))).det = 1 := by
    rw [cstar, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det, A.2, map_one]
  rw [Matrix.det_mul, Matrix.det_mul, hc, A.2, one_mul, mul_one]

theorem minusHom_isAdd (A : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))) :
    IsAddPerm (minusHom n A) := by
  intro w w'
  obtain ⟨M, rfl⟩ := (minusCoord n).surjective w
  obtain ⟨M', rfl⟩ := (minusCoord n).surjective w'
  rw [← map_add, minusHom_apply, minusHom_apply, minusHom_apply, ← map_add]
  congr 1
  apply Subtype.ext
  show (A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) * (M.1 + M'.1) *
      cstar n (A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) = _
  rw [Matrix.mul_add, Matrix.add_mul]
  rfl

theorem minusHom_injective : Function.Injective (minusHom n) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h : ∀ M : hermSub n, (g : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) * M.1 *
      cstar n (g : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) = M.1 := by
    intro M
    have := congrArg (fun τ : Equiv.Perm (Wd (Fz n) (Fq (2 * n))) => τ (minusCoord n M)) hg
    simp only [Equiv.Perm.coe_one, id] at this
    rw [minusHom_apply] at this
    exact congrArg Subtype.val ((minusCoord n).injective this)
  have hM1 := h ((minusCoord n).symm (1, 0, 0))
  have hM2 := h ((minusCoord n).symm (0, 0, 1))
  have hM3 := h ((minusCoord n).symm (0, 1, 0))
  rw [coe_minusCoord_symm] at hM1 hM2 hM3
  have e1 := congrFun (congrFun hM1 1) 1
  have e2 := congrFun (congrFun hM2 0) 0
  have e3 := congrFun (congrFun hM2 1) 1
  have e4 := congrFun (congrFun hM3 0) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, cstar_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    OneMemClass.coe_one, ZeroMemClass.coe_zero, map_zero, map_one, mul_zero, zero_mul, add_zero,
    zero_add, mul_one] at e1 e2 e3 e4
  have hc : (g : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) 1 0 = 0 := by
    rcases mul_eq_zero.mp e1 with h0 | h0
    · exact h0
    · have := congrArg (sigR n) h0
      rwa [sigR_sigR, map_zero] at this
  have hb : (g : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) 0 1 = 0 := by
    rcases mul_eq_zero.mp e2 with h0 | h0
    · exact h0
    · have := congrArg (sigR n) h0
      rwa [sigR_sigR, map_zero] at this
  rw [hb, hc, map_zero, mul_zero, zero_add] at e4
  have hdet := g.2
  rw [Matrix.det_fin_two, hb, hc, mul_zero, sub_zero] at hdet
  have hσd : sigR n ((g : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) 1 1) =
      (g : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) 1 1 := by
    have h1 : (g : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) 0 0 *
        (sigR n ((g : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) 1 1) -
          (g : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) 1 1) = 0 := by
      rw [mul_sub, e4, hdet, sub_self]
    rcases mul_eq_zero.mp h1 with h0 | h0
    · rw [h0, zero_mul] at hdet
      exact absurd hdet zero_ne_one
    · exact sub_eq_zero.mp h0
  have hd1 : (g : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) 1 1 = 1 := by
    rw [hσd] at e3
    rcases mul_self_eq_one_iff.mp e3 with h0 | h0
    · exact h0
    · rw [h0, CharTwo.neg_eq]
  have ha1 : (g : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) 0 0 = 1 := by
    rw [hd1, mul_one] at hdet
    exact hdet
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_one, ha1, hb, hc, hd1]

end Minus

theorem exists_ringEquiv_of_scalars {K : Type*} [Field K] [Finite K] [CharP K 2] (α : K → K)
    (hadd : ∀ x y, α (x + y) = α x + α y) (hinj : Function.Injective α) (h0 : α 0 = 0)
    (h : ∀ t : K, t ≠ 0 → ∃ ν : K, ∀ y, α (t * t * y) = ν * α y) :
    ∃ κ : K ≃+* K, ∀ c y, α (c * y) = κ c * α y := by
  have hu : α 1 ≠ 0 := fun h1 => one_ne_zero (hinj (h1.trans h0.symm))
  have hsq : ∀ c : K, c ≠ 0 → ∃ t : K, t ≠ 0 ∧ c = t * t := by
    intro c hc
    obtain ⟨t, ht⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
    exact ⟨t, fun h0 => hc (by rw [ht, h0, zero_mul]), ht⟩
  have hmul : ∀ c y, α (c * y) = (α c / α 1) * α y := by
    intro c y
    by_cases hc : c = 0
    · subst hc
      simp [h0]
    · obtain ⟨t, ht, rfl⟩ := hsq c hc
      obtain ⟨ν, hν⟩ := h t ht
      have h1 := hν 1
      rw [mul_one] at h1
      rw [hν y, h1]
      field_simp
  let gr : K →+* K :=
    { toFun := fun c => α c / α 1
      map_one' := div_self hu
      map_mul' := fun c d => by
        rw [hmul c d]
        field_simp
      map_zero' := by simp [h0]
      map_add' := fun c d => by rw [hadd, add_div] }
  have hbij : Function.Bijective gr := Finite.injective_iff_bijective.mp gr.injective
  exact ⟨RingEquiv.ofBijective gr hbij, fun c y => hmul c y⟩

section MinusIdx

open CFSG.SL2MinimalFaithful CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS6

variable (n : ℕ) [NeZero n]

theorem minusHom_diag_mul (t : Fq (2 * n)) (ht : t ≠ 0) (x : Fq (2 * n)) :
    minusHom n (diagSL t ht) * sigPerm (minusData n) x =
      sigPerm (minusData n) (t * t * x) * minusHom n (diagSL t ht) := by
  rw [← minusHom_unip, ← minusHom_unip, ← map_mul, ← map_mul, diagSL_mul_unipotent]

theorem minus_torus {a : Equiv.Perm (Wd (Fz n) (Fq (2 * n)))} (hsq : a * a = 1)
    (hS : ∀ x, ∃ x', a * sigPerm (minusData n) x * a⁻¹ = sigPerm (minusData n) x')
    (hnormΓ : ∀ g ∈ (minusHom n).range, a * g * a⁻¹ ∈ (minusHom n).range)
    (t : Fq (2 * n)) (ht : t ≠ 0) :
    ∃ ν : Fq (2 * n), ∀ y, alphaOf (minusData n) a (t * t * y) = ν * alphaOf (minusData n) a y := by
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right hsq
  have hα : ∀ x, a * sigPerm (minusData n) x =
      sigPerm (minusData n) (alphaOf (minusData n) a x) * a := fun x => by
    have := alphaOf_spec (minusData n) (hS x)
    rw [ha_inv] at this
    calc a * sigPerm (minusData n) x = a * sigPerm (minusData n) x * a * a := by
          rw [mul_assoc (a * sigPerm (minusData n) x) a a, hsq, mul_one]
      _ = sigPerm (minusData n) (alphaOf (minusData n) a x) * a := by rw [this]
  have hαα := alphaOf_alphaOf (minusData n) hsq hS
  obtain ⟨B', hB'⟩ : a * minusHom n (diagSL t ht) * a⁻¹ ∈ (minusHom n).range :=
    hnormΓ _ ⟨_, rfl⟩
  rw [ha_inv] at hB'
  have key : ∀ x, B' * unipotent x =
      unipotent (alphaOf (minusData n) a (t * t * alphaOf (minusData n) a x)) * B' := by
    intro x
    apply minusHom_injective n
    rw [map_mul, map_mul, minusHom_unip, minusHom_unip, hB']
    calc a * minusHom n (diagSL t ht) * a * sigPerm (minusData n) x
        = a * minusHom n (diagSL t ht) * (a * sigPerm (minusData n) x) := by
          simp only [mul_assoc]
      _ = a * minusHom n (diagSL t ht) *
          (sigPerm (minusData n) (alphaOf (minusData n) a x) * a) := by rw [hα x]
      _ = a * (minusHom n (diagSL t ht) * sigPerm (minusData n) (alphaOf (minusData n) a x)) * a := by
          simp only [mul_assoc]
      _ = a * (sigPerm (minusData n) (t * t * alphaOf (minusData n) a x) *
          minusHom n (diagSL t ht)) * a := by rw [minusHom_diag_mul]
      _ = (a * sigPerm (minusData n) (t * t * alphaOf (minusData n) a x)) *
          minusHom n (diagSL t ht) * a := by simp only [mul_assoc]
      _ = (sigPerm (minusData n) (alphaOf (minusData n) a (t * t * alphaOf (minusData n) a x)) * a) *
          minusHom n (diagSL t ht) * a := by rw [hα]
      _ = sigPerm (minusData n) (alphaOf (minusData n) a (t * t * alphaOf (minusData n) a x)) *
          (a * minusHom n (diagSL t ht) * a) := by simp only [mul_assoc]
  obtain ⟨b₁, -, hb⟩ := exists_sq_of_mul_unipotent B' _ key
  refine ⟨b₁ * b₁, fun y => ?_⟩
  have := hb (alphaOf (minusData n) a y)
  rwa [hαα y] at this

theorem minus_hidx (Ā' : Subgroup (Equiv.Perm (Wd (Fz n) (Fq (2 * n)))))
    (hadd : ∀ a ∈ Ā', IsAddPerm a) (hsq : ∀ a ∈ Ā', a * a = 1)
    (hnormΓ : ∀ a ∈ Ā', ∀ g ∈ (minusHom n).range, a * g * a⁻¹ ∈ (minusHom n).range)
    (hS : ∀ a ∈ Ā', ∀ x, ∃ x', a * sigPerm (minusData n) x * a⁻¹ = sigPerm (minusData n) x') :
    Nat.card Ā' ≤ 2 * Nat.card ↥(Ā' ⊓ Subgroup.centralizer
      (S0 (minusData n) : Set (Equiv.Perm (Wd (Fz n) (Fq (2 * n)))))) := by
  have hx₁ : (1 : Fq (2 * n)) ≠ 0 := one_ne_zero
  refine card_le_two_mul_inf_of_semilinear (minusData n) (K := Fq (2 * n)) hadd hsq hS hx₁ ?_ ?_
  · intro a ha
    have hNA := normAdd_alphaOf (minusData n) (hadd a ha) (hsq a ha) (hS a ha)
    obtain ⟨κ, hκ⟩ := exists_ringEquiv_of_scalars (alphaOf (minusData n) a) hNA.alpha_add hNA.inj
      hNA.alpha_zero (fun t ht => minus_torus n (hsq a ha) (hS a ha) (hnormΓ a ha) t ht)
    exact ⟨κ, fun c x => hκ c x⟩
  · intro a ha hlin
    have hαα := alphaOf_alphaOf (minusData n) (hsq a ha) (hS a ha)
    have hαy : ∀ y, alphaOf (minusData n) a y = y * alphaOf (minusData n) a 1 := fun y => by
      have := hlin y 1
      rwa [smul_eq_mul, smul_eq_mul, mul_one] at this
    have hu : alphaOf (minusData n) a 1 = 1 := by
      have h1 := hαα 1
      rw [hαy (alphaOf (minusData n) a 1)] at h1
      rcases mul_self_eq_one_iff.mp h1 with h0 | h0
      · exact h0
      · rw [h0, CharTwo.neg_eq]
    have hα : ∀ x, alphaOf (minusData n) a x = x := fun x => by rw [hαy, hu, mul_one]
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, rfl⟩
    have h1 := alphaOf_spec (minusData n) (hS a ha x)
    rw [hα x] at h1
    calc sigPerm (minusData n) x * a = (a * sigPerm (minusData n) x * a⁻¹) * a := by rw [h1]
      _ = a * sigPerm (minusData n) x := by group

theorem twoEight_minus {V : Type} [CommGroup V] [Finite V] {E A : Subgroup (MulAut V)} (hn : 2 ≤ n)
    (hAN : A ≤ Subgroup.normalizer (E : Set (MulAut V))) (hoff : IsOff A)
    (hnat : IsNatSectionBy (omegaMinusAct n) E (commV E) (commV E ⊓ fixV E))
    (hZ : commV E ⊓ fixV E = ⊥) : ⁅E, A⁆ = ⊥ := by
  classical
  rw [hZ] at hnat
  obtain ⟨hPE, θ, β, hβact⟩ := natSection_equiv hnat
  let φ : ↥(commV E) ≃ Wd (Fz n) (Fq (2 * n)) := β.toEquiv.trans (minusKappa n)
  have hφ : ∀ p q : ↥(commV E), φ (p * q) = φ p + φ q := fun p q => by
    show minusCoord n (Multiplicative.toAdd (β (p * q))) =
      minusCoord n (Multiplicative.toAdd (β p)) + minusCoord n (Multiplicative.toAdd (β q))
    rw [map_mul, toAdd_mul, map_add]
  have hAE : ∀ a ∈ A, ∀ e ∈ E, a * e * a⁻¹ ∈ E := fun a ha e he =>
    (Subgroup.mem_normalizer_iff.mp (hAN ha) e).mp he
  have hPA : ∀ a ∈ A, ∀ p ∈ commV E, a p ∈ commV E := fun a ha p hp =>
    G6.apply_mem_commV (fun x hx => hAE a ha x hx) hp
  have hequiv : ∀ (e : ↥E) (p : ↥(commV E)) (hp : (e : MulAut V) p ∈ commV E),
      φ ⟨(e : MulAut V) p, hp⟩ = minusHom n (θ e) (φ p) := by
    intro e p hp
    show minusKappa n (β ⟨(e : MulAut V) p, hp⟩) = minusHom n (θ e) (minusKappa n (β p))
    rw [hβact e p hp]
    exact (actPerm_apply (omegaMinusAct n) (omegaMinusAct_one n) (omegaMinusAct_mul n)
      (minusKappa n) (θ e) (β p)).symm
  have hSmax : ∀ T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))),
      IsPGroup 2 T → Nat.card T ≤ Nat.card (Fq (2 * n)) := fun T hT =>
    card_le_of_isPGroup_sl2 T hT
  refine twoEight_of_model (commV E) (minusData n) φ hφ hoff hAE hPE hPA (three_le_card_Fz n hn) θ
    (minusHom n) hequiv (fun x => ⟨unipotent x, minusHom_unip n x⟩) (one_ne_zero : (1 : Fq (2 * n)) ≠ 0)
    ⟨lowerUnipotent (sigR n 1), minusHom_lower n 1⟩ (minusHom_Q n) (minusHom_isAdd n)
    (minusHom_injective n) hSmax ⊥ ⊥
    (fun a _ e he => ⟨e, he, by
      have h1 : e = 1 := θ.injective (by rw [Subgroup.mem_bot.mp he, map_one])
      rw [h1]
      simp⟩)
    (fun a _ e he => ⟨e, he, by
      have h1 : e = 1 := θ.injective (by rw [Subgroup.mem_bot.mp he, map_one])
      rw [h1]
      simp⟩) ?_
  intro Ā' hadd hsq hΓ _ _ hS
  exact minus_hidx n Ā' hadd hsq hΓ hS

end MinusIdx

end CFSG.CGT.PushingUpLit.CGT6.TwoEight
