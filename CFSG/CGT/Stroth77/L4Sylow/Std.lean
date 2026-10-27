module

public import CFSG.CGT.Stroth77.TorusNormalForm
public import CFSG.CGT.Stroth77.TypePredicates
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Ref

public section

namespace CFSG.CGT.Stroth77.L4Sylow

open Equiv Matrix CFSG.GH74.GLS.Stage1.Thm3.Sec8

@[expose] def bVec (w : Fin 3 → ℤ) : Fin 4 → ℤ :=
  ![-3 * w 0 + w 1 + w 2, w 0, w 0 - w 1, w 0 - w 2]

@[expose] def cVec (d : Fin 4 → ℤ) : Fin 3 → ℤ := ![d 1, d 1 - d 2, d 1 - d 3]

theorem cVec_bVec (w : Fin 3 → ℤ) : cVec (bVec w) = w := by
  funext i
  fin_cases i <;> simp [bVec, cVec]

theorem bVec_cVec {d : Fin 4 → ℤ} (hd : ∑ i, d i = 0) : bVec (cVec d) = d := by
  rw [Fin.sum_univ_four] at hd
  funext i
  fin_cases i <;> simp [bVec, cVec] <;> linarith

theorem sum_bVec (w : Fin 3 → ℤ) : ∑ i, bVec w i = 0 := by
  simp [bVec, Fin.sum_univ_four]
  ring

theorem bVec_add (w w' : Fin 3 → ℤ) : bVec (w + w') = bVec w + bVec w' := by
  funext i
  fin_cases i <;> simp [bVec] <;> ring

theorem bVec_smul (z : ℤ) (w : Fin 3 → ℤ) : bVec (z • w) = z • bVec w := by
  funext i
  fin_cases i <;> simp [bVec] <;> ring

theorem cVec_add (d d' : Fin 4 → ℤ) : cVec (d + d') = cVec d + cVec d' := by
  funext i
  fin_cases i <;> simp [cVec] <;> ring

theorem cVec_smul (z : ℤ) (d : Fin 4 → ℤ) : cVec (z • d) = z • cVec d := by
  funext i
  fin_cases i <;> simp [cVec] <;> ring

@[expose] def wVec (π : Perm (Fin 4)) (w : Fin 3 → ℤ) : Fin 3 → ℤ :=
  cVec fun i => bVec w (π⁻¹ i)

theorem wVec_add (π : Perm (Fin 4)) (w w' : Fin 3 → ℤ) :
    wVec π (w + w') = wVec π w + wVec π w' := by
  rw [wVec, wVec, wVec, ← cVec_add]
  congr 1
  funext i
  rw [bVec_add]
  rfl

theorem wVec_smul (π : Perm (Fin 4)) (z : ℤ) (w : Fin 3 → ℤ) :
    wVec π (z • w) = z • wVec π w := by
  rw [wVec, wVec, ← cVec_smul]
  congr 1
  funext i
  rw [bVec_smul]
  rfl

theorem wVec_wVec (π σ : Perm (Fin 4)) (w : Fin 3 → ℤ) :
    wVec π (wVec σ w) = wVec (π * σ) w := by
  have hsum : ∑ i, bVec w (σ⁻¹ i) = 0 := by
    rw [Equiv.sum_comp σ⁻¹ (bVec w)]
    exact sum_bVec w
  rw [wVec, wVec, bVec_cVec hsum, wVec, mul_inv_rev]
  rfl

theorem wVec_one (w : Fin 3 → ℤ) : wVec 1 w = w := by
  rw [wVec]
  exact cVec_bVec w

@[expose] def wM (π : Perm (Fin 4)) : IntMat := Matrix.of fun r j => wVec π (Pi.single j 1) r

theorem eq_sum_single_three (w : Fin 3 → ℤ) :
    w = w 0 • Pi.single 0 1 + w 1 • Pi.single 1 1 + w 2 • Pi.single 2 1 := by
  funext i
  fin_cases i <;> simp

theorem wM_mulVec (π : Perm (Fin 4)) (w : Fin 3 → ℤ) : wM π *ᵥ w = wVec π w := by
  conv_rhs => rw [eq_sum_single_three w, wVec_add, wVec_add, wVec_smul, wVec_smul, wVec_smul]
  funext r
  simp only [Matrix.mulVec, dotProduct, wM, Matrix.of_apply, Fin.sum_univ_three, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem four_dvd_wM (π : Perm (Fin 4)) {r : Fin 3} (hr : r ≠ 0) : (4 : ℤ) ∣ wM π r 0 := by
  have h : ∀ p q : Fin 4, (4 : ℤ) ∣ ![-3, 1, 1, 1] p - ![-3, 1, 1, 1] q := by decide
  fin_cases r
  · exact absurd rfl hr
  · simpa [wM, wVec, cVec, bVec] using h (π⁻¹ 1) (π⁻¹ 2)
  · simpa [wM, wVec, cVec, bVec] using h (π⁻¹ 1) (π⁻¹ 3)

theorem compat_wM (m : ℕ) (π : Perm (Fin 4)) : Compat (Type200.k m) (wM π) := by
  have hk0 : Type200.k m 0 = m := rfl
  have hk : ∀ r : Fin 3, r ≠ 0 → Type200.k m r = m + 2 := by
    intro r hr
    fin_cases r
    · exact absurd rfl hr
    · rfl
    · rfl
  intro i j
  by_cases hi : i = 0
  · subst hi
    refine dvd_mul_of_dvd_left (pow_dvd_pow 2 ?_) _
    rw [hk0]
    by_cases hj : j = 0
    · rw [hj, hk0]
    · rw [hk j hj]
      omega
  · rw [hk i hi]
    by_cases hj : j = 0
    · subst hj
      obtain ⟨x, hx⟩ := four_dvd_wM π hi
      rw [hk0, hx]
      exact ⟨x, by ring⟩
    · rw [hk j hj]
      exact dvd_mul_right _ _

theorem matAct_wM_ofInt (m : ℕ) (π : Perm (Fin 4)) (w : Fin 3 → ℤ) :
    matAct (Type200.k m) (wM π) (compat_wM m π) (Torus.ofInt _ w) =
      Torus.ofInt _ (wVec π w) := by
  rw [matAct_ofInt, wM_mulVec]

theorem matAct_wM_wM (m : ℕ) (π σ : Perm (Fin 4)) (x : Torus (Type200.k m)) :
    matAct _ (wM π) (compat_wM m π) (matAct _ (wM σ) (compat_wM m σ) x) =
      matAct _ (wM (π * σ)) (compat_wM m (π * σ)) x := by
  obtain ⟨w, rfl⟩ := Torus.exists_ofInt x
  rw [matAct_wM_ofInt, matAct_wM_ofInt, matAct_wM_ofInt, wVec_wVec]

theorem matAct_wM_one (m : ℕ) (x : Torus (Type200.k m)) :
    matAct _ (wM 1) (compat_wM m 1) x = x := by
  obtain ⟨w, rfl⟩ := Torus.exists_ofInt x
  rw [matAct_wM_ofInt, wVec_one]

@[expose] def autWM (m : ℕ) (π : Perm (Fin 4)) : MulAut (Multiplicative (Torus (Type200.k m))) where
  toFun x := Multiplicative.ofAdd (matAct _ (wM π) (compat_wM m π) (Multiplicative.toAdd x))
  invFun x := Multiplicative.ofAdd (matAct _ (wM π⁻¹) (compat_wM m π⁻¹) (Multiplicative.toAdd x))
  left_inv x := by
    simp only [toAdd_ofAdd]
    rw [matAct_wM_wM, inv_mul_cancel, matAct_wM_one]
    rfl
  right_inv x := by
    simp only [toAdd_ofAdd]
    rw [matAct_wM_wM, mul_inv_cancel, matAct_wM_one]
    rfl
  map_mul' x y := by
    simp only [toAdd_mul, map_add]
    rfl

theorem toAdd_autWM (m : ℕ) (π : Perm (Fin 4)) (x : Multiplicative (Torus (Type200.k m))) :
    Multiplicative.toAdd (autWM m π x) =
      matAct _ (wM π) (compat_wM m π) (Multiplicative.toAdd x) := rfl

@[expose] def ψ200 (m : ℕ) : Fin81.R0 →* MulAut (Multiplicative (Torus (Type200.k m))) where
  toFun π := autWM m π
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    apply Multiplicative.toAdd.injective
    rw [toAdd_autWM, OneMemClass.coe_one, matAct_wM_one]
    rfl
  map_mul' π σ := by
    refine MulEquiv.ext fun x => ?_
    apply Multiplicative.toAdd.injective
    rw [toAdd_autWM, MulAut.mul_apply, toAdd_autWM, toAdd_autWM, matAct_wM_wM]
    rfl

theorem toAdd_ψ200 (m : ℕ) (π : Fin81.R0) (x : Multiplicative (Torus (Type200.k m))) :
    Multiplicative.toAdd (ψ200 m π x) =
      matAct _ (wM π) (compat_wM m π) (Multiplicative.toAdd x) := rfl

abbrev L4Std (m : ℕ) := Multiplicative (Torus (Type200.k m)) ⋊[ψ200 m] Fin81.R0

theorem card_L4Std (m : ℕ) : Nat.card (L4Std m) = 2 ^ (3 * m + 7) := by
  rw [SemidirectProduct.card, Fin81.card_R0, Nat.card_congr Multiplicative.toAdd, natCard_torus]
  simp only [Type200.k, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

@[expose] def uvR0 : Fin81.R0 := ⟨swap 0 1 * swap 2 3, by decide⟩

@[expose] def tR0 : Fin81.R0 := ⟨swap 0 2 * swap 1 3, by decide⟩

@[expose] def uR0 : Fin81.R0 := ⟨swap 2 3, by decide⟩

theorem wM_uvR0 : wM uvR0 = Type200.uvM := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem wM_tR0 : wM tR0 = Type200.tM := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem wM_uR0 : wM uR0 = Type200.uM := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem toAdd_ψ200_uvR0 (m : ℕ) (x : Multiplicative (Torus (Type200.k m))) :
    Multiplicative.toAdd (ψ200 m uvR0 x) =
      (StrothTypeIndex.t200 m).action.φuv (Multiplicative.toAdd x) := by
  rw [toAdd_ψ200]
  exact congrArg (fun f : Torus (Type200.k m) →+ Torus (Type200.k m) => f _)
    (matAct_congr _ _ (MatEq.of_eq wM_uvR0))

theorem toAdd_ψ200_tR0 (m : ℕ) (x : Multiplicative (Torus (Type200.k m))) :
    Multiplicative.toAdd (ψ200 m tR0 x) =
      (StrothTypeIndex.t200 m).action.φt (Multiplicative.toAdd x) := by
  rw [toAdd_ψ200]
  exact congrArg (fun f : Torus (Type200.k m) →+ Torus (Type200.k m) => f _)
    (matAct_congr _ _ (MatEq.of_eq wM_tR0))

theorem toAdd_ψ200_uR0 (m : ℕ) (x : Multiplicative (Torus (Type200.k m))) :
    Multiplicative.toAdd (ψ200 m uR0 x) =
      (StrothTypeIndex.t200 m).action.φu (Multiplicative.toAdd x) := by
  rw [toAdd_ψ200]
  exact congrArg (fun f : Torus (Type200.k m) →+ Torus (Type200.k m) => f _)
    (matAct_congr _ _ (MatEq.of_eq wM_uR0))

end CFSG.CGT.Stroth77.L4Sylow
