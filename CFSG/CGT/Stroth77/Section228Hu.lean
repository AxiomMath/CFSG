module

public import CFSG.CGT.Stroth77.Section228Frame

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

namespace StrothFrame.IsD

variable {F : StrothFrame G} {D : Subgroup G} {τ : StrothTypeIndex}
  {dD : StrothWeakTypeData D τ}

theorem isConj_u_w_mul_u_of_phiu_sub (h : F.IsD D dD) {v : Torus τ.k}
    (hv : τ.action.φu v - v = (2 ^ (τ.m - 1) : ℕ) • Torus.c (k := τ.k)) :
    IsConj dD.u (F.dA.toConfig.w * dD.u) := by
  let d : G := dD.ofTorus v
  set wco : Torus τ.k := (2 ^ (τ.m - 1) : ℕ) • Torus.c (k := τ.k) with hwco
  have hw : dD.ofTorus wco = F.dA.toConfig.w := by
    rw [hwco, dD.ofTorus_nsmul,
      show dD.ofTorus (Torus.c (k := τ.k)) = (dD.c : G) from rfl, c_pow_eq_w h,
      StrothWeakTypeData.toConfig_w]
  have hφ : τ.action.φu v = v + wco := by
    rw [← sub_add_cancel (τ.action.φu v) v, hv, add_comm]
  have hux : dD.u * d = d * F.dA.toConfig.w * dD.u := by
    calc dD.u * d = dD.ofTorus (τ.action.φu v) * dD.u := dD.u_mul_ofTorus v
      _ = dD.ofTorus (v + wco) * dD.u := by rw [hφ]
      _ = d * dD.ofTorus wco * dD.u := by rw [dD.ofTorus_add]
      _ = d * F.dA.toConfig.w * dD.u := by rw [hw]
  have hconj : d⁻¹ * dD.u * d = F.dA.toConfig.w * dD.u := by
    calc d⁻¹ * dD.u * d = d⁻¹ * (dD.u * d) := by group
      _ = d⁻¹ * (d * F.dA.toConfig.w * dD.u) := by rw [hux]
      _ = F.dA.toConfig.w * dD.u := by group
  exact isConj_iff.2 ⟨d⁻¹, by simpa using hconj⟩

theorem phi_smul_sub_neg_one {A : Type*} [AddCommGroup A] (φ : A →+ A) (c : A) (m : ℕ)
    (hm : 2 ≤ m) (hφ : φ c = (-1 : ℤ) • c) :
    φ ((-(2 : ℤ) ^ (m - 2)) • c) - (-(2 : ℤ) ^ (m - 2)) • c = (2 ^ (m - 1) : ℕ) • c := by
  rw [map_zsmul, hφ, smul_smul, ← natCast_zsmul, ← sub_smul]
  congr 1
  have hpow : (2 : ℤ) ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    rw [← pow_succ']; congr 1; omega
  rw [show ((2 ^ (m - 1) : ℕ) : ℤ) = (2 : ℤ) ^ (m - 1) by push_cast; ring, hpow]
  ring

theorem phi_smul_sub_one_plus {A : Type*} [AddCommGroup A] (φ : A →+ A) (c : A) (m : ℕ)
    (hφ : φ c = (1 + 2 ^ (m - 1) : ℤ) • c) :
    φ ((1 : ℤ) • c) - (1 : ℤ) • c = (2 ^ (m - 1) : ℕ) • c := by
  rw [one_zsmul, hφ, add_smul, one_smul, ← natCast_zsmul]
  abel

theorem phi_smul_sub_neg_one_plus_torus (τ : StrothTypeIndex) (m : ℕ) (hm : 3 ≤ m)
    (hkm : τ.k 0 = m)
    (hφ : τ.action.φu (Torus.c (k := τ.k)) = (-1 + 2 ^ (m - 1) : ℤ) • Torus.c (k := τ.k)) :
    τ.action.φu (((2 : ℤ) ^ (m - 2)) • Torus.c (k := τ.k)) -
        ((2 : ℤ) ^ (m - 2)) • Torus.c (k := τ.k) = (2 ^ (m - 1) : ℕ) • Torus.c (k := τ.k) := by
  rw [map_zsmul, hφ, smul_smul, ← natCast_zsmul, ← sub_smul]
  funext i
  fin_cases i <;> simp [Torus.c, gen, Pi.single_apply, zsmul_eq_mul]
  rw [hkm]
  have hzero : ((2 : ZMod (2 ^ m)) ^ m) = 0 := by
    rw [show (2 : ZMod (2 ^ m)) = ((2 : ℕ) : ZMod (2 ^ m)) from by norm_num]
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have h2 : (2 : ZMod (2 ^ m)) ^ (m - 2) * (2 : ZMod (2 ^ m)) ^ (m - 1) = 0 := by
    rw [← pow_add, show m - 2 + (m - 1) = m + (m - 3) by omega, pow_add, hzero, zero_mul]
  have h3 : (2 : ZMod (2 ^ m)) ^ (m - 1) = 2 * (2 : ZMod (2 ^ m)) ^ (m - 2) := by
    rw [show m - 1 = (m - 2) + 1 by omega, pow_succ, mul_comm]
  calc (2 : ZMod (2 ^ m)) ^ (m - 2) * (-1 + 2 ^ (m - 1)) - 2 ^ (m - 2)
      = -2 ^ (m - 2) + (2 ^ (m - 2) * 2 ^ (m - 1)) - 2 ^ (m - 2) := by ring
    _ = -2 ^ (m - 1) := by rw [h2, h3]; ring
    _ = 2 ^ (m - 1) := by
        rw [neg_eq_iff_add_eq_zero]
        calc (2 : ZMod (2 ^ m)) ^ (m - 1) + 2 ^ (m - 1)
            = 2 * 2 ^ (m - 1) := by ring
          _ = 2 ^ m := by rw [mul_comm, ← pow_succ, show m - 1 + 1 = m by omega]
          _ = 0 := hzero

theorem u_c_t110 (t : ℕ) :
    (StrothTypeIndex.t110 t).action.φu (Torus.c (k := (StrothTypeIndex.t110 t).k)) =
      (1 + 2 ^ (t + 1) : ℤ) • Torus.c (k := (StrothTypeIndex.t110 t).k) := by
  show (Type110.action t).φu (Torus.c (k := Type110.k t)) =
    (1 + 2 ^ (t + 1) : ℤ) • Torus.c (k := Type110.k t)
  have h : (2 * 2 ^ t + 1 : ℤ) = 1 + 2 ^ (t + 1) := by
    have h2 : (2 : ℤ) * 2 ^ t = 2 ^ (t + 1) := by rw [mul_comm, ← pow_succ]
    linarith
  simpa [h] using Type110.u_c t

theorem u_c_t111 (t : ℕ) :
    (StrothTypeIndex.t111 t).action.φu (Torus.c (k := (StrothTypeIndex.t111 t).k)) =
      (1 + 2 ^ (t + 1) : ℤ) • Torus.c (k := (StrothTypeIndex.t111 t).k) := by
  show (Type111.action t).φu (Torus.c (k := Type111.k t)) =
    (1 + 2 ^ (t + 1) : ℤ) • Torus.c (k := Type111.k t)
  have h : (2 * 2 ^ t + 1 : ℤ) = 1 + 2 ^ (t + 1) := by
    have h2 : (2 : ℤ) * 2 ^ t = 2 ^ (t + 1) := by rw [mul_comm, ← pow_succ]
    linarith
  simpa [h] using Type111.u_c t

theorem u_c_t120 (m : ℕ) (hm : 3 ≤ m) :
    (StrothTypeIndex.t120 m hm).action.φu (Torus.c (k := (StrothTypeIndex.t120 m hm).k)) =
      (-1 : ℤ) • Torus.c (k := (StrothTypeIndex.t120 m hm).k) := by
  show (Type120.action (Type120.data m (by omega))).φu (Torus.c (k := Type120.k m)) =
    (-1 : ℤ) • Torus.c (k := Type120.k m)
  simpa using Type120.u_c (Type120.data m (by omega))

theorem u_c_t210 (m : ℕ) (hm : 2 ≤ m) :
    (StrothTypeIndex.t210 m hm).action.φu (Torus.c (k := (StrothTypeIndex.t210 m hm).k)) =
      (1 + 2 ^ (m - 1) : ℤ) • Torus.c (k := (StrothTypeIndex.t210 m hm).k) := by
  have h : (2 * 2 ^ (m - 2) + 1 : ℤ) = 1 + 2 ^ (m - 1) := by
    have h2 : (2 : ℤ) * 2 ^ (m - 2) = 2 ^ (m - 1) := by
      rw [mul_comm, ← pow_succ, show m - 2 + 1 = m - 1 by omega]
    linarith
  show (Type210.action m hm).φu (Torus.c (k := Type210.k m)) =
    (1 + 2 ^ (m - 1) : ℤ) • Torus.c (k := Type210.k m)
  simpa [h, zero_zsmul, add_zero] using Type210.u_c m hm

theorem u_c_t211 (m : ℕ) (hm : 2 ≤ m) :
    (StrothTypeIndex.t211 m hm).action.φu (Torus.c (k := (StrothTypeIndex.t211 m hm).k)) =
      (1 + 2 ^ (m - 1) : ℤ) • Torus.c (k := (StrothTypeIndex.t211 m hm).k) := by
  have h : (2 * 2 ^ (m - 2) + 1 : ℤ) = 1 + 2 ^ (m - 1) := by
    have h2 : (2 : ℤ) * 2 ^ (m - 2) = 2 ^ (m - 1) := by
      rw [mul_comm, ← pow_succ, show m - 2 + 1 = m - 1 by omega]
    linarith
  show (Type211.action m hm).φu (Torus.c (k := Type211.k m)) =
    (1 + 2 ^ (m - 1) : ℤ) • Torus.c (k := Type211.k m)
  simpa [h, zero_zsmul, add_zero] using Type211.u_c m hm

theorem u_c_t310 (m : ℕ) (hm : 2 ≤ m) :
    (StrothTypeIndex.t310 m hm).action.φu (Torus.c (k := (StrothTypeIndex.t310 m hm).k)) =
      (1 + 2 ^ (m - 1) : ℤ) • Torus.c (k := (StrothTypeIndex.t310 m hm).k) := by
  have h : (2 * 2 ^ (m - 2) + 1 : ℤ) = 1 + 2 ^ (m - 1) := by
    have h2 : (2 : ℤ) * 2 ^ (m - 2) = 2 ^ (m - 1) := by
      rw [mul_comm, ← pow_succ, show m - 2 + 1 = m - 1 by omega]
    linarith
  show (Type310.action m hm).φu (Torus.c (k := Type310.k m)) =
    (1 + 2 ^ (m - 1) : ℤ) • Torus.c (k := Type310.k m)
  simpa [h, zero_zsmul, add_zero] using Type310.u_c m hm

theorem u_c_t121 (m : ℕ) (hm : 3 ≤ m) :
    (StrothTypeIndex.t121 m hm).action.φu (Torus.c (k := (StrothTypeIndex.t121 m hm).k)) =
      (-1 : ℤ) • Torus.c (k := (StrothTypeIndex.t121 m hm).k) := by
  show (Type121.action (Type121.data m (by omega))).φu (Torus.c (k := Type121.k m)) =
    (-1 : ℤ) • Torus.c (k := Type121.k m)
  dsimp only [Type121.action, SigmaFourAction.ofMatEq, SigmaFourAction.φu, Torus.c]
  rw [matAct_gen_eq]
  simp [Type121.uM, uMat, ofCols, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem u_c_t130 (m : ℕ) (hm : 3 ≤ m) :
    (StrothTypeIndex.t130 m hm).action.φu (Torus.c (k := (StrothTypeIndex.t130 m hm).k)) =
      (-1 + 2 ^ (m - 1) : ℤ) • Torus.c (k := (StrothTypeIndex.t130 m hm).k) := by
  show (Type130.action (Type130.data m (by omega))).φu (Torus.c (k := Type130.k m)) =
    (-1 + 2 ^ (m - 1) : ℤ) • Torus.c (k := Type130.k m)
  dsimp only [Type130.action, SigmaFourAction.ofMatEq, SigmaFourAction.φu, Torus.c]
  rw [matAct_gen_eq]
  simp [Type130.uM, uMat, ofCols, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem u_c_t131 (m : ℕ) (hm : 3 ≤ m) :
    (StrothTypeIndex.t131 m hm).action.φu (Torus.c (k := (StrothTypeIndex.t131 m hm).k)) =
      (-1 + 2 ^ (m - 1) : ℤ) • Torus.c (k := (StrothTypeIndex.t131 m hm).k) := by
  show (Type131.action (Type131.data m (by omega))).φu (Torus.c (k := Type131.k m)) =
    (-1 + 2 ^ (m - 1) : ℤ) • Torus.c (k := Type131.k m)
  dsimp only [Type131.action, SigmaFourAction.ofMatEq, SigmaFourAction.φu, Torus.c]
  rw [matAct_gen_eq]
  simp [Type131.uM, uMat, ofCols, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem u_c_t220 (s : ℕ) (hs : 1 ≤ s) :
    (StrothTypeIndex.t220 s hs).action.φu
        (Torus.c (k := (StrothTypeIndex.t220 s hs).k)) =
      (-1 : ℤ) • Torus.c (k := (StrothTypeIndex.t220 s hs).k) := by
  show (Type220.action (Type220.data s)).φu (Torus.c (k := Type220.k s)) =
    (-1 : ℤ) • Torus.c (k := Type220.k s)
  dsimp only [Type220.action, SigmaFourAction.ofMatEq, SigmaFourAction.φu, Torus.c]
  rw [matAct_gen_eq]
  simp [Type220.uM, uMat, ofCols, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem u_c_t221 (s : ℕ) (hs : 1 ≤ s) :
    (StrothTypeIndex.t221 s hs).action.φu
        (Torus.c (k := (StrothTypeIndex.t221 s hs).k)) =
      (-1 : ℤ) • Torus.c (k := (StrothTypeIndex.t221 s hs).k) := by
  show (Type221.action (Type221.data s)).φu (Torus.c (k := Type221.k s)) =
    (-1 : ℤ) • Torus.c (k := Type221.k s)
  dsimp only [Type221.action, SigmaFourAction.ofMatEq, SigmaFourAction.φu, Torus.c]
  rw [matAct_gen_eq]
  simp [Type221.uM, uMat, ofCols, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem u_c_t230 (s : ℕ) (hs : 1 ≤ s) :
    (StrothTypeIndex.t230 s hs).action.φu
        (Torus.c (k := (StrothTypeIndex.t230 s hs).k)) =
      (-1 + 2 ^ (s + 1) : ℤ) • Torus.c (k := (StrothTypeIndex.t230 s hs).k) := by
  show (Type230.action (Type230.data s)).φu (Torus.c (k := Type230.k s)) =
    (-1 + 2 ^ (s + 1) : ℤ) • Torus.c (k := Type230.k s)
  dsimp only [Type230.action, SigmaFourAction.ofMatEq, SigmaFourAction.φu, Torus.c]
  rw [matAct_gen_eq]
  simp [Type230.uM, uMat, ofCols, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem u_c_t231 (s : ℕ) (hs : 1 ≤ s) :
    (StrothTypeIndex.t231 s hs).action.φu
        (Torus.c (k := (StrothTypeIndex.t231 s hs).k)) =
      (-1 + 2 ^ (s + 1) : ℤ) • Torus.c (k := (StrothTypeIndex.t231 s hs).k) := by
  show (Type231.action (Type231.data s)).φu (Torus.c (k := Type231.k s)) =
    (-1 + 2 ^ (s + 1) : ℤ) • Torus.c (k := Type231.k s)
  dsimp only [Type231.action, SigmaFourAction.ofMatEq, SigmaFourAction.φu, Torus.c]
  rw [matAct_gen_eq]
  simp [Type231.uM, uMat, ofCols, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem u_c_t321 :
    (StrothTypeIndex.t321).action.φu (Torus.c (k := (StrothTypeIndex.t321).k)) =
      (-1 : ℤ) • Torus.c (k := (StrothTypeIndex.t321).k) := by
  show Type321.action.φu (Torus.c (k := Type321.k)) = (-1 : ℤ) • Torus.c (k := Type321.k)
  dsimp only [Type321.action, SigmaFourAction.ofMatEq, SigmaFourAction.φu, Torus.c]
  rw [matAct_gen_eq]
  simp [Type321.uM, uMat, ofCols, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem u_c_t331 :
    (StrothTypeIndex.t331).action.φu (Torus.c (k := (StrothTypeIndex.t331).k)) =
      (-1 + 2 ^ (3 - 1) : ℤ) • Torus.c (k := (StrothTypeIndex.t331).k) := by
  show Type331.action.φu (Torus.c (k := Type331.k)) = (-1 + 2 ^ (3 - 1) : ℤ) • Torus.c (k := Type331.k)
  dsimp only [Type331.action, SigmaFourAction.ofMatEq, SigmaFourAction.φu, Torus.c]
  rw [matAct_gen_eq]
  simp [Type331.uM, uMat, ofCols, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem u_c_t320 (m : ℕ) (hm : 3 ≤ m) :
    (StrothTypeIndex.t320 m hm).action.φu (Torus.c (k := (StrothTypeIndex.t320 m hm).k)) =
      (-1 : ℤ) • Torus.c (k := (StrothTypeIndex.t320 m hm).k) := by
  show (Type320.action (Type32x.data m (by omega))).φu (Torus.c (k := Type320.k m)) =
    (-1 : ℤ) • Torus.c (k := Type320.k m)
  simpa using Type320.u_c (Type32x.data m (by omega))

theorem u_c_t330 (m : ℕ) (hm : 3 ≤ m) :
    (StrothTypeIndex.t330 m hm).action.φu (Torus.c (k := (StrothTypeIndex.t330 m hm).k)) =
      (-1 + 2 ^ (m - 1) : ℤ) • Torus.c (k := (StrothTypeIndex.t330 m hm).k) := by
  show (Type330.action (Type32x.data m (by omega))).φu (Torus.c (k := Type330.k m)) =
    (-1 + 2 ^ (m - 1) : ℤ) • Torus.c (k := Type330.k m)
  dsimp only [Type330.action, SigmaFourAction.ofMatEq, SigmaFourAction.φu, Torus.c]
  rw [matAct_gen_eq]
  simp [Type330.uM, uMat, ofCols, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem isConj_u_w_mul_u_of_not_five {G : Type} [Group G] [Finite G]
    {F : StrothFrame G} {D : Subgroup G} {τ : StrothTypeIndex}
    {dD : StrothWeakTypeData D τ} (h : F.IsD D dD)
    (hfive : ¬ ((∃ m, τ = .t200 m) ∨ (∃ m, τ = .t201 m) ∨
      (∃ m, τ = .t100 m) ∨ (∃ s, τ = .t101 s) ∨ ∃ n, τ = .t300 n)) :
    IsConj dD.u (F.dA.toConfig.w * dD.u) := by
  cases τ with
  | t200 m => exact absurd (Or.inl ⟨m, rfl⟩) hfive
  | t201 m => exact absurd (Or.inr (Or.inl ⟨m, rfl⟩)) hfive
  | t100 m => exact absurd (Or.inr (Or.inr (Or.inl ⟨m, rfl⟩))) hfive
  | t101 s => exact absurd (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, rfl⟩)))) hfive
  | t300 n => exact absurd (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, rfl⟩)))) hfive
  | t110 t =>
      refine isConj_u_w_mul_u_of_phiu_sub h (v := (1 : ℤ) • Torus.c) ?_
      exact phi_smul_sub_one_plus _ _ _ (u_c_t110 t)
  | t111 t =>
      refine isConj_u_w_mul_u_of_phiu_sub h (v := (1 : ℤ) • Torus.c) ?_
      exact phi_smul_sub_one_plus _ _ _ (u_c_t111 t)
  | t120 m hm =>
      refine isConj_u_w_mul_u_of_phiu_sub h (v := (-(2 : ℤ) ^ (m - 2)) • Torus.c) ?_
      exact phi_smul_sub_neg_one _ _ _ (by omega) (u_c_t120 m hm)
  | t121 m hm =>
      refine isConj_u_w_mul_u_of_phiu_sub h (v := (-(2 : ℤ) ^ (m - 2)) • Torus.c) ?_
      exact phi_smul_sub_neg_one _ _ _ (by omega) (u_c_t121 m hm)
  | t130 m hm =>
      refine isConj_u_w_mul_u_of_phiu_sub h (v := ((2 : ℤ) ^ (m - 2)) • Torus.c) ?_
      exact phi_smul_sub_neg_one_plus_torus _ m (by omega) rfl (u_c_t130 m hm)
  | t131 m hm =>
      refine isConj_u_w_mul_u_of_phiu_sub h (v := ((2 : ℤ) ^ (m - 2)) • Torus.c) ?_
      exact phi_smul_sub_neg_one_plus_torus _ m (by omega) rfl (u_c_t131 m hm)
  | t210 m hm =>
      refine isConj_u_w_mul_u_of_phiu_sub h (v := (1 : ℤ) • Torus.c) ?_
      exact phi_smul_sub_one_plus _ _ _ (u_c_t210 m hm)
  | t211 m hm =>
      refine isConj_u_w_mul_u_of_phiu_sub h (v := (1 : ℤ) • Torus.c) ?_
      exact phi_smul_sub_one_plus _ _ _ (u_c_t211 m hm)
  | t220 s hs =>
      refine isConj_u_w_mul_u_of_phiu_sub h (v := (-(2 : ℤ) ^ s) • Torus.c) ?_
      exact phi_smul_sub_neg_one _ _ (s + 2) (by omega) (u_c_t220 s hs)
  | t221 s hs =>
      refine isConj_u_w_mul_u_of_phiu_sub h (v := (-(2 : ℤ) ^ s) • Torus.c) ?_
      exact phi_smul_sub_neg_one _ _ (s + 2) (by omega) (u_c_t221 s hs)
  | t230 s hs =>
      refine isConj_u_w_mul_u_of_phiu_sub h (v := ((2 : ℤ) ^ s) • Torus.c) ?_
      exact phi_smul_sub_neg_one_plus_torus _ (s + 2) (by omega) rfl (u_c_t230 s hs)
  | t231 s hs =>
      refine isConj_u_w_mul_u_of_phiu_sub h (v := ((2 : ℤ) ^ s) • Torus.c) ?_
      exact phi_smul_sub_neg_one_plus_torus _ (s + 2) (by omega) rfl (u_c_t231 s hs)
  | t310 m hm =>
      refine isConj_u_w_mul_u_of_phiu_sub h (v := (1 : ℤ) • Torus.c) ?_
      exact phi_smul_sub_one_plus _ _ _ (u_c_t310 m hm)
  | t320 m hm =>
      refine isConj_u_w_mul_u_of_phiu_sub h (v := (-(2 : ℤ) ^ (m - 2)) • Torus.c) ?_
      exact phi_smul_sub_neg_one _ _ _ (by omega) (u_c_t320 m hm)
  | t330 m hm =>
      refine isConj_u_w_mul_u_of_phiu_sub h (v := ((2 : ℤ) ^ (m - 2)) • Torus.c) ?_
      exact phi_smul_sub_neg_one_plus_torus _ m (by omega) rfl (u_c_t330 m hm)
  | t321 =>
      refine isConj_u_w_mul_u_of_phiu_sub h (v := (-(2 : ℤ) ^ (3 - 2)) • Torus.c) ?_
      exact phi_smul_sub_neg_one _ _ 3 (by norm_num) u_c_t321
  | t331 =>
      refine isConj_u_w_mul_u_of_phiu_sub h (v := ((2 : ℤ) ^ (3 - 2)) • Torus.c) ?_
      exact phi_smul_sub_neg_one_plus_torus _ 3 (by norm_num) rfl u_c_t331

end StrothFrame.IsD

end CFSG.CGT.Stroth77
