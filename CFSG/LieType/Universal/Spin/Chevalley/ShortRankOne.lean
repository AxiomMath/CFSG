module

public import CFSG.LieType.Universal.Spin.Chevalley.RankOne

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ}

@[expose] def shortWeylBool {n : ℕ} (i m : Fin n) (r : Bool) : Bool := if m = i then !r else r

@[expose] def shortCoroot {n : ℕ} (i : Fin n) (s : Bool) (m : Fin n) (r : Bool) : ℤ :=
  if m = i then (if r = s then 2 else -2) else 0

theorem shortCoroot_not {n : ℕ} (i : Fin n) (s : Bool) (m : Fin n) (r : Bool) :
    shortCoroot i s m (!r) = -shortCoroot i s m r := by
  simp only [shortCoroot]
  by_cases hi : m = i <;> cases r <;> cases s <;> simp [hi]

namespace OddFrame

variable (F : OddFrame Q n)

@[expose] noncomputable def shortPair (i : Fin n) (s : Bool) : SL2Pair (CliffordAlgebra Q) where
  X := ι Q F.z * ι Q (F.vec i s)
  Y := ι Q (F.vec i (!s)) * ι Q F.z
  X_mul_X := ι_mul_ι_mul_ι_mul_ι_eq_zero Q (F.map_vec i s) (F.polar_vec_z i s)
  Y_mul_Y := by
    rw [mul_assoc, ← mul_assoc (ι Q F.z), F.ι_z_mul_ι_vec, neg_mul, mul_neg, mul_assoc,
      F.ι_vec_mul_ι_vec_self_mul, neg_zero]
  X_mul_Y_mul_X := by
    simp only [mul_assoc]
    rw [ι_mul_ι_mul_eq_of_map_eq_one Q F.map_z, F.ι_vec_mul_ι_vec_not_mul_ι_vec]
  Y_mul_X_mul_Y := by
    simp only [mul_assoc]
    rw [ι_mul_ι_mul_eq_of_map_eq_one Q F.map_z]
    have h := ι_mul_ι_mul_ι_mul_eq Q (F.map_vec i (!s)) (F.polar_vec_not i (!s)) (ι Q F.z)
    simpa only [Bool.not_not] using h

@[expose] noncomputable def shortSL2 (i : Fin n) (s : Bool) :
    Matrix.SpecialLinearGroup (Fin 2) K →* spinGroup Q :=
  (F.shortPair i s).toSpin (F.one_add_smul_z_mem_spinGroup i s) fun c => by
    change 1 + c • (ι Q (F.vec i (!s)) * ι Q F.z) ∈ spinGroup Q
    rw [F.ι_vec_mul_ι_z, smul_neg, ← neg_smul]
    exact F.one_add_smul_z_mem_spinGroup i (!s) (-c)

theorem coe_shortSL2 (i : Fin n) (s : Bool) (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    (F.shortSL2 i s M : CliffordAlgebra Q) =
      (F.shortPair i s).toFun (M : Matrix (Fin 2) (Fin 2) K) := rfl

@[simp]
theorem shortSL2_upperSL2 (i : Fin n) (s : Bool) (c : K) :
    F.shortSL2 i s (upperSL2 c) = F.shortRoot i s (.ofAdd c) := by
  apply Subtype.ext
  rw [coe_shortSL2, SL2Pair.toFun_upperSL2, coe_shortRoot]
  rfl

@[simp]
theorem shortSL2_lowerSL2 (i : Fin n) (s : Bool) (c : K) :
    F.shortSL2 i s (lowerSL2 c) = F.shortRoot i (!s) (.ofAdd (-c)) := by
  apply Subtype.ext
  rw [coe_shortSL2, SL2Pair.toFun_lowerSL2, coe_shortRoot]
  change 1 + c • (ι Q (F.vec i (!s)) * ι Q F.z) = _
  rw [F.ι_vec_mul_ι_z, smul_neg, neg_smul]

@[expose] noncomputable def shortWeyl (i : Fin n) (s : Bool) : spinGroup Q :=
  F.shortSL2 i s (weylSL2 1)

theorem shortWeyl_eq (i : Fin n) (s : Bool) :
    F.shortWeyl i s = F.shortRoot i s (.ofAdd 1) * F.shortRoot i (!s) (.ofAdd 1) *
      F.shortRoot i s (.ofAdd 1) := by
  rw [shortWeyl, weylSL2_eq, map_mul, map_mul, shortSL2_upperSL2, shortSL2_lowerSL2]
  simp

theorem shortPair_X_mul_Y (i : Fin n) (s : Bool) :
    (F.shortPair i s).X * (F.shortPair i s).Y = F.numOp i s := by
  simp only [shortPair, HypFrame.numOp, mul_assoc]
  rw [ι_mul_ι_mul_ι_mul_comm Q (F.polar_z_vec i s) (F.polar_z_vec i (!s)), ι_z_mul_ι_z, mul_one]

theorem shortPair_Y_mul_X (i : Fin n) (s : Bool) :
    (F.shortPair i s).Y * (F.shortPair i s).X = F.numOp i (!s) := by
  simp only [shortPair, HypFrame.numOp, mul_assoc, Bool.not_not]
  rw [ι_mul_ι_mul_eq_of_map_eq_one Q F.map_z]

theorem coe_shortWeyl (i : Fin n) (s : Bool) :
    (F.shortWeyl i s : CliffordAlgebra Q) = ι Q F.z * ι Q (F.vec i s + F.vec i (!s)) := by
  rw [shortWeyl, coe_shortSL2, SL2Pair.toFun_weylSL2, shortPair_X_mul_Y, shortPair_Y_mul_X]
  have h : F.numOp i s + F.numOp i (!s) = 1 := by
    simpa only [HypFrame.numOp, Bool.not_not] using F.ι_vec_mul_ι_vec_not_add i s
  rw [sub_sub, h, sub_self, add_zero, map_add, mul_add]
  simp only [shortPair, Units.val_one, inv_one, one_smul, F.ι_vec_mul_ι_z, sub_neg_eq_add]

@[expose] noncomputable def shortTorus (i : Fin n) (s : Bool) : Kˣ →* spinGroup Q :=
  (F.shortSL2 i s).comp diagSL2

theorem shortTorus_apply (i : Fin n) (s : Bool) (τ : Kˣ) :
    F.shortTorus i s τ = F.shortSL2 i s (diagSL2 τ) := rfl

theorem coe_shortTorus (i : Fin n) (s : Bool) (τ : Kˣ) :
    (F.shortTorus i s τ : CliffordAlgebra Q) =
      (F.shortPair i s).toFun ((diagSL2 τ : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) := rfl

theorem shortWeyl_mul_self (i : Fin n) (s : Bool) :
    F.shortWeyl i s * F.shortWeyl i s = F.shortTorus i s (-1) := by
  rw [shortWeyl, ← map_mul, weylSL2_one_mul_self, shortTorus_apply]

theorem shortWeyl_mul_shortTorus_mul_inv (i : Fin n) (s : Bool) (τ : Kˣ) :
    F.shortWeyl i s * F.shortTorus i s τ * (F.shortWeyl i s)⁻¹ = F.shortTorus i s τ⁻¹ := by
  rw [shortWeyl, shortTorus_apply, shortTorus_apply, ← map_inv, ← map_mul, ← map_mul,
    weylSL2_mul_diagSL2_mul_inv]

theorem spinAction_shortSL2_weylSL2 (i : Fin n) (s : Bool) (τ : Kˣ) (v : V) :
    spinAction Q (F.shortSL2 i s (weylSL2 τ)) v =
      v - polar Q v (F.vec i (!s)) • (F.vec i s + (((τ⁻¹ : Kˣ) : K) ^ 2) • F.vec i (!s))
        - polar Q v (F.vec i s) • (F.vec i (!s) + ((τ : K) ^ 2) • F.vec i s)
        - polar Q v F.z • F.z := by
  simp only [weylSL2_eq, map_mul, shortSL2_upperSL2, shortSL2_lowerSL2, LinearEquiv.mul_apply,
    spinAction_shortRoot]
  simp only [polar_add_left, polar_sub_left, polar_smul_left, smul_eq_mul, HypFrame.polar_vec_vec,
    Bool.not_not, polar_z_vec, polar_z_self, polar_vec_z, Bool.eq_not_self, ite_false, ite_true,
    and_self, and_false, neg_neg]
  have hτ : (τ : K) ≠ 0 := τ.ne_zero
  match_scalars <;> (try field_simp) <;> ring

theorem spinAction_shortTorus (i : Fin n) (s : Bool) (τ : Kˣ) (v : V) :
    spinAction Q (F.shortTorus i s τ) v =
      v + ((τ : K) ^ 2 - 1) • polar Q v (F.vec i (!s)) • F.vec i s
        + ((((τ⁻¹ : Kˣ) : K)) ^ 2 - 1) • polar Q v (F.vec i s) • F.vec i (!s) := by
  rw [shortTorus_apply, diagSL2_eq, map_mul, map_mul, LinearEquiv.mul_apply,
    spinAction_shortSL2_weylSL2, spinAction_shortSL2_weylSL2]
  simp only [polar_add_left, polar_sub_left, polar_smul_left, smul_eq_mul, HypFrame.polar_vec_vec,
    Bool.not_not, polar_z_vec, polar_z_self, polar_vec_z, Bool.eq_not_self, Bool.not_eq_self,
    ite_false, ite_true, and_self, and_false]
  have hτ : (τ : K) ≠ 0 := τ.ne_zero
  match_scalars <;> (try field_simp) <;> simp <;> ring

@[simp]
theorem spinAction_shortWeyl_z (i : Fin n) (s : Bool) :
    spinAction Q (F.shortWeyl i s) F.z = -F.z := by
  rw [shortWeyl, spinAction_shortSL2_weylSL2]
  simp only [polar_z_vec, polar_z_self, zero_smul, sub_zero]
  module

theorem spinAction_shortWeyl_vec (i : Fin n) (s : Bool) (m : Fin n) (r : Bool) :
    spinAction Q (F.shortWeyl i s) (F.vec m r) =
      (longWeylSign i m : K) • F.vec m (shortWeylBool i m r) := by
  rw [shortWeyl, spinAction_shortSL2_weylSL2]
  by_cases hmi : m = i
  · subst hmi
    rcases Bool.eq_or_eq_not r s with rfl | rfl
    · simp [longWeylSign, shortWeylBool, HypFrame.polar_vec_vec]
    · simp [longWeylSign, shortWeylBool, HypFrame.polar_vec_vec]
  · simp [longWeylSign, shortWeylBool, HypFrame.polar_vec_vec, hmi]

@[simp]
theorem spinAction_shortTorus_z (i : Fin n) (s : Bool) (τ : Kˣ) :
    spinAction Q (F.shortTorus i s τ) F.z = F.z := by
  rw [spinAction_shortTorus]
  simp

theorem spinAction_shortTorus_vec (i : Fin n) (s : Bool) (τ : Kˣ) (m : Fin n) (r : Bool) :
    spinAction Q (F.shortTorus i s τ) (F.vec m r) =
      ((τ ^ shortCoroot i s m r : Kˣ) : K) • F.vec m r := by
  rw [spinAction_shortTorus]
  by_cases hmi : m = i
  · subst hmi
    rcases Bool.eq_or_eq_not r s with rfl | rfl
    · simp [shortCoroot, HypFrame.polar_vec_vec]
      module
    · simp [shortCoroot, HypFrame.polar_vec_vec]
      module
  · simp [shortCoroot, HypFrame.polar_vec_vec, hmi]

theorem shortWeyl_conj_longRoot (i : Fin n) (s : Bool) {k l : Fin n} (hkl : k ≠ l) (u v : Bool)
    (c : K) :
    F.shortWeyl i s * F.longRoot hkl u v (.ofAdd c) * (F.shortWeyl i s)⁻¹ =
      F.longRoot hkl (shortWeylBool i k u) (shortWeylBool i l v)
        (.ofAdd ((longWeylSign i k : K) * longWeylSign i l * c)) :=
  F.conj_longRoot _ hkl u v hkl _ _ (F.spinAction_shortWeyl_vec i s k u)
    (F.spinAction_shortWeyl_vec i s l v) c

theorem shortWeyl_conj_shortRoot (i : Fin n) (s : Bool) (k : Fin n) (u : Bool) (c : K) :
    F.shortWeyl i s * F.shortRoot k u (.ofAdd c) * (F.shortWeyl i s)⁻¹ =
      F.shortRoot k (shortWeylBool i k u) (.ofAdd (-(longWeylSign i k : K) * c)) := by
  rw [F.conj_shortRoot _ k u k _ (l := -1) (by rw [spinAction_shortWeyl_z, neg_one_smul])
    (F.spinAction_shortWeyl_vec i s k u) c, neg_one_mul]

theorem longWeyl_conj_shortRoot {i j : Fin n} (hij : i ≠ j) (s t : Bool) (k : Fin n) (u : Bool)
    (c : K) :
    F.longWeyl hij s t * F.shortRoot k u (.ofAdd c) * (F.longWeyl hij s t)⁻¹ =
      F.shortRoot (Equiv.swap i j k) (longWeylBool i j s t k u)
        (.ofAdd ((longWeylSign i k : K) * c)) := by
  rw [F.conj_shortRoot _ k u _ _ (l := 1)
    (by rw [F.spinAction_longWeyl_of_polar hij s t (fun r => F.polar_z_vec i r)
      (fun r => F.polar_z_vec j r), one_smul]) (F.spinAction_longWeyl_vec hij s t k u) c, one_mul]

theorem shortTorus_conj_longRoot (i : Fin n) (s : Bool) (τ : Kˣ) {k l : Fin n} (hkl : k ≠ l)
    (u v : Bool) (c : K) :
    F.shortTorus i s τ * F.longRoot hkl u v (.ofAdd c) * (F.shortTorus i s τ)⁻¹ =
      F.longRoot hkl u v
        (.ofAdd (((τ ^ (shortCoroot i s k u + shortCoroot i s l v) : Kˣ) : K) * c)) := by
  rw [F.conj_longRoot _ hkl u v hkl u v (F.spinAction_shortTorus_vec i s τ k u)
    (F.spinAction_shortTorus_vec i s τ l v) c, zpow_add, Units.val_mul]

theorem shortTorus_conj_shortRoot (i : Fin n) (s : Bool) (τ : Kˣ) (k : Fin n) (u : Bool) (c : K) :
    F.shortTorus i s τ * F.shortRoot k u (.ofAdd c) * (F.shortTorus i s τ)⁻¹ =
      F.shortRoot k u (.ofAdd (((τ ^ shortCoroot i s k u : Kˣ) : K) * c)) := by
  rw [F.conj_shortRoot _ k u k u (l := 1) (by rw [spinAction_shortTorus_z, one_smul])
    (F.spinAction_shortTorus_vec i s τ k u) c, one_mul]

theorem longTorus_conj_shortRoot {i j : Fin n} (hij : i ≠ j) (s t : Bool) (τ : Kˣ) (k : Fin n)
    (u : Bool) (c : K) :
    F.longTorus hij s t τ * F.shortRoot k u (.ofAdd c) * (F.longTorus hij s t τ)⁻¹ =
      F.shortRoot k u (.ofAdd (((τ ^ longCoroot i j s t k u : Kˣ) : K) * c)) := by
  have hz : spinAction Q (F.longTorus hij s t τ) F.z = (1 : K) • F.z := by
    rw [HypFrame.spinAction_longTorus]
    simp
  rw [F.conj_shortRoot _ k u k u hz (F.spinAction_longTorus_vec hij s t τ k u) c, one_mul]

theorem commute_shortTorus_numOp (i : Fin n) (s : Bool) (τ : Kˣ) (m : Fin n) (r : Bool) :
    Commute (F.shortTorus i s τ : CliffordAlgebra Q) (F.numOp m r) := by
  rw [coe_shortTorus]
  refine SL2Pair.commute_toFun_diagSL2 _ ?_ ?_ τ
  · rw [shortPair_X_mul_Y]
    exact F.commute_numOp _ _ _ _
  · rw [shortPair_Y_mul_X]
    exact F.commute_numOp _ _ _ _

theorem commute_shortTorus_shortTorus (i : Fin n) (s : Bool) (τ : Kˣ) (k : Fin n) (u : Bool)
    (σ : Kˣ) : Commute (F.shortTorus i s τ) (F.shortTorus k u σ) := by
  refine commute_of_coe ?_
  rw [F.coe_shortTorus k]
  refine (SL2Pair.commute_toFun_diagSL2 _ ?_ ?_ σ).symm
  · rw [shortPair_X_mul_Y]
    exact (F.commute_shortTorus_numOp i s τ _ _).symm
  · rw [shortPair_Y_mul_X]
    exact (F.commute_shortTorus_numOp i s τ _ _).symm

theorem commute_longTorus_shortTorus {i j : Fin n} (hij : i ≠ j) (s t : Bool) (τ : Kˣ) (k : Fin n)
    (u : Bool) (σ : Kˣ) : Commute (F.longTorus hij s t τ) (F.shortTorus k u σ) := by
  refine commute_of_coe ?_
  rw [F.coe_shortTorus k]
  refine (SL2Pair.commute_toFun_diagSL2 _ ?_ ?_ σ).symm
  · rw [shortPair_X_mul_Y]
    exact (F.commute_longTorus_numOp hij s t τ _ _).symm
  · rw [shortPair_Y_mul_X]
    exact (F.commute_longTorus_numOp hij s t τ _ _).symm

end OddFrame

end CFSG.LieType.Universal.Spin
