module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRootData
public import CFSG.LinearAlgebra.LinearGroups.Generation

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.NormTail

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal OrthogonalTail

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable (K F) in
structure NormTailData where
  bar : F ≃ₐ[K] F
  bar_bar : ∀ z, bar (bar z) = z
  exists_eq_of_bar_eq : ∀ z, bar z = z → ∃ k : K, algebraMap K F k = z

variable (K F) in
@[expose] def retr : F →ₗ[K] K :=
  (LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K F)
    (LinearMap.ker_eq_bot.2 (algebraMap K F).injective)).choose

theorem retr_algebraMap (k : K) : retr K F (algebraMap K F k) = k :=
  LinearMap.congr_fun (LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K F)
    (LinearMap.ker_eq_bot.2 (algebraMap K F).injective)).choose_spec k

variable (T : NormTailData K F)

theorem algebraMap_retr {z : F} (hz : T.bar z = z) : algebraMap K F (retr K F z) = z := by
  obtain ⟨k, rfl⟩ := T.exists_eq_of_bar_eq z hz
  rw [retr_algebraMap]

theorem bar_algebraMap (k : K) : T.bar (algebraMap K F k) = algebraMap K F k :=
  T.bar.commutes k

theorem bar_mul_bar (z w : F) : T.bar (z * T.bar w) = T.bar z * w := by
  rw [map_mul, T.bar_bar]

@[expose] def normBilin : LinearMap.BilinForm K F :=
  LinearMap.mk₂ K (fun z w => retr K F (z * T.bar w))
    (fun z₁ z₂ w => by rw [add_mul, map_add])
    (fun c z w => by rw [smul_mul_assoc, map_smul, smul_eq_mul])
    (fun z w₁ w₂ => by rw [map_add, mul_add, map_add])
    (fun c z w => by rw [map_smul, mul_smul_comm, map_smul, smul_eq_mul])

@[expose] def normForm : QuadraticForm K F :=
  (normBilin T).toQuadraticMap

theorem normForm_apply (z : F) : normForm T z = retr K F (z * T.bar z) :=
  rfl

theorem algebraMap_normForm (z : F) : algebraMap K F (normForm T z) = z * T.bar z := by
  rw [normForm_apply, algebraMap_retr T (by rw [bar_mul_bar, mul_comm])]

theorem polar_normForm (z w : F) :
    polar (normForm T) z w = retr K F (z * T.bar w + w * T.bar z) := by
  rw [normForm, LinearMap.BilinMap.polar_toQuadraticMap, map_add]
  rfl

theorem algebraMap_polar_normForm (z w : F) :
    algebraMap K F (polar (normForm T) z w) = z * T.bar w + w * T.bar z := by
  rw [polar_normForm, algebraMap_retr T (by rw [map_add, bar_mul_bar, bar_mul_bar, add_comm,
    mul_comm (T.bar w), mul_comm (T.bar z)])]

theorem normForm_eq_zero_iff {z : F} : normForm T z = 0 ↔ z = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, QuadraticMap.map_zero]⟩
  have h' := algebraMap_normForm T z
  rw [h, map_zero, eq_comm, mul_eq_zero] at h'
  rcases h' with h' | h'
  · exact h'
  · exact (map_eq_zero T.bar).1 h'

theorem normForm_anisotropic : (normForm T).Anisotropic := fun _ h =>
  (normForm_eq_zero_iff T).1 h

theorem normForm_mul (z w : F) : normForm T (z * w) = normForm T z * normForm T w := by
  apply (algebraMap K F).injective
  rw [RingHom.map_mul, algebraMap_normForm, algebraMap_normForm, algebraMap_normForm,
    map_mul T.bar]
  ring

theorem normForm_one : normForm T 1 = 1 := by
  apply (algebraMap K F).injective
  rw [algebraMap_normForm, map_one, map_one, mul_one]

theorem normForm_inv (z : F) : normForm T z⁻¹ = (normForm T z)⁻¹ := by
  by_cases hz : z = 0
  · rw [hz, _root_.inv_zero, QuadraticMap.map_zero, _root_.inv_zero]
  · refine eq_inv_of_mul_eq_one_left ?_
    rw [← normForm_mul, inv_mul_cancel₀ hz, normForm_one]

theorem two_eq_zero_of_charP [CharP K 2] : (2 : F) = 0 := by
  rw [← map_ofNat (algebraMap K F) 2, CharTwo.two_eq_zero, map_zero]

theorem neg_eq_self_of_charP [CharP K 2] (z : F) : -z = z := by
  rw [neg_eq_iff_add_eq_zero, ← two_mul, two_eq_zero_of_charP (K := K), zero_mul]

theorem exists_bar_ne (hF : Module.finrank K F = 2) : ∃ u : F, T.bar u ≠ u := by
  by_contra! h
  have hsurj : Function.Surjective (Algebra.linearMap K F) := fun z =>
    T.exists_eq_of_bar_eq z (h z)
  have hle := LinearMap.finrank_range_le (Algebra.linearMap K F)
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self] at hle
  omega

theorem nondegenerate_polarBilin_normForm [CharP K 2] (hF : Module.finrank K F = 2) :
    (polarBilin (normForm T)).Nondegenerate := by
  obtain ⟨u, hu⟩ := exists_bar_ne T hF
  refine CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun z hz => ?_
  by_contra hz0
  have h' := congrArg (algebraMap K F) (hz (z * u))
  rw [algebraMap_polar_normForm, map_zero, map_mul] at h'
  have h3 : z * T.bar z * (T.bar u + u) = 0 := by linear_combination h'
  rcases mul_eq_zero.1 h3 with h4 | h4
  · rcases mul_eq_zero.1 h4 with h5 | h5
    · exact hz0 h5
    · exact hz0 ((map_eq_zero T.bar).1 h5)
  · exact hu (by rw [eq_neg_of_add_eq_zero_left h4, neg_eq_self_of_charP (K := K)])

@[expose] def act (A X : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F :=
  A * X * (A.map T.bar)ᵀ

@[expose] def IsHerm (X : Matrix (Fin 2) (Fin 2) F) : Prop :=
  (X.map T.bar)ᵀ = X

theorem act_mul (A B X : Matrix (Fin 2) (Fin 2) F) : act T (A * B) X = act T A (act T B X) := by
  simp only [act, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem act_one (X : Matrix (Fin 2) (Fin 2) F) : act T 1 X = X := by
  simp [act]

theorem map_bar_bar (X : Matrix (Fin 2) (Fin 2) F) : (X.map T.bar).map T.bar = X := by
  ext i j
  simp [T.bar_bar]

theorem act_isHerm (A : Matrix (Fin 2) (Fin 2) F) {X : Matrix (Fin 2) (Fin 2) F}
    (hX : IsHerm T X) : IsHerm T (act T A X) := by
  rw [IsHerm, act, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, map_bar_bar,
    Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hX,
    Matrix.mul_assoc]

theorem map_act (A X : Matrix (Fin 2) (Fin 2) F) :
    (act T A X).map T.bar = act T (A.map T.bar) (X.map T.bar) := by
  rw [act, act, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

variable {r : ℕ}

@[expose] def herm (i : Fin r) (v : (Fin r ⊕ Fin r → K) × F) : Matrix (Fin 2) (Fin 2) F :=
  !![algebraMap K F (v.1 (.inl i)), v.2; T.bar v.2, algebraMap K F (v.1 (.inr i))]

theorem herm_isHerm (i : Fin r) (v : (Fin r ⊕ Fin r → K) × F) : IsHerm T (herm T i v) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [herm, T.bar_bar]

theorem herm_add (i : Fin r) (v w : (Fin r ⊕ Fin r → K) × F) :
    herm T i (v + w) = herm T i v + herm T i w := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [herm]

theorem herm_smul (i : Fin r) (c : K) (v : (Fin r ⊕ Fin r → K) × F) :
    herm T i (c • v) = c • herm T i v := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [herm, Algebra.smul_def]

theorem act_add (A X Y : Matrix (Fin 2) (Fin 2) F) : act T A (X + Y) = act T A X + act T A Y := by
  rw [act, act, act, Matrix.mul_add, Matrix.add_mul]

theorem act_smul (A X : Matrix (Fin 2) (Fin 2) F) (c : K) : act T A (c • X) = c • act T A X := by
  rw [act, act, Matrix.mul_smul, Matrix.smul_mul]

theorem eq_of_herm_eq (i : Fin r) {v w : (Fin r ⊕ Fin r → K) × F}
    (h : herm T i v = herm T i w) (h' : ∀ c, c ≠ .inl i → c ≠ .inr i → v.1 c = w.1 c) :
    v = w := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h11 := congrFun (congrFun h 1) 1
  simp only [herm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h01 h11
  refine Prod.ext (funext fun c => ?_) h01
  by_cases hc : c = .inl i
  · subst hc
    exact (algebraMap K F).injective h00
  by_cases hc' : c = .inr i
  · subst hc'
    exact (algebraMap K F).injective h11
  exact h' c hc hc'

@[expose] def rhoLin (i : Fin r) (A : Matrix (Fin 2) (Fin 2) F) :
    ((Fin r ⊕ Fin r → K) × F) →ₗ[K] ((Fin r ⊕ Fin r → K) × F) where
  toFun v :=
    (fun c => if c = .inl i then retr K F (act T A (herm T i v) 0 0)
      else if c = .inr i then retr K F (act T A (herm T i v) 1 1) else v.1 c,
      act T A (herm T i v) 0 1)
  map_add' v w := by
    refine Prod.ext (funext fun c => ?_) ?_
    · simp only [herm_add, act_add, Matrix.add_apply, map_add, Prod.fst_add, Pi.add_apply]
      split_ifs <;> rfl
    · simp only [herm_add, act_add, Matrix.add_apply, Prod.snd_add]
  map_smul' t v := by
    refine Prod.ext (funext fun c => ?_) ?_
    · simp only [herm_smul, act_smul, Matrix.smul_apply, map_smul, Prod.smul_fst, Pi.smul_apply,
        RingHom.id_apply]
      split_ifs <;> rfl
    · simp only [herm_smul, act_smul, Matrix.smul_apply, Prod.smul_snd, RingHom.id_apply]

theorem rhoLin_apply_of_ne (i : Fin r) (A : Matrix (Fin 2) (Fin 2) F)
    (v : (Fin r ⊕ Fin r → K) × F) {c : Fin r ⊕ Fin r} (h1 : c ≠ .inl i) (h2 : c ≠ .inr i) :
    (rhoLin T i A v).1 c = v.1 c := by
  simp [rhoLin, h1, h2]

theorem rhoLin_apply_inl (i : Fin r) (A : Matrix (Fin 2) (Fin 2) F)
    (v : (Fin r ⊕ Fin r → K) × F) :
    (rhoLin T i A v).1 (.inl i) = retr K F (act T A (herm T i v) 0 0) := by
  simp [rhoLin]

theorem rhoLin_apply_inr (i : Fin r) (A : Matrix (Fin 2) (Fin 2) F)
    (v : (Fin r ⊕ Fin r → K) × F) :
    (rhoLin T i A v).1 (.inr i) = retr K F (act T A (herm T i v) 1 1) := by
  simp [rhoLin]

theorem rhoLin_apply_snd (i : Fin r) (A : Matrix (Fin 2) (Fin 2) F)
    (v : (Fin r ⊕ Fin r → K) × F) :
    (rhoLin T i A v).2 = act T A (herm T i v) 0 1 :=
  rfl

theorem herm_rhoLin (i : Fin r) (A : Matrix (Fin 2) (Fin 2) F) (v : (Fin r ⊕ Fin r → K) × F) :
    herm T i (rhoLin T i A v) = act T A (herm T i v) := by
  have hH := act_isHerm T A (herm_isHerm T i v)
  have h00 : T.bar (act T A (herm T i v) 0 0) = act T A (herm T i v) 0 0 := by
    simpa using congrFun (congrFun hH 0) 0
  have h11 : T.bar (act T A (herm T i v) 1 1) = act T A (herm T i v) 1 1 := by
    simpa using congrFun (congrFun hH 1) 1
  have h10 : T.bar (act T A (herm T i v) 0 1) = act T A (herm T i v) 1 0 := by
    simpa using congrFun (congrFun hH 1) 0
  rw [herm, rhoLin_apply_inl, rhoLin_apply_inr, rhoLin_apply_snd, algebraMap_retr T h00,
    algebraMap_retr T h11, h10]
  exact (Matrix.eta_fin_two _).symm

theorem rhoLin_mul (i : Fin r) (A B : Matrix (Fin 2) (Fin 2) F) :
    rhoLin T i (A * B) = rhoLin T i A ∘ₗ rhoLin T i B := by
  refine LinearMap.ext fun v => eq_of_herm_eq T i ?_ fun c h1 h2 => ?_
  · rw [LinearMap.comp_apply, herm_rhoLin, herm_rhoLin, herm_rhoLin, act_mul]
  · rw [LinearMap.comp_apply, rhoLin_apply_of_ne T i _ _ h1 h2, rhoLin_apply_of_ne T i _ _ h1 h2,
      rhoLin_apply_of_ne T i _ _ h1 h2]

theorem rhoLin_one (i : Fin r) : rhoLin T i 1 = LinearMap.id := by
  refine LinearMap.ext fun v => eq_of_herm_eq T i ?_ fun c h1 h2 => ?_
  · rw [herm_rhoLin, act_one, LinearMap.id_apply]
  · rw [rhoLin_apply_of_ne T i _ _ h1 h2, LinearMap.id_apply]

@[expose] def rho (i : Fin r) :
    SpecialLinearGroup (Fin 2) F →* ((Fin r ⊕ Fin r → K) × F) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × F) where
  toFun A := LinearEquiv.ofLinearMap (rhoLin T i A.1) (rhoLin T i A⁻¹.1)
    (by
      rw [← rhoLin_mul]
      exact (congrArg (fun B : SpecialLinearGroup (Fin 2) F => rhoLin T i B.1)
        (mul_inv_cancel A)).trans (rhoLin_one T i))
    (by
      rw [← rhoLin_mul]
      exact (congrArg (fun B : SpecialLinearGroup (Fin 2) F => rhoLin T i B.1)
        (inv_mul_cancel A)).trans (rhoLin_one T i))
  map_one' := LinearEquiv.ext fun v => by
    change rhoLin T i 1 v = v
    rw [rhoLin_one, LinearMap.id_apply]
  map_mul' A B := LinearEquiv.ext fun v => by
    change rhoLin T i (A.1 * B.1) v = rhoLin T i A.1 (rhoLin T i B.1 v)
    rw [rhoLin_mul, LinearMap.comp_apply]

theorem rho_apply (i : Fin r) (A : SpecialLinearGroup (Fin 2) F) (v : (Fin r ⊕ Fin r → K) × F) :
    rho T i A v = rhoLin T i A.1 v :=
  rfl

theorem herm_rho (i : Fin r) (A : SpecialLinearGroup (Fin 2) F) (v : (Fin r ⊕ Fin r → K) × F) :
    herm T i (rho T i A v) = act T A.1 (herm T i v) :=
  herm_rhoLin T i A.1 v

theorem rho_apply_of_ne (i : Fin r) (A : SpecialLinearGroup (Fin 2) F)
    (v : (Fin r ⊕ Fin r → K) × F) {c : Fin r ⊕ Fin r} (h1 : c ≠ .inl i) (h2 : c ≠ .inr i) :
    (rho T i A v).1 c = v.1 c :=
  rhoLin_apply_of_ne T i A.1 v h1 h2

variable (F) in
@[expose] def upperSL (t : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩

variable (F) in
@[expose] def lowerSL (t : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two_of]⟩

variable (F) in
@[expose] def diagSL (s : Fˣ) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two_of]⟩

variable (F) in
@[expose] def swapSL : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩

theorem coe_upperSL (t : F) : (upperSL F t : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] :=
  rfl

theorem coe_lowerSL (t : F) : (lowerSL F t : Matrix (Fin 2) (Fin 2) F) = !![1, 0; t, 1] :=
  rfl

theorem coe_diagSL (s : Fˣ) :
    (diagSL F s : Matrix (Fin 2) (Fin 2) F) = !![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)] :=
  rfl

theorem coe_swapSL [CharP K 2] : (swapSL F : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := by
  change !![0, 1; -1, 0] = !![(0 : F), 1; 1, 0]
  rw [neg_eq_self_of_charP (K := K)]

theorem act_fin_two (a b c d x z w y : F) :
    act T !![a, b; c, d] !![x, z; w, y] =
      !![(a * x + b * w) * T.bar a + (a * z + b * y) * T.bar b,
        (a * x + b * w) * T.bar c + (a * z + b * y) * T.bar d;
        (c * x + d * w) * T.bar a + (c * z + d * y) * T.bar b,
        (c * x + d * w) * T.bar c + (c * z + d * y) * T.bar d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [act, Matrix.mul_apply, Fin.sum_univ_two]

theorem herm_eq (i : Fin r) (v : (Fin r ⊕ Fin r → K) × F) :
    herm T i v = !![algebraMap K F (v.1 (.inl i)), v.2; T.bar v.2, algebraMap K F (v.1 (.inr i))] :=
  rfl

omit [Field F] [Algebra K F] in
theorem fin_two_matrix_eq {α : Type*} {a b c d a' b' c' d' : α} (h₁ : a = a') (h₂ : b = b')
    (h₃ : c = c') (h₄ : d = d') : !![a, b; c, d] = !![a', b'; c', d'] := by
  rw [h₁, h₂, h₃, h₄]

omit [Algebra K F] in
theorem hypVec_fst (c d : Fin r ⊕ Fin r) : (hypVec K F c).1 d = if d = c then 1 else 0 := by
  simp [hypVec, Pi.single_apply]

omit [Algebra K F] in
theorem hypVec_snd (c : Fin r ⊕ Fin r) : (hypVec K F c).2 = 0 :=
  rfl

theorem eichler_hypVec_tail_fst (c : Fin r ⊕ Fin r) (t : F) (v : (Fin r ⊕ Fin r → K) × F)
    (d : Fin r ⊕ Fin r) :
    (eichler (quadTail r (normForm T)) (hypVec K F c) (0, t) v).1 d =
      v.1 d - if d = c then polar (normForm T) v.2 t + normForm T t * v.1 c.swap else 0 := by
  rw [eichler_apply (quadTail_hypVec _) (polar_hypVec_tail _ t), polar_hypVec, polar_quadTail,
    polar_zero_right, zero_add, quadTail_tail]
  by_cases hd : d = c <;> simp [hypVec_fst, hd, mul_comm]

theorem eichler_hypVec_tail_snd (c : Fin r ⊕ Fin r) (t : F) (v : (Fin r ⊕ Fin r → K) × F) :
    (eichler (quadTail r (normForm T)) (hypVec K F c) (0, t) v).2 = v.2 + v.1 c.swap • t := by
  rw [eichler_apply (quadTail_hypVec _) (polar_hypVec_tail _ t), polar_hypVec]
  simp [hypVec_snd]

theorem rho_upperSL [CharP K 2] (i : Fin r) (t : F) :
    rho T i (upperSL F t) = eichler (quadTail r (normForm T)) (hypVec K F (.inl i)) (0, t) := by
  have h2 : (2 : F) = 0 := two_eq_zero_of_charP (K := K)
  refine LinearEquiv.ext fun v => eq_of_herm_eq T i ?_ fun c h1 h2' => ?_
  · rw [herm_rho, coe_upperSL, herm_eq, herm_eq, act_fin_two, eichler_hypVec_tail_fst,
      eichler_hypVec_tail_fst, eichler_hypVec_tail_snd]
    simp only [Sum.swap_inl, ↓reduceIte, reduceCtorEq, sub_zero]
    refine fin_two_matrix_eq ?_ ?_ ?_ ?_
    · rw [map_sub, map_add, RingHom.map_mul, algebraMap_polar_normForm,
        algebraMap_normForm, map_one]
      linear_combination (v.2 * T.bar t + t * T.bar v.2 +
        algebraMap K F (v.1 (.inr i)) * (t * T.bar t)) * h2
    · rw [map_zero, map_one, Algebra.smul_def]
      ring
    · rw [map_one, map_add, map_smul, Algebra.smul_def]
      ring
    · rw [map_zero, map_one]
      ring
  · rw [rho_apply_of_ne T i _ v h1 h2', eichler_hypVec_tail_fst, ite_eq_right h1, sub_zero]

theorem rho_lowerSL [CharP K 2] (i : Fin r) (t : F) :
    rho T i (lowerSL F t) =
      eichler (quadTail r (normForm T)) (hypVec K F (.inr i)) (0, T.bar t) := by
  have h2 : (2 : F) = 0 := two_eq_zero_of_charP (K := K)
  refine LinearEquiv.ext fun v => eq_of_herm_eq T i ?_ fun c h1 h2' => ?_
  · rw [herm_rho, coe_lowerSL, herm_eq, herm_eq, act_fin_two, eichler_hypVec_tail_fst,
      eichler_hypVec_tail_fst, eichler_hypVec_tail_snd]
    simp only [Sum.swap_inr, ↓reduceIte, reduceCtorEq, sub_zero]
    refine fin_two_matrix_eq ?_ ?_ ?_ ?_
    · rw [map_zero, map_one]
      ring
    · rw [map_one, Algebra.smul_def]
      ring
    · rw [map_zero, map_one, map_add, map_smul, T.bar_bar, Algebra.smul_def]
      ring
    · rw [map_one, map_sub, map_add, RingHom.map_mul, algebraMap_polar_normForm,
        algebraMap_normForm, T.bar_bar]
      linear_combination (t * T.bar t * algebraMap K F (v.1 (.inl i)) + T.bar v.2 * T.bar t +
        t * v.2) * h2
  · rw [rho_apply_of_ne T i _ v h1 h2', eichler_hypVec_tail_fst, ite_eq_right h2', sub_zero]

theorem algebraMap_rho_inl (i : Fin r) (A : SpecialLinearGroup (Fin 2) F)
    (v : (Fin r ⊕ Fin r → K) × F) :
    algebraMap K F ((rho T i A v).1 (.inl i)) = act T A.1 (herm T i v) 0 0 := by
  have := congrFun (congrFun (herm_rho T i A v) 0) 0
  rwa [herm_eq] at this

theorem algebraMap_rho_inr (i : Fin r) (A : SpecialLinearGroup (Fin 2) F)
    (v : (Fin r ⊕ Fin r → K) × F) :
    algebraMap K F ((rho T i A v).1 (.inr i)) = act T A.1 (herm T i v) 1 1 := by
  have := congrFun (congrFun (herm_rho T i A v) 1) 1
  rwa [herm_eq] at this

theorem rho_snd (i : Fin r) (A : SpecialLinearGroup (Fin 2) F) (v : (Fin r ⊕ Fin r → K) × F) :
    (rho T i A v).2 = act T A.1 (herm T i v) 0 1 := by
  have := congrFun (congrFun (herm_rho T i A v) 0) 1
  rwa [herm_eq] at this

theorem rho_diagSL (i : Fin r) (s : Fˣ) (v : (Fin r ⊕ Fin r → K) × F) :
    (rho T i (diagSL F s) v).1 (.inl i) = normForm T s * v.1 (.inl i) ∧
      (rho T i (diagSL F s) v).1 (.inr i) = (normForm T s)⁻¹ * v.1 (.inr i) ∧
      (rho T i (diagSL F s) v).2 = ((s : F) / T.bar s) * v.2 := by
  refine ⟨(algebraMap K F).injective ?_, (algebraMap K F).injective ?_, ?_⟩
  · rw [algebraMap_rho_inl, coe_diagSL, herm_eq, act_fin_two, RingHom.map_mul,
      algebraMap_normForm]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
      Matrix.cons_val_fin_one, map_zero]
    ring
  · rw [algebraMap_rho_inr, coe_diagSL, herm_eq, act_fin_two, RingHom.map_mul, map_inv₀,
      algebraMap_normForm]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, map_zero, Units.val_inv_eq_inv_val, map_inv₀]
    rw [mul_inv]
    ring
  · rw [rho_snd, coe_diagSL, herm_eq, act_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, map_zero, Units.val_inv_eq_inv_val, map_inv₀]
    ring

theorem rho_swapSL [CharP K 2] (i : Fin r) (v : (Fin r ⊕ Fin r → K) × F) :
    rho T i (swapSL F) v = (v.1 ∘ Equiv.swap (.inl i) (.inr i), T.bar v.2) := by
  refine eq_of_herm_eq T i ?_ fun c h1 h2 => ?_
  · rw [herm_rho, coe_swapSL (K := K), herm_eq, herm_eq, act_fin_two]
    simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right, T.bar_bar]
    refine fin_two_matrix_eq ?_ ?_ ?_ ?_
    · rw [map_zero, map_one]
      ring
    · rw [map_zero, map_one]
      ring
    · rw [map_zero, map_one]
      ring
    · rw [map_zero, map_one]
      ring
  · change (rho T i (swapSL F) v).1 c = v.1 (Equiv.swap (.inl i) (.inr i) c)
    rw [rho_apply_of_ne T i _ v h1 h2, Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem transvection_zero_one (c : F) :
    SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c = upperSL F c := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [SpecialLinearGroup.transvection_coe, coe_upperSL]

theorem transvection_one_zero (c : F) :
    SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) c = lowerSL F c := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [SpecialLinearGroup.transvection_coe, coe_lowerSL]

theorem rho_mem [CharP K 2] (i : Fin r) (A : SpecialLinearGroup (Fin 2) F) :
    rho T i A ∈ orthElementaryGroup (quadTail r (normForm T)) := by
  have h : (⊤ : Subgroup (SpecialLinearGroup (Fin 2) F)).map (rho T i) ≤
      orthElementaryGroup (quadTail r (normForm T)) := by
    rw [← CFSG.LinearGroups.special_linear_elementary_generation, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨a, b, hab, c, rfl⟩, rfl⟩
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · change rho T i (SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c) ∈ _
      rw [transvection_zero_one, rho_upperSL]
      exact eichler_mem_elementaryGroup _ _ _
    · change rho T i (SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) c) ∈ _
      rw [transvection_one_zero, rho_lowerSL]
      exact eichler_mem_elementaryGroup _ _ _
    · exact absurd rfl hab
  exact h ⟨A, trivial, rfl⟩

theorem rho_injective [CharP K 2] (i : Fin r) : Function.Injective (rho T i) := by
  have h2 : (2 : F) = 0 := two_eq_zero_of_charP (K := K)
  rw [injective_iff_map_eq_one]
  intro A hA
  have key : ∀ v, act T A.1 (herm T i v) = herm T i v := fun v => by
    rw [← herm_rho, hA]
    rfl
  have hA' : A.1 = !![A.1 0 0, A.1 0 1; A.1 1 0, A.1 1 1] := Matrix.eta_fin_two _
  set a := A.1 0 0
  set b := A.1 0 1
  set c := A.1 1 0
  set d := A.1 1 1
  have hdet : a * d - b * c = 1 := by
    have := A.2
    rw [hA', Matrix.det_fin_two_of] at this
    exact this
  have e1 := key (Pi.single (.inl i) 1, 0)
  have e2 := key (Pi.single (.inr i) 1, 0)
  have e3 := key (0, 1)
  rw [hA', herm_eq, act_fin_two] at e1 e2 e3
  have e1a := congrFun (congrFun e1 0) 0
  have e1d := congrFun (congrFun e1 1) 1
  have e2a := congrFun (congrFun e2 0) 0
  have e2d := congrFun (congrFun e2 1) 1
  have e3b := congrFun (congrFun e3 0) 1
  simp at e1a e1d e2a e2d e3b
  have hc : c = 0 := e1d
  have hb : b = 0 := e2a
  rw [hb, hc, mul_zero, sub_zero] at hdet
  rw [hb, zero_mul, zero_add] at e3b
  have ha0 : a ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have h1 : T.bar a = d := mul_left_cancel₀ ha0 (e1a.trans hdet.symm)
  have h3 : T.bar d = d := mul_left_cancel₀ ha0 (e3b.trans hdet.symm)
  have had : a = d := by rw [← T.bar_bar a, h1, h3]
  rw [← had] at hdet
  have ha1 : a = 1 := by
    have : (a - 1) * (a - 1) = 0 := by linear_combination hdet + (1 - a) * h2
    rw [mul_self_eq_zero, sub_eq_zero] at this
    exact this
  have hd1 : d = 1 := had ▸ ha1
  ext p q
  fin_cases p <;> fin_cases q
  · exact ha1
  · exact hb
  · exact hc
  · exact hd1

end CFSG.LocalAnalysis.ComponentInitial.NormTail
