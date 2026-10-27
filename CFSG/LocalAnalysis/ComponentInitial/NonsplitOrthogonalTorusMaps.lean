module

public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalSignedPerms

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.NormTail

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal OrthogonalTail

section Sqrt

variable (L : Type*) [Field L]

@[expose] def sqrtHom : Lˣ →* Lˣ :=
  powMonoidHom (Nat.card L / 2)

variable {L}

theorem two_dvd_natCard [Finite L] [CharP L 2] : 2 ∣ Nat.card L := by
  have := Fintype.ofFinite L
  rw [Nat.card_eq_fintype_card]
  exact (CharP.cast_eq_zero_iff L 2 _).1 (FiniteField.cast_card_eq_zero L)

theorem sqrtHom_sq [Finite L] [CharP L 2] (x : Lˣ) : sqrtHom L x ^ 2 = x := by
  have := Fintype.ofFinite L
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, sqrtHom, powMonoidHom_apply, Units.val_pow_eq_pow_val, ← pow_mul,
    Nat.div_mul_cancel two_dvd_natCard, Nat.card_eq_fintype_card, FiniteField.pow_card]

end Sqrt

section Norm

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (T : NormTailData K F)

@[expose] def normHom : F →* K where
  toFun := normForm T
  map_one' := normForm_one T
  map_mul' := normForm_mul T

@[expose] def normUnits : Fˣ →* Kˣ :=
  Units.map (normHom T)

theorem coe_normUnits (s : Fˣ) : (normUnits T s : K) = normForm T s :=
  rfl

@[expose] def normOne : Subgroup Fˣ :=
  (normUnits T).ker

theorem mem_normOne {c : Fˣ} : c ∈ normOne T ↔ normForm T c = 1 := by
  rw [normOne, MonoidHom.mem_ker, Units.ext_iff, coe_normUnits, Units.val_one]

theorem mul_bar_eq_one {c : Fˣ} (hc : c ∈ normOne T) : (c : F) * T.bar c = 1 := by
  rw [← algebraMap_normForm, (mem_normOne T).1 hc, map_one]

theorem normForm_algebraMap (k : K) : normForm T (algebraMap K F k) = k ^ 2 := by
  apply (algebraMap K F).injective
  rw [algebraMap_normForm, bar_algebraMap, map_pow, pow_two]

@[expose] def barUnits : Fˣ →* Fˣ :=
  Units.map (T.bar : F →* F)

theorem coe_barUnits (s : Fˣ) : (barUnits T s : F) = T.bar s :=
  rfl

theorem normForm_bar (z : F) : normForm T (T.bar z) = normForm T z := by
  apply (algebraMap K F).injective
  rw [algebraMap_normForm, algebraMap_normForm, T.bar_bar, mul_comm]

@[expose] def barQuot (s : Fˣ) : Fˣ :=
  s * (barUnits T s)⁻¹

theorem barQuot_mem (s : Fˣ) : barQuot T s ∈ normOne T := by
  rw [mem_normOne, barQuot, Units.val_mul, normForm_mul, Units.val_inv_eq_inv_val,
    normForm_inv, coe_barUnits, normForm_bar, mul_inv_cancel₀]
  rw [Ne, normForm_eq_zero_iff]
  exact s.ne_zero

theorem coe_barQuot (s : Fˣ) : (barQuot T s : F) = (s : F) / T.bar s := by
  rw [barQuot, Units.val_mul, Units.val_inv_eq_inv_val, coe_barUnits, div_eq_mul_inv]

theorem barUnits_algebraMap (k : Kˣ) :
    barUnits T (Units.map (algebraMap K F : K →* F) k) = Units.map (algebraMap K F : K →* F) k :=
  Units.ext (bar_algebraMap T k)

theorem barQuot_algebraMap (k : Kˣ) : barQuot T (Units.map (algebraMap K F : K →* F) k) = 1 := by
  rw [barQuot, barUnits_algebraMap, mul_inv_cancel]

theorem normUnits_algebraMap (k : Kˣ) :
    normUnits T (Units.map (algebraMap K F : K →* F) k) = k ^ 2 :=
  Units.ext (normForm_algebraMap T k)

end Norm

section Torus

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (T : NormTailData K F) {r : ℕ}

@[expose] def torusScal (a : Fin r → Kˣ) : Fin r ⊕ Fin r → K :=
  Sum.elim (fun i => (a i : K)) (fun i => ((a i)⁻¹ : Kˣ))

theorem torusScal_inv_mul (a : Fin r → Kˣ) (k : Fin r ⊕ Fin r) :
    torusScal a⁻¹ k * torusScal a k = 1 := by
  rcases k with i | i <;> simp [torusScal]

theorem torusScal_mul_inv (a : Fin r → Kˣ) (k : Fin r ⊕ Fin r) :
    torusScal a k * torusScal a⁻¹ k = 1 := by
  rw [mul_comm, torusScal_inv_mul]

theorem torusScal_mul (a a' : Fin r → Kˣ) (k : Fin r ⊕ Fin r) :
    torusScal (a * a') k = torusScal a k * torusScal a' k := by
  rcases k with i | i <;> simp [torusScal, mul_comm]

theorem torusScal_one (k : Fin r ⊕ Fin r) : torusScal (1 : Fin r → Kˣ) k = 1 := by
  rcases k with i | i <;> simp [torusScal]

variable (F) in
@[expose] def torusMap (a : Fin r → Kˣ) (c : Fˣ) :
    ((Fin r ⊕ Fin r → K) × F) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × F) where
  toFun v := (fun k => torusScal a k * v.1 k, (c : F) * v.2)
  invFun v := (fun k => torusScal a⁻¹ k * v.1 k, ((c⁻¹ : Fˣ) : F) * v.2)
  map_add' v w := Prod.ext (funext fun _ => mul_add _ _ _) (mul_add _ _ _)
  map_smul' t v := Prod.ext (funext fun _ => mul_left_comm _ _ _) (mul_smul_comm t _ _)
  left_inv v := Prod.ext (funext fun k => by
    change torusScal a⁻¹ k * (torusScal a k * v.1 k) = v.1 k
    rw [← mul_assoc, torusScal_inv_mul, one_mul]) (Units.inv_mul_cancel_left c v.2)
  right_inv v := Prod.ext (funext fun k => by
    change torusScal a k * (torusScal a⁻¹ k * v.1 k) = v.1 k
    rw [← mul_assoc, torusScal_mul_inv, one_mul]) (Units.mul_inv_cancel_left c v.2)

theorem torusMap_apply (a : Fin r → Kˣ) (c : Fˣ) (v : (Fin r ⊕ Fin r → K) × F) :
    torusMap F a c v = (fun k => torusScal a k * v.1 k, (c : F) * v.2) :=
  rfl

variable (F r) in
@[expose] def torusHom :
    (Fin r → Kˣ) × Fˣ →* ((Fin r ⊕ Fin r → K) × F) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × F) where
  toFun p := torusMap F p.1 p.2
  map_one' := LinearEquiv.ext fun v => Prod.ext (funext fun k => by
    change torusScal (1 : Fin r → Kˣ) k * v.1 k = v.1 k
    rw [torusScal_one, one_mul]) (one_mul v.2)
  map_mul' p p' := LinearEquiv.ext fun v => Prod.ext (funext fun k => by
    change torusScal (p.1 * p'.1) k * v.1 k = torusScal p.1 k * (torusScal p'.1 k * v.1 k)
    rw [torusScal_mul, mul_assoc]) (by
    change ((p.2 * p'.2 : Fˣ) : F) * v.2 = (p.2 : F) * ((p'.2 : F) * v.2)
    rw [Units.val_mul, mul_assoc])

theorem torusHom_apply (p : (Fin r → Kˣ) × Fˣ) : torusHom F r p = torusMap F p.1 p.2 :=
  rfl

theorem torusHom_injective : Function.Injective (torusHom (K := K) F r) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, c⟩ h
  have ha : ∀ i, a i = 1 := fun i => by
    have := congrArg (fun g : ((Fin r ⊕ Fin r → K) × F) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × F) =>
      (g ((Pi.single (Sum.inl i) 1, 0) : (Fin r ⊕ Fin r → K) × F)).1 (Sum.inl i)) h
    simp only [torusHom_apply, torusMap_apply, Pi.single_eq_same, mul_one,
      LinearEquiv.coe_one, id_eq] at this
    exact Units.ext this
  have hc : c = 1 := by
    have := congrArg (fun g : ((Fin r ⊕ Fin r → K) × F) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × F) =>
      (g ((0, 1) : (Fin r ⊕ Fin r → K) × F)).2) h
    simp only [torusHom_apply, torusMap_apply, mul_one, LinearEquiv.coe_one, id_eq] at this
    exact Units.ext this
  exact Prod.ext (funext ha) hc

theorem rho_diagSL_eq_torusMap (i : Fin r) (s : Fˣ) :
    rho T i (diagSL F s) = torusMap F (Pi.mulSingle i (normUnits T s)) (barQuot T s) := by
  refine LinearEquiv.ext fun v => Prod.ext (funext fun c => ?_) ?_
  · obtain ⟨h1, h2, -⟩ := rho_diagSL T i s v
    rw [torusMap_apply]
    rcases c with k | k
    · by_cases hk : k = i
      · subst hk
        rw [h1]
        simp [torusScal, coe_normUnits]
      · rw [rho_apply_of_ne T i _ v (by simpa using hk) (by simp)]
        simp [torusScal, hk]
    · by_cases hk : k = i
      · subst hk
        rw [h2]
        simp [torusScal, coe_normUnits]
      · rw [rho_apply_of_ne T i _ v (by simp) (by simpa using hk)]
        simp [torusScal, hk]
  · rw [(rho_diagSL T i s v).2.2, torusMap_apply, coe_barQuot]

end Torus

section Pair

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {r : ℕ} {i j : Fin r}

@[expose] def pairVec (i j : Fin r) (A : Matrix (Fin 2) (Fin 2) K) (x : Fin r → K) : Fin r → K :=
  fun k => if k = i then A 0 0 * x i + A 0 1 * x j
    else if k = j then A 1 0 * x i + A 1 1 * x j else x k

theorem pairVec_add (A : Matrix (Fin 2) (Fin 2) K) (x y : Fin r → K) :
    pairVec i j A (x + y) = pairVec i j A x + pairVec i j A y := by
  funext k
  simp only [pairVec, Pi.add_apply]
  split_ifs <;> ring

theorem pairVec_smul (A : Matrix (Fin 2) (Fin 2) K) (t : K) (x : Fin r → K) :
    pairVec i j A (t • x) = t • pairVec i j A x := by
  funext k
  simp only [pairVec, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem pairVec_mul (hij : i ≠ j) (A B : Matrix (Fin 2) (Fin 2) K) (x : Fin r → K) :
    pairVec i j (A * B) x = pairVec i j A (pairVec i j B x) := by
  funext k
  have hji := hij.symm
  by_cases hki : k = i
  · subst hki
    simp [pairVec, hji, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · by_cases hkj : k = j
    · subst hkj
      simp [pairVec, hji, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    · simp [pairVec, hki, hkj]

theorem pairVec_one (x : Fin r → K) : pairVec i j 1 x = x := by
  funext k
  simp only [pairVec]
  split_ifs with h1 h2
  · subst h1
    simp
  · subst h2
    simp
  · rfl

variable (F) in
@[expose] def pairLin (i j : Fin r) (A B : Matrix (Fin 2) (Fin 2) K) :
    ((Fin r ⊕ Fin r → K) × F) →ₗ[K] ((Fin r ⊕ Fin r → K) × F) where
  toFun v := (Sum.elim (pairVec i j A (v.1 ∘ Sum.inl)) (pairVec i j B (v.1 ∘ Sum.inr)), v.2)
  map_add' v w := by
    refine Prod.ext (funext fun c => ?_) rfl
    rcases c with k | k
    · change pairVec i j A ((v.1 + w.1) ∘ Sum.inl) k =
        pairVec i j A (v.1 ∘ Sum.inl) k + pairVec i j A (w.1 ∘ Sum.inl) k
      rw [show (v.1 + w.1) ∘ Sum.inl = v.1 ∘ Sum.inl + w.1 ∘ Sum.inl from rfl, pairVec_add]
      rfl
    · change pairVec i j B ((v.1 + w.1) ∘ Sum.inr) k =
        pairVec i j B (v.1 ∘ Sum.inr) k + pairVec i j B (w.1 ∘ Sum.inr) k
      rw [show (v.1 + w.1) ∘ Sum.inr = v.1 ∘ Sum.inr + w.1 ∘ Sum.inr from rfl, pairVec_add]
      rfl
  map_smul' t v := by
    refine Prod.ext (funext fun c => ?_) rfl
    rcases c with k | k
    · change pairVec i j A ((t • v.1) ∘ Sum.inl) k = t * pairVec i j A (v.1 ∘ Sum.inl) k
      rw [show (t • v.1) ∘ Sum.inl = t • (v.1 ∘ Sum.inl) from rfl, pairVec_smul]
      rfl
    · change pairVec i j B ((t • v.1) ∘ Sum.inr) k = t * pairVec i j B (v.1 ∘ Sum.inr) k
      rw [show (t • v.1) ∘ Sum.inr = t • (v.1 ∘ Sum.inr) from rfl, pairVec_smul]
      rfl

theorem pairLin_apply (A B : Matrix (Fin 2) (Fin 2) K) (v : (Fin r ⊕ Fin r → K) × F) :
    pairLin F i j A B v =
      (Sum.elim (pairVec i j A (v.1 ∘ Sum.inl)) (pairVec i j B (v.1 ∘ Sum.inr)), v.2) :=
  rfl

theorem pairLin_mul (hij : i ≠ j) (A A' B B' : Matrix (Fin 2) (Fin 2) K) :
    pairLin F i j (A * A') (B * B') = pairLin F i j A B ∘ₗ pairLin F i j A' B' := by
  refine LinearMap.ext fun v => Prod.ext (funext fun c => ?_) rfl
  rcases c with k | k
  · change pairVec i j (A * A') (v.1 ∘ Sum.inl) k =
      pairVec i j A (pairVec i j A' (v.1 ∘ Sum.inl)) k
    rw [pairVec_mul hij]
  · change pairVec i j (B * B') (v.1 ∘ Sum.inr) k =
      pairVec i j B (pairVec i j B' (v.1 ∘ Sum.inr)) k
    rw [pairVec_mul hij]

theorem pairLin_one : pairLin F i j (1 : Matrix (Fin 2) (Fin 2) K) 1 = LinearMap.id := by
  refine LinearMap.ext fun v => Prod.ext (funext fun c => ?_) rfl
  rcases c with k | k
  · change pairVec i j 1 (v.1 ∘ Sum.inl) k = v.1 (Sum.inl k)
    rw [pairVec_one]
    rfl
  · change pairVec i j 1 (v.1 ∘ Sum.inr) k = v.1 (Sum.inr k)
    rw [pairVec_one]
    rfl

variable (F) in
@[expose] def eta (hij : i ≠ j) :
    SpecialLinearGroup (Fin 2) K →* ((Fin r ⊕ Fin r → K) × F) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × F) where
  toFun A := LinearEquiv.ofLinearMap (pairLin F i j A.1 (A⁻¹).1ᵀ) (pairLin F i j (A⁻¹).1 A.1ᵀ)
    (by rw [← pairLin_mul hij, coe_mul_coe_inv, ← Matrix.transpose_mul, coe_mul_coe_inv,
      Matrix.transpose_one, pairLin_one])
    (by rw [← pairLin_mul hij, coe_inv_mul_coe, ← Matrix.transpose_mul, coe_inv_mul_coe,
      Matrix.transpose_one, pairLin_one])
  map_one' := LinearEquiv.ext fun v => by
    change pairLin F i j (1 : SpecialLinearGroup (Fin 2) K).1
      ((1 : SpecialLinearGroup (Fin 2) K)⁻¹).1ᵀ v = v
    rw [inv_one]
    change pairLin F i j (1 : Matrix (Fin 2) (Fin 2) K) (1 : Matrix (Fin 2) (Fin 2) K)ᵀ v = v
    rw [Matrix.transpose_one, pairLin_one, LinearMap.id_apply]
  map_mul' A B := LinearEquiv.ext fun v => by
    change pairLin F i j (A.1 * B.1) ((A * B)⁻¹).1ᵀ v =
      pairLin F i j A.1 (A⁻¹).1ᵀ (pairLin F i j B.1 (B⁻¹).1ᵀ v)
    rw [_root_.mul_inv_rev]
    change pairLin F i j (A.1 * B.1) ((B⁻¹).1 * (A⁻¹).1)ᵀ v = _
    rw [Matrix.transpose_mul, pairLin_mul hij, LinearMap.comp_apply]

theorem eta_apply (hij : i ≠ j) (A : SpecialLinearGroup (Fin 2) K)
    (v : (Fin r ⊕ Fin r → K) × F) :
    eta F hij A v = pairLin F i j A.1 (A⁻¹).1ᵀ v :=
  rfl

theorem eta_transvection_zero_one (hij : i ≠ j) (c : K) :
    eta F hij (SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c) =
      psi F r (SpecialLinearGroup.transvection hij c) := by
  refine LinearEquiv.ext fun v => Prod.ext (funext fun d => ?_) rfl
  rw [eta_apply, psi_apply, pairLin_apply, SpecialLinearGroup.transvection_inv,
    SpecialLinearGroup.transvection_inv]
  rcases d with k | k
  · simp only [Sum.elim_inl, SpecialLinearGroup.transvection_coe, pairVec, Matrix.add_mulVec,
      Matrix.one_mulVec, Matrix.single_mulVec, Pi.add_apply, Function.update_apply,
      Pi.zero_apply, Function.comp_apply]
    by_cases hki : k = i
    · subst hki
      simp
    · by_cases hkj : k = j
      · subst hkj
        simp [hki]
      · simp [hki, hkj]
  · simp only [Sum.elim_inr, SpecialLinearGroup.transvection_coe, pairVec, Matrix.transpose_add,
      Matrix.transpose_one, Matrix.transpose_single, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.single_mulVec, Pi.add_apply, Function.update_apply, Pi.zero_apply,
      Function.comp_apply]
    by_cases hki : k = i
    · subst hki
      simp [hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [hki]
        ring
      · simp [hki, hkj]

theorem eta_transvection_one_zero (hij : i ≠ j) (c : K) :
    eta F hij (SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) c) =
      psi F r (SpecialLinearGroup.transvection hij.symm c) := by
  refine LinearEquiv.ext fun v => Prod.ext (funext fun d => ?_) rfl
  rw [eta_apply, psi_apply, pairLin_apply, SpecialLinearGroup.transvection_inv,
    SpecialLinearGroup.transvection_inv]
  rcases d with k | k
  · simp only [Sum.elim_inl, SpecialLinearGroup.transvection_coe, pairVec, Matrix.add_mulVec,
      Matrix.one_mulVec, Matrix.single_mulVec, Pi.add_apply, Function.update_apply,
      Pi.zero_apply, Function.comp_apply]
    by_cases hki : k = i
    · subst hki
      simp [hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [hki]
        ring
      · simp [hki, hkj]
  · simp only [Sum.elim_inr, SpecialLinearGroup.transvection_coe, pairVec, Matrix.transpose_add,
      Matrix.transpose_one, Matrix.transpose_single, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.single_mulVec, Pi.add_apply, Function.update_apply, Pi.zero_apply,
      Function.comp_apply]
    by_cases hki : k = i
    · subst hki
      simp
    · by_cases hkj : k = j
      · subst hkj
        simp [hki]
      · simp [hki, hkj]

variable (T : NormTailData K F)

theorem eta_mem (hij : i ≠ j) (A : SpecialLinearGroup (Fin 2) K) :
    eta F hij A ∈ orthElementaryGroup (quadTail r (normForm T)) := by
  have h : (⊤ : Subgroup (SpecialLinearGroup (Fin 2) K)).map (eta F hij) ≤
      orthElementaryGroup (quadTail r (normForm T)) := by
    rw [← CFSG.LinearGroups.special_linear_elementary_generation, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨a, b, hab, c, rfl⟩, rfl⟩
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · change eta F hij (SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c) ∈ _
      rw [eta_transvection_zero_one]
      exact psi_mem T _
    · change eta F hij (SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) c) ∈ _
      rw [eta_transvection_one_zero]
      exact psi_mem T _
    · exact absurd rfl hab
  exact h ⟨A, trivial, rfl⟩

@[expose] def etaG (hij : i ≠ j) : SpecialLinearGroup (Fin 2) K →* G0 T r :=
  (eta F hij).codRestrict _ (eta_mem T hij)

theorem coe_etaG (hij : i ≠ j) (A : SpecialLinearGroup (Fin 2) K) :
    (etaG T hij A : ((Fin r ⊕ Fin r → K) × F) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × F)) = eta F hij A :=
  rfl

theorem coe_diagSL_inv (a : Kˣ) :
    (((diagSL K a)⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![((a⁻¹ : Kˣ) : K), 0; 0, (a : K)] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_diagSL, Matrix.adjugate_fin_two_of]
  simp

theorem eta_diagSL (hij : i ≠ j) (a : Kˣ) :
    eta F hij (diagSL K a) = torusMap F (Pi.mulSingle i a * Pi.mulSingle j a⁻¹) 1 := by
  refine LinearEquiv.ext fun v => Prod.ext (funext fun d => ?_) (one_mul v.2).symm
  rw [eta_apply, pairLin_apply, torusMap_apply, coe_diagSL_inv, coe_diagSL]
  have hji := hij.symm
  rcases d with k | k
  · by_cases hki : k = i
    · subst hki
      simp [pairVec, torusScal, hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [pairVec, torusScal, hki]
      · simp [pairVec, torusScal, hki, hkj]
  · by_cases hki : k = i
    · subst hki
      simp [pairVec, torusScal, hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [pairVec, torusScal, hki]
      · simp [pairVec, torusScal, hki, hkj]

end Pair

end CFSG.LocalAnalysis.ComponentInitial.NormTail
