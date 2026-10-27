module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityFieldNormalForm
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticWitt

public section

namespace CFSG.GroupTheory.WeirSylow

open Module QuadraticMap
open CFSG.LieType.Universal.Spin (quadPlus quadMinus quadOdd quadPlus_apply quadMinus_apply
  quadOdd_apply)
open CFSG.ComponentClassification.UnbalancedCatalog (finite_even_regular_quadratic_normal_forms
  plusBasisIsometry minusBasisIsometry)
open CFSG.ComponentClassification.CatalogueBOddQuadratic (hyperbolicSumForm
  hyperbolicSumForm_apply exists_hyperbolic_decomposition)

variable {K : Type} [Field K]

section Binary

variable (b c : K)

@[expose] noncomputable def binForm : QuadraticForm K (K × K) :=
  LinearMap.BilinMap.toQuadraticMap
    (LinearMap.mk₂ K (fun v w : K × K => v.1 * w.1 + b * v.1 * w.2 + c * v.2 * w.2)
      (fun v v' w => by simp only [Prod.fst_add, Prod.snd_add]; ring)
      (fun r v w => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
      (fun v w w' => by simp only [Prod.fst_add, Prod.snd_add]; ring)
      (fun r v w => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring))

theorem binForm_apply (v : K × K) : binForm b c v = v.1 ^ 2 + b * v.1 * v.2 + c * v.2 ^ 2 := by
  simp only [binForm, LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.mk₂_apply]
  ring

variable {b c}

theorem binForm_eq_zero (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {v : K × K}
    (hv : binForm b c v = 0) : v = 0 := by
  rw [binForm_apply] at hv
  obtain ⟨h1, h2⟩ := CFSG.ClassicalGroups.Orthogonal.binary_eq_zero_of_irreducible hirr hv
  exact Prod.ext h1 h2

theorem noRoot_quadraticAlgebra (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∀ r : K, r ^ 2 ≠ -c + b * r := fun r h => hirr (-r) (by linear_combination h)

variable (b c) in
@[expose] noncomputable def qaEquiv : QuadraticAlgebra K (-c) b ≃ₗ[K] K × K where
  toFun z := (z.re, z.im)
  invFun v := ⟨v.1, v.2⟩
  left_inv z := rfl
  right_inv v := rfl
  map_add' z w := by simp
  map_smul' r z := by simp

theorem binForm_qaEquiv (z : QuadraticAlgebra K (-c) b) :
    binForm b c (qaEquiv b c z) = QuadraticAlgebra.norm z := by
  rw [binForm_apply, QuadraticAlgebra.norm_def]
  change z.re ^ 2 + b * z.re * z.im + c * z.im ^ 2 = _
  ring

theorem algebra_norm_eq (z : QuadraticAlgebra K (-c) b) :
    Algebra.norm K z = QuadraticAlgebra.norm z := by
  rw [Algebra.norm_apply, ← QuadraticAlgebra.det_toLinearMap_eq_norm]
  rfl

variable [Finite K]

theorem finite_quadraticAlgebra : Finite (QuadraticAlgebra K (-c) b) :=
  Finite.of_equiv _ (qaEquiv b c).toEquiv.symm

theorem exists_binForm_eq (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (d : K) :
    ∃ v : K × K, binForm b c v = d := by
  have : Fact (∀ r : K, r ^ 2 ≠ -c + b * r) := ⟨noRoot_quadraticAlgebra hirr⟩
  have := finite_quadraticAlgebra (b := b) (c := c)
  obtain ⟨z, hz⟩ := FiniteField.norm_surjective K (QuadraticAlgebra K (-c) b) d
  exact ⟨qaEquiv b c z, by rw [binForm_qaEquiv, ← algebra_norm_eq, hz]⟩

theorem exists_binForm_similitude (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {d : K}
    (hd : d ≠ 0) : ∃ φ : (K × K) ≃ₗ[K] (K × K), ∀ v, binForm b c (φ v) = d * binForm b c v := by
  have : Fact (∀ r : K, r ^ 2 ≠ -c + b * r) := ⟨noRoot_quadraticAlgebra hirr⟩
  have := finite_quadraticAlgebra (b := b) (c := c)
  obtain ⟨w, hw⟩ := FiniteField.norm_surjective K (QuadraticAlgebra K (-c) b) d
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [Algebra.norm_zero] at hw
    exact hd hw.symm
  let m := DistribMulAction.toModuleAut K (QuadraticAlgebra K (-c) b) (Units.mk0 w hw0)
  refine ⟨(qaEquiv b c).symm.trans (m.trans (qaEquiv b c)), fun v => ?_⟩
  change binForm b c (qaEquiv b c (w * (qaEquiv b c).symm v)) = _
  rw [binForm_qaEquiv, map_mul, ← algebra_norm_eq, hw, ← binForm_qaEquiv,
    LinearEquiv.apply_symm_apply]

theorem binForm_isometry {b' c' : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hirr' : ∀ s : K, s ^ 2 + b' * s + c' ≠ 0) :
    Nonempty ((binForm b' c').IsometryEquiv (binForm b c)) := by
  have : Fact (∀ r : K, r ^ 2 ≠ -c + b * r) := ⟨noRoot_quadraticAlgebra hirr⟩
  have : Fact (∀ r : K, r ^ 2 ≠ -c' + b' * r) := ⟨noRoot_quadraticAlgebra hirr'⟩
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  let e₁ := FiniteField.algEquivExtension K (ringChar K) 2 (QuadraticAlgebra K (-c) b)
    (QuadraticAlgebra.finrank_eq_two _ _)
  let e₂ := FiniteField.algEquivExtension K (ringChar K) 2 (QuadraticAlgebra K (-c') b')
    (QuadraticAlgebra.finrank_eq_two _ _)
  let e : QuadraticAlgebra K (-c') b' ≃ₐ[K] QuadraticAlgebra K (-c) b := e₂.trans e₁.symm
  refine ⟨⟨(qaEquiv b' c').symm.trans (e.toLinearEquiv.trans (qaEquiv b c)), fun v => ?_⟩⟩
  change binForm b c (qaEquiv b c (e ((qaEquiv b' c').symm v))) = _
  rw [binForm_qaEquiv]
  refine (QuadraticAlgebra.norm_algHom e.toAlgHom e.injective _).trans ?_
  rw [← binForm_qaEquiv, LinearEquiv.apply_symm_apply]

end Binary

section Models

variable (K) in
@[expose] noncomputable def lineForm (d : K) : QuadraticForm K K :=
  d • QuadraticMap.sq

theorem lineForm_apply (d x : K) : lineForm K d x = d * x ^ 2 := by
  rw [lineForm, smul_apply, QuadraticMap.sq_apply, smul_eq_mul, _root_.sq]

variable (K) in
@[expose] noncomputable def minusSplitEquiv (n : ℕ) :
    (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) ≃ₗ[K] (Fin (n - 1) ⊕ Fin (n - 1) → K) × (K × K) where
  toFun v := (Sum.elim (fun i => v (.inl i)) (fun i => v (.inr (.inl i))),
    (v (.inr (.inr 0)), v (.inr (.inr 1))))
  invFun x := Sum.elim (fun i => x.1 (.inl i))
    (Sum.elim (fun i => x.1 (.inr i)) ![x.2.1, x.2.2])
  left_inv v := by
    funext j
    rcases j with i | i | k
    · rfl
    · rfl
    · fin_cases k <;> rfl
  right_inv x := by
    obtain ⟨x, y⟩ := x
    refine Prod.ext ?_ rfl
    funext j
    rcases j with i | i <;> rfl
  map_add' v w := by
    refine Prod.ext ?_ rfl
    funext j
    rcases j with i | i <;> rfl
  map_smul' r v := by
    refine Prod.ext ?_ rfl
    funext j
    rcases j with i | i <;> rfl

@[expose] noncomputable def quadMinusIsometry (n : ℕ) (b c : K) :
    (quadMinus n K b c).IsometryEquiv ((quadPlus (n - 1) K).prod (binForm b c)) where
  toLinearEquiv := minusSplitEquiv K n
  map_app' v := by
    change quadPlus (n - 1) K (Sum.elim (fun i => v (.inl i)) (fun i => v (.inr (.inl i)))) +
      binForm b c (v (.inr (.inr 0)), v (.inr (.inr 1))) = _
    rw [quadPlus_apply, binForm_apply, quadMinus_apply]
    simp only [Sum.elim_inl, Sum.elim_inr]
    ring

variable (K) in
@[expose] noncomputable def oddSplitEquiv (n : ℕ) :
    (Fin n ⊕ Fin n ⊕ Unit → K) ≃ₗ[K] (Fin n ⊕ Fin n → K) × K where
  toFun v := (Sum.elim (fun i => v (.inl i)) (fun i => v (.inr (.inl i))), v (.inr (.inr ())))
  invFun x := Sum.elim (fun i => x.1 (.inl i)) (Sum.elim (fun i => x.1 (.inr i)) fun _ => x.2)
  left_inv v := by
    funext j
    rcases j with i | i | ⟨⟩ <;> rfl
  right_inv x := by
    obtain ⟨x, y⟩ := x
    refine Prod.ext ?_ rfl
    funext j
    rcases j with i | i <;> rfl
  map_add' v w := by
    refine Prod.ext ?_ rfl
    funext j
    rcases j with i | i <;> rfl
  map_smul' r v := by
    refine Prod.ext ?_ rfl
    funext j
    rcases j with i | i <;> rfl

@[expose] noncomputable def quadOddIsometry (n : ℕ) :
    (quadOdd n K).IsometryEquiv ((quadPlus n K).prod (lineForm K 1)) where
  toLinearEquiv := oddSplitEquiv K n
  map_app' v := by
    change quadPlus n K (Sum.elim (fun i => v (.inl i)) (fun i => v (.inr (.inl i)))) +
      lineForm K 1 (v (.inr (.inr ()))) = _
    rw [quadPlus_apply, lineForm_apply, quadOdd_apply, one_mul]
    simp only [Sum.elim_inl, Sum.elim_inr]

variable (K) in
@[expose] noncomputable def hypCoordEquiv (m : ℕ) : (Fin m → K × K) ≃ₗ[K] (Fin m ⊕ Fin m → K) where
  toFun x := Sum.elim (fun i => (x i).1) (fun i => (x i).2)
  invFun v i := (v (.inl i), v (.inr i))
  left_inv x := rfl
  right_inv v := by
    funext j
    rcases j with i | i <;> rfl
  map_add' x y := by
    funext j
    rcases j with i | i <;> rfl
  map_smul' r x := by
    funext j
    rcases j with i | i <;> rfl

@[expose] noncomputable def hyperbolicSumIsometry (m : ℕ) :
    (hyperbolicSumForm K m).IsometryEquiv
      (quadPlus m K) where
  toLinearEquiv := hypCoordEquiv K m
  map_app' x := by
    rw [hyperbolicSumForm_apply,
      quadPlus_apply]
    rfl

end Models

section PlusType

variable {V : Type} [AddCommGroup V] [Module K V]

@[expose] def IsPlusType (Q : QuadraticForm K V) : Prop :=
  ∃ W : Submodule K V, 2 * finrank K W = finrank K V ∧ ∀ x ∈ W, Q x = 0

theorem IsPlusType.of_isometryEquiv {V' : Type} [AddCommGroup V'] [Module K V']
    {Q : QuadraticForm K V} {Q' : QuadraticForm K V'} (e : Q.IsometryEquiv Q')
    (h : IsPlusType Q) : IsPlusType Q' := by
  obtain ⟨W, hW, hWs⟩ := h
  refine ⟨W.map e.toLinearEquiv.toLinearMap, ?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq, hW, e.toLinearEquiv.finrank_eq]
  · rintro _ ⟨x, hx, rfl⟩
    change Q' (e x) = 0
    rw [e.map_app]
    exact hWs x hx

theorem isPlusType_congr {V' : Type} [AddCommGroup V'] [Module K V']
    {Q : QuadraticForm K V} {Q' : QuadraticForm K V'} (e : Q.IsometryEquiv Q') :
    IsPlusType Q ↔ IsPlusType Q' :=
  ⟨IsPlusType.of_isometryEquiv e, IsPlusType.of_isometryEquiv e.symm⟩

theorem IsPlusType.prod {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V]
    [FiniteDimensional K V'] {Q : QuadraticForm K V} {Q' : QuadraticForm K V'}
    (h : IsPlusType Q) (h' : IsPlusType Q') : IsPlusType (Q.prod Q') := by
  obtain ⟨W, hW, hWs⟩ := h
  obtain ⟨W', hW', hWs'⟩ := h'
  let j := LinearMap.prodMap W.subtype W'.subtype
  have hj : Function.Injective j := fun x y hxy => Prod.ext
    (Subtype.ext (congrArg Prod.fst hxy)) (Subtype.ext (congrArg Prod.snd hxy))
  refine ⟨LinearMap.range j, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hj, Module.finrank_prod, Module.finrank_prod]
    omega
  · rintro _ ⟨x, rfl⟩
    change Q x.1 + Q' x.2 = 0
    rw [hWs _ x.1.2, hWs' _ x.2.2, add_zero]

theorem isPlusType_of_subsingleton [Subsingleton V] (Q : QuadraticForm K V) : IsPlusType Q :=
  ⟨⊥, by rw [finrank_bot, finrank_zero_of_subsingleton], fun x hx => by
    rw [(Submodule.mem_bot K).1 hx, QuadraticMap.map_zero]⟩

variable (K) in
@[expose] def plusHalf (m : ℕ) : (Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K) where
  toFun y := Sum.elim y 0
  map_add' _ _ := by
    funext j
    rcases j with i | i <;> simp
  map_smul' _ _ := by
    funext j
    rcases j with i | i <;> simp

theorem plusHalf_injective (m : ℕ) : Function.Injective (plusHalf K m) := fun _ _ h =>
  funext fun i => congrFun h (.inl i)

variable (K) in
theorem isPlusType_quadPlus (m : ℕ) : IsPlusType (quadPlus m K) := by
  refine ⟨LinearMap.range (plusHalf K m), ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj (plusHalf_injective m), Module.finrank_fin_fun,
      Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  · rintro _ ⟨y, rfl⟩
    rw [quadPlus_apply]
    simp [plusHalf]

theorem nonempty_isometry_quadPlus [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {n : ℕ} (hdim : finrank K V = 2 * n)
    (h : IsPlusType Q) : Nonempty (Q.IsometryEquiv (quadPlus n K)) := by
  obtain ⟨W, hW, hWs⟩ := h
  obtain ⟨b, -, -, -, -, hb⟩ :=
    (CFSG.LocalAnalysis.ComponentInitial.orthogonal_geometry_split_Witt_flags hQ hdim
      ⟨W, by omega, hWs⟩).1 0 (Nat.zero_le n) (fun _ => ⊥) (fun i hi => by
        rw [finrank_bot]
        omega) (fun i hi => absurd hi (Nat.not_lt_zero i))
      (fun x hx => by rw [(Submodule.mem_bot K).1 hx, QuadraticMap.map_zero])
  exact ⟨plusBasisIsometry b hb⟩

end PlusType

section Nondegenerate

variable {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

theorem nondegenerate_polarBilin_prod {Q : QuadraticForm K V} {Q' : QuadraticForm K V'}
    (hQ : (polarBilin Q).Nondegenerate) (hQ' : (polarBilin Q').Nondegenerate) :
    (polarBilin (Q.prod Q')).Nondegenerate := by
  refine CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun x hx => ?_
  refine Prod.ext (hQ.1 x.1 fun y => ?_) (hQ'.1 x.2 fun y => ?_)
  · have := hx (y, 0)
    rw [polar_prod, polar_zero_right, add_zero] at this
    exact this
  · have := hx (0, y)
    rw [polar_prod, polar_zero_right, zero_add] at this
    exact this

theorem nondegenerate_polarBilin_of_isometryEquiv {Q : QuadraticForm K V}
    {Q' : QuadraticForm K V'} (e : Q.IsometryEquiv Q') (hQ : (polarBilin Q).Nondegenerate) :
    (polarBilin Q').Nondegenerate := by
  refine CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun x hx => ?_
  have key : ∀ a b, polar Q a b = polar Q' (e a) (e b) := fun a b => by
    simp only [polar, ← map_add, e.map_app]
  have h : e.symm x = 0 := hQ.1 _ fun y => by
    rw [polarBilin_apply_apply, key, e.apply_symm_apply]
    exact hx (e y)
  simpa using congrArg e h

end Nondegenerate

section NormalForms

variable [Finite K]

theorem exists_binForm_isometryEquiv {U : Type} [AddCommGroup U] [Module K U]
    (hU : finrank K U = 2) (A : QuadraticForm K U) (hA : ∀ x, A x = 0 → x = 0) :
    ∃ b c : K, (∀ s, s ^ 2 + b * s + c ≠ 0) ∧ Nonempty ((binForm b c).IsometryEquiv A) := by
  have : FiniteDimensional K U := Module.finite_of_finrank_eq_succ hU
  let x := Module.finBasisOfFinrankEq K U hU
  set α := A (x 0)
  have hα : α ≠ 0 := fun h => x.ne_zero 0 (hA _ h)
  have hval : ∀ s t : K, A (s • x 0 + t • x 1) =
      α * (s ^ 2 + (polar A (x 0) (x 1) / α) * s * t + (A (x 1) / α) * t ^ 2) := by
    intro s t
    rw [QuadraticMap.map_add A, QuadraticMap.map_smul, QuadraticMap.map_smul,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right]
    simp only [smul_eq_mul]
    field_simp
    ring
  have hli : ∀ s t : K, s • x 0 + t • x 1 = 0 → s = 0 ∧ t = 0 := by
    intro s t h
    have := (Fintype.linearIndependent_iff.1 x.linearIndependent) ![s, t]
      (by simpa [Fin.sum_univ_two] using h)
    exact ⟨this 0, this 1⟩
  have hirr₀ : ∀ r : K, r ^ 2 + polar A (x 0) (x 1) / α * r + A (x 1) / α ≠ 0 := by
    intro r h
    have h1 := hval r 1
    rw [one_pow, mul_one, mul_one, h, mul_zero] at h1
    exact one_ne_zero (hli r 1 (hA _ h1)).2
  obtain ⟨v₀, hv₀⟩ := exists_binForm_eq hirr₀ α⁻¹
  set u := v₀.1 • x 0 + v₀.2 • x 1
  have hu : A u = 1 := by
    rw [hval, ← binForm_apply, hv₀, mul_inv_cancel₀ hα]
  have hu0 : u ≠ 0 := fun h => by rw [h, QuadraticMap.map_zero] at hu; exact zero_ne_one hu
  obtain ⟨v, hv⟩ : ∃ v : U, ∀ s t : K, s • u + t • v = 0 → s = 0 ∧ t = 0 := by
    by_cases ht : v₀.2 = 0
    · refine ⟨x 1, fun s t h => ?_⟩
      have h' : (s * v₀.1) • x 0 + (s * v₀.2 + t) • x 1 = 0 := by
        rw [← h]
        simp only [u, smul_add, smul_smul, add_smul]
        abel
      obtain ⟨h1, h2⟩ := hli _ _ h'
      have hs1 : v₀.1 ≠ 0 := by
        intro h0
        apply hu0
        simp [u, h0, ht]
      have hs : s = 0 := (mul_eq_zero.1 h1).resolve_right hs1
      refine ⟨hs, ?_⟩
      rw [hs, zero_mul, zero_add] at h2
      exact h2
    · refine ⟨x 0, fun s t h => ?_⟩
      have h' : (s * v₀.1 + t) • x 0 + (s * v₀.2) • x 1 = 0 := by
        rw [← h]
        simp only [u, smul_add, smul_smul, add_smul]
        abel
      obtain ⟨h1, h2⟩ := hli _ _ h'
      have hs : s = 0 := (mul_eq_zero.1 h2).resolve_right ht
      refine ⟨hs, ?_⟩
      rw [hs, zero_mul, zero_add] at h1
      exact h1
  let φ : (K × K) →ₗ[K] U := (LinearMap.fst K K K).smulRight u + (LinearMap.snd K K K).smulRight v
  have hφ : ∀ p : K × K, φ p = p.1 • u + p.2 • v := fun p => rfl
  have hval' : ∀ p : K × K, A (φ p) = binForm (polar A u v) (A v) p := by
    intro p
    rw [hφ, QuadraticMap.map_add A, QuadraticMap.map_smul, QuadraticMap.map_smul,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hu, binForm_apply]
    simp only [smul_eq_mul]
    ring
  have hirr : ∀ r : K, r ^ 2 + polar A u v * r + A v ≠ 0 := by
    intro r h
    have h1 := hval' (r, 1)
    rw [binForm_apply] at h1
    simp only [one_pow, mul_one] at h1
    rw [h] at h1
    exact one_ne_zero (hv r 1 (hA _ (by rw [← h1]; rfl))).2
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    obtain ⟨h1, h2⟩ := hv p.1 p.2 (by rw [← hφ]; exact hp)
    exact Prod.ext h1 h2
  have hbij : Function.Bijective φ :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [hU, Module.finrank_prod, Module.finrank_self])).1 hinj⟩
  exact ⟨polar A u v, A v, hirr, ⟨⟨LinearEquiv.ofBijective φ hbij, fun p => hval' p⟩⟩⟩

theorem odd_card_of_ringChar_ne_two (h2 : ringChar K ≠ 2) : Odd (Nat.card K) := by
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Nat.odd_iff]
  have h := mt FiniteField.even_card_iff_char_two.2 h2
  omega

@[expose] def IsometryEquiv.smulForm {V V' : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] {Q : QuadraticForm K V} {Q' : QuadraticForm K V'} (d : K)
    (e : Q.IsometryEquiv Q') : (d • Q).IsometryEquiv (d • Q') :=
  ⟨e.toLinearEquiv, fun x => by
    change d • Q' (e x) = d • Q x
    rw [e.map_app]⟩

theorem exists_isometry_quadPlus_or_quadMinus {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate) {n : ℕ}
    (hn : 1 ≤ n) (hdim : finrank K V = 2 * n) :
    Nonempty (Q.IsometryEquiv (quadPlus n K)) ∨
      ∃ b c : K, (∀ s, s ^ 2 + b * s + c ≠ 0) ∧ Nonempty (Q.IsometryEquiv (quadMinus n K b c)) := by
  by_cases h2 : ringChar K = 2
  · have : CharP K 2 := ringChar.of_eq h2
    rcases (finite_even_regular_quadratic_normal_forms
      Q hQ).2.2.1 n hn hdim with ⟨b, hb⟩ | ⟨β, γ, -, hroot, b, hb⟩
    · exact Or.inl ⟨plusBasisIsometry b hb⟩
    · exact Or.inr ⟨β, γ, hroot,
        ⟨minusBasisIsometry b hb⟩⟩
  · obtain ⟨m, k, w, hk, hani, hrank, ⟨e⟩⟩ :=
      exists_hyperbolic_decomposition
        (odd_card_of_ringChar_ne_two h2) Q hQ
    obtain rfl | rfl : k = 0 ∨ k = 2 := by omega
    · obtain rfl : n = m := by omega
      refine Or.inl ⟨e.trans ((QuadraticMap.IsometryEquiv.prodComm _ _).trans
        ((QuadraticMap.IsometryEquiv.uniqueProd _ _).trans (hyperbolicSumIsometry n)))⟩
    · obtain rfl : n = m + 1 := by omega
      obtain ⟨b, c, hirr, ⟨ι⟩⟩ := exists_binForm_isometryEquiv (by simp)
        (QuadraticMap.weightedSumSquares K w) fun x hx => hani x hx
      exact Or.inr ⟨b, c, hirr, ⟨e.trans (((hyperbolicSumIsometry m).prod ι.symm).trans
        (quadMinusIsometry (m + 1) b c).symm)⟩⟩

theorem exists_smul_isometry_quadOdd {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h2 : ringChar K ≠ 2) (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate) {n : ℕ} (hdim : finrank K V = 2 * n + 1) :
    ∃ d : K, d ≠ 0 ∧ Nonempty ((d • Q).IsometryEquiv (quadOdd n K)) := by
  obtain ⟨m, k, w, hk, -, hrank, ⟨e⟩⟩ :=
    exists_hyperbolic_decomposition
      (odd_card_of_ringChar_ne_two h2) Q hQ
  obtain rfl : k = 1 := by omega
  obtain rfl : n = m := by omega
  set d : K := ((w 0 : Kˣ) : K)⁻¹ with hd
  have hd0 : d ≠ 0 := inv_ne_zero (w 0).ne_zero
  let s₁ : (Fin n → K × K) ≃ₗ[K] (Fin n → K × K) :=
    LinearEquiv.piCongrRight fun _ =>
      (LinearEquiv.smulOfUnit (Units.mk0 d hd0)).prodCongr (LinearEquiv.refl K K)
  let i₁ : (d • hyperbolicSumForm K n).IsometryEquiv
      (hyperbolicSumForm K n) :=
    ⟨s₁, fun x => by
      change hyperbolicSumForm K n
        (fun i => (d • (x i).1, (x i).2)) = d • _
      rw [hyperbolicSumForm_apply,
        hyperbolicSumForm_apply,
        smul_eq_mul, Finset.mul_sum]
      simp only [smul_eq_mul, mul_assoc]⟩
  let i₂ : (d • QuadraticMap.weightedSumSquares K w).IsometryEquiv (lineForm K 1) :=
    ⟨LinearEquiv.funUnique (Fin 1) K K, fun x => by
      change lineForm K 1 (x default) = d • QuadraticMap.weightedSumSquares K w x
      rw [lineForm_apply, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_one,
        smul_eq_mul, Units.smul_def, smul_eq_mul, hd, ← mul_assoc, inv_mul_cancel₀ (w 0).ne_zero,
        one_mul, one_mul, _root_.sq]
      rfl⟩
  refine ⟨d, hd0, ⟨(IsometryEquiv.smulForm d e).trans ?_⟩⟩
  rw [QuadraticMap.smul_prod]
  exact (i₁.prod i₂).trans (((hyperbolicSumIsometry n).prod
    (QuadraticMap.IsometryEquiv.refl _)).trans (quadOddIsometry n).symm)

omit [Finite K] in
theorem orthogonalGroup_smul {V : Type} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
    {d : K} (hd : d ≠ 0) :
    TauCeti.QuadraticMap.orthogonalGroup (d • Q) = TauCeti.QuadraticMap.orthogonalGroup Q := by
  ext g
  simp only [TauCeti.QuadraticMap.mem_orthogonalGroup_iff, smul_apply, smul_eq_mul]
  exact forall_congr' fun x => mul_right_inj' hd

end NormalForms

end CFSG.GroupTheory.WeirSylow
