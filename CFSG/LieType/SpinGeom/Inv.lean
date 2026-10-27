module

public import CFSG.LieType.SpinGeom.Elt

public section

namespace CFSG.LieType.SpinGeom

open CFSG.StandardType CFSG.StandardType.Triality CFSG.LieType.D4Small CFSG.LieType.Sp6Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear QuadraticMap
open scoped Matrix

section Group

variable {K : Type} [Field K] [Finite K] [CharP K 2] {C : Type} [AddCommGroup C]

omit [Finite K] [CharP K 2] in
theorem fix_inv {h : Om8 K} {v : Fin (2 * 4) → K}
    (hv : ((h : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v = v) :
    ((h⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) *ᵥ v = v := by
  have h1 : (((h⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
      ((h : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = 1 := by
    have : ((h⁻¹ * h : Om8 K) : GL (Fin (2 * 4)) K) = 1 := by rw [inv_mul_cancel]; rfl
    exact congrArg (fun u : GL (Fin (2 * 4)) K => (u : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)) this
  calc _ = (((h⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
        (((h : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v := by
        rw [hv]
    _ = v := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

private def InvAt (W : AddSubgroup ((Fin (2 * 4) → K) × C)) (A : Subgroup (GL (Fin (2 * 4)) K))
    (M : Om8 K) : Prop :=
  (∀ w ∈ W, (((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w.1,
    w.2) ∈ W) ∧
    ∀ a ∈ A, (M : GL (Fin (2 * 4)) K) * a * (M : GL (Fin (2 * 4)) K)⁻¹ ∈ A

omit [Finite K] [CharP K 2] in
private theorem InvAt.mul {W : AddSubgroup ((Fin (2 * 4) → K) × C)}
    {A : Subgroup (GL (Fin (2 * 4)) K)} {M₁ M₂ : Om8 K} (h₁ : InvAt W A M₁)
    (h₂ : InvAt W A M₂) : InvAt W A (M₁ * M₂) := by
  refine ⟨fun w hw => ?_, fun a ha => ?_⟩
  · have e : (((M₁ * M₂ : Om8 K) : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w.1 =
        ((M₁ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
          (((M₂ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w.1) := by
      rw [Matrix.mulVec_mulVec]
      rfl
    rw [e]
    exact h₁.1 (_, w.2) (h₂.1 w hw)
  · have e : ((M₁ * M₂ : Om8 K) : GL (Fin (2 * 4)) K) * a *
        ((M₁ * M₂ : Om8 K) : GL (Fin (2 * 4)) K)⁻¹ =
        (M₁ : GL (Fin (2 * 4)) K) * ((M₂ : GL (Fin (2 * 4)) K) * a *
          (M₂ : GL (Fin (2 * 4)) K)⁻¹) * (M₁ : GL (Fin (2 * 4)) K)⁻¹ := by
      simp [mul_assoc]
    rw [e]
    exact h₁.2 _ (h₂.2 a ha)

private theorem InvAt.commutator {W : AddSubgroup ((Fin (2 * 4) → K) × C)}
    {A : Subgroup (GL (Fin (2 * 4)) K)}
    (hodd : ∀ M ∈ spinSeven K, Odd (orderOf M) →
      ((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ frameE K 0 =
        frameE K 0 → InvAt W A M)
    {x t : Om8 K} (hxS : x ∈ spinSeven K)
    (hxf : ((x : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ frameE K 0 =
      frameE K 0)
    (htS : t ∈ spinSeven K)
    (htf : ((t : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ frameE K 0 =
      frameE K 0)
    (ht : Odd (orderOf t)) : InvAt W A (t * x * t⁻¹ * x⁻¹) := by
  have e : t * x * t⁻¹ * x⁻¹ = t * (x * t⁻¹ * x⁻¹) := by simp [mul_assoc]
  rw [e]
  refine InvAt.mul (hodd t htS ht htf) (hodd _ ?_ ?_ ?_)
  · exact (spinSeven K).mul_mem ((spinSeven K).mul_mem hxS ((spinSeven K).inv_mem htS))
      ((spinSeven K).inv_mem hxS)
  · have hs : SemiconjBy x t⁻¹ (x * t⁻¹ * x⁻¹) := by
      unfold SemiconjBy
      simp [mul_assoc]
    rw [← hs.orderOf_eq, orderOf_inv]
    exact ht
  · have h1 := fix_inv hxf
    have h2 := fix_inv htf
    have e2 : (((x * t⁻¹ * x⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ frameE K 0 =
        ((x : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
          ((((t⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
            ((((x⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) :
              Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ frameE K 0)) := by
      rw [mul_assoc]
      simp only [Matrix.mulVec_mulVec]
      rfl
    rw [e2, h1, h2, hxf]


private theorem InvAt.of_root {W : AddSubgroup ((Fin (2 * 4) → K) × C)}
    {A : Subgroup (GL (Fin (2 * 4)) K)}
    (hodd : ∀ M ∈ spinSeven K, Odd (orderOf M) →
      ((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ frameE K 0 =
        frameE K 0 → InvAt W A M)
    {x : K → Om8 K} (hadd : ∀ a b, x a * x b = x (a + b)) (hS : ∀ a, x a ∈ spinSeven K)
    (hf : ∀ a, ((x a : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
      frameE K 0 = frameE K 0)
    {t : Om8 K} (htS : t ∈ spinSeven K)
    (htf : ((t : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ frameE K 0 =
      frameE K 0)
    (ht : Odd (orderOf t)) {τ : K} (hτ : τ ≠ 1) (hcomm : ∀ a, t * x a = x (τ * a) * t) (s : K) :
    InvAt W A (x s) := by
  have hτ' : τ - 1 ≠ 0 := sub_ne_zero.2 hτ
  have hx0 : x 0 = 1 := by
    apply mul_left_cancel (a := x 0)
    rw [hadd, add_zero, mul_one]
  have hinv : (x (s / (τ - 1)))⁻¹ = x (-(s / (τ - 1))) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [hadd, add_neg_cancel, hx0]
  have hsa : s = τ * (s / (τ - 1)) + -(s / (τ - 1)) := by
    field_simp
    ring
  have e : x s = t * x (s / (τ - 1)) * t⁻¹ * (x (s / (τ - 1)))⁻¹ := by
    rw [hinv, hcomm, mul_inv_cancel_right, hadd, ← hsa]
  rw [e]
  exact InvAt.commutator hodd (hS _) (hf _) htS htf ht

end Group

section Torus

variable {K : Type} [Field K] [Finite K] [CharP K 2]

noncomputable def spinIota : Matrix.SpecialLinearGroup (Fin 3) K →* Om8 K where
  toFun g := sE 0 0 g
  map_one' := sE_one
  map_mul' g₁ g₂ := by
    rw [sE_mul]
    simp

def torusDiag (i j : Fin 3) (ω : K) : Fin 3 → K :=
  fun l => if l = i then ω else if l = j then 1 else ω⁻¹

omit [Finite K] [CharP K 2] in
theorem torusDiag_ne_zero (i j : Fin 3) {ω : K} (hω : ω ≠ 0) (l : Fin 3) :
    torusDiag i j ω l ≠ 0 := by
  unfold torusDiag
  split_ifs
  exacts [hω, one_ne_zero, inv_ne_zero hω]

omit [Finite K] [CharP K 2] in
theorem det_torusDiag {i j : Fin 3} (hij : i ≠ j) {ω : K} (hω : ω ≠ 0) :
    (Matrix.diagonal (torusDiag i j ω)).det = 1 := by
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | simp [torusDiag, hω]


@[expose] def torusSL (i j : Fin 3) (hij : i ≠ j) {ω : K} (hω : ω ≠ 0) :
    Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.diagonal (torusDiag i j ω), det_torusDiag hij hω⟩

omit [Finite K] [CharP K 2] in
theorem coe_torusSL {i j : Fin 3} (hij : i ≠ j) {ω : K} (hω : ω ≠ 0) :
    (torusSL i j hij hω : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal (torusDiag i j ω) := rfl

theorem orderOf_torus_dvd {i j : Fin 3} (hij : i ≠ j) {ω : K} (hω : ω ≠ 0) :
    orderOf (spinIota (torusSL i j hij hω)) ∣ Nat.card K - 1 := by
  refine (orderOf_map_dvd spinIota _).trans (orderOf_dvd_of_pow_eq_one ?_)
  have := Fintype.ofFinite K
  have h1 : torusDiag i j ω ^ (Nat.card K - 1) = 1 := by
    funext l
    rw [Pi.pow_apply, Pi.one_apply, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ (torusDiag_ne_zero i j hω l)
  have h2 : ((torusSL i j hij hω ^ (Nat.card K - 1) : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_pow, coe_torusSL, Matrix.diagonal_pow, h1]
    exact Matrix.diagonal_one
  exact Subtype.ext (h2.trans Matrix.SpecialLinearGroup.coe_one.symm)

theorem odd_card_sub_one : Odd (Nat.card K - 1) := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hq⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hq]
  have h2 : Even (2 ^ (n : ℕ)) := (Nat.even_pow.2 ⟨even_two, n.ne_zero⟩)
  obtain ⟨k, hk⟩ := h2
  have h3 : 0 < 2 ^ (n : ℕ) := pow_pos (by norm_num) _
  exact ⟨k - 1, by omega⟩

omit [Finite K] [CharP K 2] in
theorem diag_mul_transvection (d : Fin 3 → K) (i j : Fin 3) (hdj : d j ≠ 0) (s : K) :
    Matrix.diagonal d * Matrix.transvection i j s =
      Matrix.transvection i j (d i * s * (d j)⁻¹) * Matrix.diagonal d := by
  ext a b
  simp [Matrix.transvection, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply,
    Matrix.one_apply]
  split_ifs <;> simp_all
  field_simp


end Torus

section Roots

variable {K : Type} [Field K] [Finite K] [CharP K 2] {C : Type} [AddCommGroup C]

@[expose] def tvSL (i j : Fin 3) (hij : i ≠ j) (r : K) : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.transvection i j r, Matrix.det_transvection_of_ne i j hij r⟩

omit [Finite K] [CharP K 2] in
theorem coe_tvSL {i j : Fin 3} (hij : i ≠ j) (r : K) :
    (tvSL i j hij r : Matrix (Fin 3) (Fin 3) K) = Matrix.transvection i j r := rfl

noncomputable def zetaE (b : Fin 3) (r : K) : Om8 K := sE 0 (Pi.single b r) 1

noncomputable def tvE (i j : Fin 3) (hij : i ≠ j) (r : K) : Om8 K := spinIota (tvSL i j hij r)

omit [Finite K] in
theorem altMat_single_single (b : Fin 3) (r r' : K) :
    altMat K (Pi.single b r) *ᵥ (Pi.single b r' : Fin 3 → K) = 0 := by
  have e1 : (Pi.single b r : Fin 3 → K) = r • Pi.single b 1 := by
    ext i
    by_cases h : i = b <;> simp [h]
  have e2 : (Pi.single b r' : Fin 3 → K) = r' • Pi.single b 1 := by
    ext i
    by_cases h : i = b <;> simp [h]
  rw [e1, e2, altMat_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, altMat_mulVec_self, smul_zero,
    smul_zero]

theorem tvE_mul (i j : Fin 3) (hij : i ≠ j) (a b : K) :
    tvE i j hij a * tvE i j hij b = tvE i j hij (a + b) := by
  unfold tvE
  rw [← map_mul]
  congr 1
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_tvSL, coe_tvSL, coe_tvSL,
    Matrix.transvection_mul_transvection_same i j hij]

theorem zetaE_mul (b : Fin 3) (a a' : K) : zetaE b a * zetaE b a' = zetaE b (a + a') := by
  unfold zetaE
  have h1 : altMat K (((1 : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (Pi.single b a' : Fin 3 → K)) *ᵥ (Pi.single b a : Fin 3 → K) = 0 := by
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    exact altMat_single_single b a' a
  rw [sE_mul, h1]
  simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, Matrix.mulVec_zero, add_zero,
    mul_one, Pi.single_add]


theorem torus_tvE_comm {i j : Fin 3} (hij : i ≠ j) {ω : K} (hω : ω ≠ 0) (r : K) :
    spinIota (torusSL i j hij hω) * tvE i j hij r =
      tvE i j hij (ω * r) * spinIota (torusSL i j hij hω) := by
  unfold tvE
  rw [← map_mul, ← map_mul]
  congr 1
  have h := diag_mul_transvection (torusDiag i j ω) i j (torusDiag_ne_zero i j hω j) r
  have h1 : torusDiag i j ω i = ω := by simp [torusDiag]
  have h2 : torusDiag i j ω j = 1 := by simp [torusDiag, hij.symm]
  rw [h1, h2, inv_one, mul_one] at h
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_torusSL,
    coe_tvSL, coe_tvSL]
  exact h

omit [Finite K] [CharP K 2] in
theorem torus_mulVec_single {b j : Fin 3} (hbj : b ≠ j) {ω : K} (hω : ω ≠ 0) (r : K) :
    (torusSL b j hbj hω : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single b r : Fin 3 → K) =
      Pi.single b (ω * r) := by
  rw [coe_torusSL]
  ext l
  rw [Matrix.mulVec_diagonal]
  by_cases h : l = b
  · subst h
    simp [torusDiag]
  · simp [torusDiag, h]

theorem torus_zetaE_comm {b j : Fin 3} (hbj : b ≠ j) {ω : K} (hω : ω ≠ 0) (r : K) :
    spinIota (torusSL b j hbj hω) * zetaE b r =
      zetaE b (ω * r) * spinIota (torusSL b j hbj hω) := by
  unfold zetaE
  show sE 0 0 _ * sE 0 (Pi.single b r) 1 = sE 0 (Pi.single b (ω * r)) 1 * sE 0 0 _
  rw [sE_mul, sE_mul, torus_mulVec_single hbj hω]
  simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.mulVec_zero, altMat_zero,
    Matrix.zero_mulVec, add_zero, zero_add, mul_one, one_mul]


theorem zetaE_act (b : Fin 3) (r : K) (v : Fin (2 * 4) → K) :
    (((zetaE b r : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v =
      spinElt K 0 (Pi.single b r) 1 v := by
  rw [zetaE, sE_act, Matrix.SpecialLinearGroup.coe_one]

theorem tvE_act (i j : Fin 3) (hij : i ≠ j) (r : K) (v : Fin (2 * 4) → K) :
    (((tvE i j hij r : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v =
      spinElt K 0 0 (Matrix.transvection i j r) v := by
  unfold tvE
  show (((sE 0 0 (tvSL i j hij r) : Om8 K) : GL (Fin (2 * 4)) K) :
    Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v = _
  rw [sE_act, coe_tvSL]

omit [CharP K 2] in
theorem exists_ne_zero_one (hq : 4 ≤ Nat.card K) : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
  have := Fintype.ofFinite K
  classical
  have hc : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact lt_of_le_of_lt Finset.card_le_two (by omega)
  obtain ⟨ω, -, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  exact ⟨ω, fun h => hω (by simp [h]), fun h => hω (by simp [h])⟩

theorem inv_root_elements {W : AddSubgroup ((Fin (2 * 4) → K) × C)}
    {A : Subgroup (GL (Fin (2 * 4)) K)} (hq : 4 ≤ Nat.card K)
    (hodd : ∀ M ∈ spinSeven K, Odd (orderOf M) →
      ((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ frameE K 0 =
        frameE K 0 →
      (∀ w ∈ W, (((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w.1,
        w.2) ∈ W) ∧
        ∀ a ∈ A, (M : GL (Fin (2 * 4)) K) * a * (M : GL (Fin (2 * 4)) K)⁻¹ ∈ A) :
    (∀ (b : Fin 3) (r : K), ∀ w ∈ W, (spinElt K 0 (Pi.single b r) 1 w.1, w.2) ∈ W) ∧
    (∀ i j : Fin 3, i ≠ j → ∀ r : K, ∀ w ∈ W,
      (spinElt K 0 0 (Matrix.transvection i j r) w.1, w.2) ∈ W) ∧
    ∀ i j : Fin 3, i ≠ j → ∀ r : K, ∃ M : GL (Fin (2 * 4)) K,
      (∀ v, (M : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v =
        spinElt K 0 0 (Matrix.transvection i j r) v) ∧ ∀ a ∈ A, M * a * M⁻¹ ∈ A := by
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_one hq
  have hT : ∀ (i j : Fin 3) (hij : i ≠ j) (r : K), InvAt W A (tvE i j hij r) := fun i j hij r =>
    InvAt.of_root hodd (x := tvE i j hij) (tvE_mul i j hij) (fun a => sE_mem 0 0 _)
      (fun a => sE_fix 0 0 _) (t := spinIota (torusSL i j hij hω0)) (sE_mem 0 0 _)
      (sE_fix 0 0 _) (Odd.of_dvd_nat odd_card_sub_one (orderOf_torus_dvd hij hω0)) hω1
      (torus_tvE_comm hij hω0) r
  have hZ : ∀ (b : Fin 3) (r : K), InvAt W A (zetaE b r) := by
    intro b r
    obtain ⟨j, hj⟩ := exists_ne b
    exact InvAt.of_root hodd (x := zetaE b) (zetaE_mul b) (fun a => sE_mem _ _ _)
      (fun a => sE_fix _ _ _) (t := spinIota (torusSL b j hj.symm hω0)) (sE_mem 0 0 _)
      (sE_fix 0 0 _) (Odd.of_dvd_nat odd_card_sub_one (orderOf_torus_dvd hj.symm hω0)) hω1
      (torus_zetaE_comm hj.symm hω0) r
  refine ⟨fun b r w hw => ?_, fun i j hij r w hw => ?_, fun i j hij r => ?_⟩
  · rw [← zetaE_act]
    exact (hZ b r).1 w hw
  · rw [← tvE_act i j hij r]
    exact (hT i j hij r).1 w hw
  · exact ⟨((tvE i j hij r : Om8 K) : GL (Fin (2 * 4)) K), tvE_act i j hij r, (hT i j hij r).2⟩

end Roots

end CFSG.LieType.SpinGeom
