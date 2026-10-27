module

public import CFSG.LieType.SpinGeom.Law
public import CFSG.LieType.SpinGeom.Elem

public section

namespace CFSG.LieType.SpinGeom

open CFSG.StandardType CFSG.StandardType.Triality CFSG.LieType.D4Small
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear QuadraticMap
open scoped Matrix

section Coordinates

variable {K : Type} [Field K]

theorem coordX_elemMap (a b : Fin 4) (c : K) (v : Fin (2 * 4) → K) (k : Fin 4) :
    coordX K (elemMap K a b c v) k =
      coordX K v k + c * coordX K v b * (if a = k then 1 else 0) := by
  unfold elemMap
  rw [coordX_add, coordX_add, coordX_smul, coordX_smul, coordX_frameE, coordX_frameF]
  ring

theorem coordY_elemMap (a b : Fin 4) (c : K) (v : Fin (2 * 4) → K) (k : Fin 4) :
    coordY K (elemMap K a b c v) k =
      coordY K v k + c * coordY K v a * (if b = k then 1 else 0) := by
  unfold elemMap
  rw [coordY_add, coordY_add, coordY_smul, coordY_smul, coordY_frameE, coordY_frameF]
  ring

theorem coordX_longMap (a b c d : Fin 4) (m : K) (v : Fin (2 * 4) → K) (k : Fin 4) :
    coordX K (longMap K a b c d m v) k =
      coordX K v k + m * coordY K v b * (if a = k then 1 else 0) +
        m * coordY K v a * (if b = k then 1 else 0) := by
  unfold longMap
  rw [coordX_add, coordX_add, coordX_add, coordX_add, coordX_smul, coordX_smul, coordX_smul,
    coordX_smul, coordX_frameE, coordX_frameE, coordX_frameF, coordX_frameF]
  ring

theorem coordY_longMap (a b c d : Fin 4) (m : K) (v : Fin (2 * 4) → K) (k : Fin 4) :
    coordY K (longMap K a b c d m v) k =
      coordY K v k + m * coordX K v d * (if c = k then 1 else 0) +
        m * coordX K v c * (if d = k then 1 else 0) := by
  unfold longMap
  rw [coordY_add, coordY_add, coordY_add, coordY_add, coordY_smul, coordY_smul, coordY_smul,
    coordY_smul, coordY_frameE, coordY_frameE, coordY_frameF, coordY_frameF]
  ring

end Coordinates

section Special

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem coordX_spinElt_succ (c m : Fin 3 → K) (g : Matrix (Fin 3) (Fin 3) K)
    (v : Fin (2 * 4) → K) (l : Fin 3) :
    coordX K (spinElt K c m g v) l.succ = (g *ᵥ xvec K v + coordY K v 0 • m) l := by
  change xvec K _ l = _
  rw [xvec_spinElt]

omit [CharP K 2] in
theorem coordY_spinElt_succ (c m : Fin 3 → K) (g : Matrix (Fin 3) (Fin 3) K)
    (v : Fin (2 * 4) → K) (l : Fin 3) :
    coordY K (spinElt K c m g v) l.succ = ((g.adjugate)ᵀ *ᵥ yvec K v +
      altMat K m *ᵥ (g *ᵥ xvec K v) + coordY K v 0 • c) l := by
  change yvec K _ l = _
  rw [yvec_spinElt]

omit [CharP K 2] in
theorem spinElt_single_zero_one (j : Fin 3) (t : K) (v : Fin (2 * 4) → K) :
    spinElt K (Pi.single j t) 0 1 v = elemMap K 0 j.succ t v := by
  apply vec_ext
  · intro k
    refine Fin.cases ?_ (fun l => ?_) k
    · rw [coordX_spinElt_zero, coordX_elemMap]
      simp [xvec, single_dotProduct, mul_comm]
    · rw [coordX_spinElt_succ, coordX_elemMap, if_neg (Fin.succ_ne_zero l).symm]
      simp [xvec]
  · intro k
    refine Fin.cases ?_ (fun l => ?_) k
    · rw [coordY_spinElt_zero, coordY_elemMap, if_neg (Fin.succ_ne_zero j)]
      ring
    · rw [coordY_spinElt_succ, coordY_elemMap]
      by_cases h : l = j
      · subst h
        simp [yvec, altMat_zero, mul_comm]
      · simp [yvec, altMat_zero, Fin.succ_inj, h, Ne.symm h]

end Special

section Zeta

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem spinElt_zeta_zero (t : K) (v : Fin (2 * 4) → K) :
    spinElt K 0 (Pi.single 0 t) 1 v = longMap K 0 1 2 3 t v := by
  apply vec_ext
  · intro k
    refine Fin.cases ?_ (fun l => ?_) k
    · rw [coordX_spinElt_zero, coordX_longMap]
      simp [yvec, single_dotProduct]
    · rw [coordX_spinElt_succ, coordX_longMap]
      fin_cases l <;> simp [xvec, mul_comm]
  · intro k
    refine Fin.cases ?_ (fun l => ?_) k
    · rw [coordY_spinElt_zero, coordY_longMap]
      simp
    · rw [coordY_spinElt_succ, coordY_longMap]
      fin_cases l <;> simp [yvec, xvec, altMat, dotProduct, Fin.sum_univ_three, Matrix.vecHead,
        Matrix.vecTail, mul_comm]

omit [CharP K 2] in
theorem spinElt_zeta_one (t : K) (v : Fin (2 * 4) → K) :
    spinElt K 0 (Pi.single 1 t) 1 v = longMap K 0 2 1 3 t v := by
  apply vec_ext
  · intro k
    refine Fin.cases ?_ (fun l => ?_) k
    · rw [coordX_spinElt_zero, coordX_longMap]
      simp [yvec, single_dotProduct]
    · rw [coordX_spinElt_succ, coordX_longMap]
      fin_cases l <;> simp [xvec, mul_comm]
  · intro k
    refine Fin.cases ?_ (fun l => ?_) k
    · rw [coordY_spinElt_zero, coordY_longMap]
      simp
    · rw [coordY_spinElt_succ, coordY_longMap]
      fin_cases l <;> simp [yvec, xvec, altMat, dotProduct, Fin.sum_univ_three, Matrix.vecHead,
        Matrix.vecTail, mul_comm]

omit [CharP K 2] in
theorem spinElt_zeta_two (t : K) (v : Fin (2 * 4) → K) :
    spinElt K 0 (Pi.single 2 t) 1 v = longMap K 0 3 1 2 t v := by
  apply vec_ext
  · intro k
    refine Fin.cases ?_ (fun l => ?_) k
    · rw [coordX_spinElt_zero, coordX_longMap]
      simp [yvec, single_dotProduct]
    · rw [coordX_spinElt_succ, coordX_longMap]
      fin_cases l <;> simp [xvec, mul_comm]
  · intro k
    refine Fin.cases ?_ (fun l => ?_) k
    · rw [coordY_spinElt_zero, coordY_longMap]
      simp
    · rw [coordY_spinElt_succ, coordY_longMap]
      fin_cases l <;> simp [yvec, xvec, altMat, dotProduct, Fin.sum_univ_three, Matrix.vecHead,
        Matrix.vecTail, mul_comm]

end Zeta

section Iota

variable {K : Type} [Field K] [CharP K 2]

theorem adjugate_transvection (i j : Fin 3) (hij : i ≠ j) (t : K) :
    (Matrix.transvection i j t).adjugate = Matrix.transvection i j t := by
  have hmul : Matrix.transvection i j t * Matrix.transvection i j t = 1 := by
    rw [Matrix.transvection_mul_transvection_same i j hij, CharTwo.add_self_eq_zero,
      Matrix.transvection_zero]
  have h1 : (Matrix.transvection i j t).adjugate * Matrix.transvection i j t = 1 := by
    rw [Matrix.adjugate_mul, Matrix.det_transvection_of_ne i j hij, one_smul]
  calc (Matrix.transvection i j t).adjugate
      = (Matrix.transvection i j t).adjugate *
          (Matrix.transvection i j t * Matrix.transvection i j t) := by rw [hmul, mul_one]
    _ = ((Matrix.transvection i j t).adjugate * Matrix.transvection i j t) *
          Matrix.transvection i j t := by rw [mul_assoc]
    _ = Matrix.transvection i j t := by rw [h1, one_mul]

omit [CharP K 2] in
theorem transvection_mulVec_apply (i j : Fin 3) (t : K) (x : Fin 3 → K) (l : Fin 3) :
    (Matrix.transvection i j t *ᵥ x) l = x l + (if i = l then t * x j else 0) := by
  simp only [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.single_apply]
  by_cases h : i = l
  · subst h
    simp [mul_comm]
  · simp [h]

omit [CharP K 2] in
theorem transvection_transpose (i j : Fin 3) (t : K) :
    (Matrix.transvection i j t)ᵀ = Matrix.transvection j i t := by
  simp [Matrix.transvection, Matrix.transpose_add, Matrix.transpose_single]

theorem spinElt_transvection (i j : Fin 3) (hij : i ≠ j) (t : K) (v : Fin (2 * 4) → K) :
    spinElt K 0 0 (Matrix.transvection i j t) v = elemMap K i.succ j.succ t v := by
  apply vec_ext
  · intro k
    refine Fin.cases ?_ (fun l => ?_) k
    · rw [coordX_spinElt_zero, coordX_elemMap, if_neg (Fin.succ_ne_zero i)]
      simp
    · rw [coordX_spinElt_succ, coordX_elemMap]
      simp [transvection_mulVec_apply, xvec, Fin.succ_inj]
  · intro k
    refine Fin.cases ?_ (fun l => ?_) k
    · rw [coordY_spinElt_zero, coordY_elemMap, if_neg (Fin.succ_ne_zero j)]
      simp
    · rw [coordY_spinElt_succ, coordY_elemMap, adjugate_transvection i j hij,
        transvection_transpose]
      simp [transvection_mulVec_apply, yvec, altMat_zero, Fin.succ_inj]

end Iota

section Realize

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private abbrev Realized (f : (Fin (2 * 4) → K) → (Fin (2 * 4) → K)) : Prop :=
  ∃ h ∈ spinSeven K, ∀ v, (((h : Om8 K) : GL (Fin (2 * 4)) K) :
    Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v = f v

private theorem realized_one : Realized (K := K) (fun v : Fin (2 * 4) → K => v) :=
  ⟨1, one_mem _, fun v => by simp⟩

private theorem realized_comp {f g : (Fin (2 * 4) → K) → (Fin (2 * 4) → K)}
    (hf : Realized f) (hg : Realized g) : Realized (fun v => f (g v)) := by
  obtain ⟨h₁, hm₁, e₁⟩ := hf
  obtain ⟨h₂, hm₂, e₂⟩ := hg
  refine ⟨h₁ * h₂, mul_mem hm₁ hm₂, fun v => ?_⟩
  have : (((h₁ * h₂ : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) =
      ((h₁ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
        ((h₂ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) := rfl
  rw [this, ← Matrix.mulVec_mulVec, e₂, e₁]

private theorem realized_inv {f f' : (Fin (2 * 4) → K) → (Fin (2 * 4) → K)}
    (hf : Realized f) (hinv : ∀ v, f (f' v) = v) : Realized f' := by
  obtain ⟨h, hm, e⟩ := hf
  refine ⟨h⁻¹, inv_mem hm, fun v => ?_⟩
  have h1 : (((h⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
      ((h : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = 1 := by
    have : ((h⁻¹ * h : Om8 K) : GL (Fin (2 * 4)) K) = 1 := by rw [inv_mul_cancel]; rfl
    exact congrArg (fun u : GL (Fin (2 * 4)) K => (u : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K))
      this
  calc _ = (((h⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
        (((h : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ f' v := by
        rw [e, hinv]
    _ = f' v := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

end Realize

section RealizeIota

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem spinElt_zero_zero_comp (x y : Matrix (Fin 3) (Fin 3) K) (hx : x.det = 1)
    (v : Fin (2 * 4) → K) :
    spinElt K 0 0 x (spinElt K 0 0 y v) = spinElt K 0 0 (x * y) v := by
  rw [spinElt_comp 0 0 x hx 0 0 y v]
  simp [altMat_zero]

private theorem realized_iota (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    Realized (spinElt K 0 0 (g : Matrix (Fin 3) (Fin 3) K)) := by
  have hg : g ∈ Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin 3) K → Matrix.SpecialLinearGroup (Fin 3) K)) := by
    rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
    trivial
  refine Subgroup.closure_induction
    (p := fun (g : Matrix.SpecialLinearGroup (Fin 3) K) _ =>
      Realized (spinElt K 0 0 (g : Matrix (Fin 3) (Fin 3) K))) ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨t, rfl⟩
    have e : spinElt K 0 0 ((t.toSpecialLinearGroup : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = elemMap K t.i.succ t.j.succ t.c := by
      rw [Matrix.TransvectionStruct.toSpecialLinearGroup_coe]
      funext v
      exact spinElt_transvection t.i t.j t.hij t.c v
    rw [e]
    exact exists_mem_spinSeven_elemMap _ _ (fun h => t.hij (Fin.succ_injective _ h)) _
  · have e : spinElt K 0 0 ((1 : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        fun v => v := by
      funext v
      exact spinElt_one v
    rw [e]
    exact realized_one
  · intro x y _ _ hx hy
    have e : spinElt K 0 0 ((x * y : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) =
        fun v => spinElt K 0 0 (x : Matrix (Fin 3) (Fin 3) K)
          (spinElt K 0 0 (y : Matrix (Fin 3) (Fin 3) K) v) := by
      funext v
      rw [Matrix.SpecialLinearGroup.coe_mul, spinElt_zero_zero_comp _ _ x.2]
    rw [e]
    exact realized_comp hx hy
  · intro x _ hx
    refine realized_inv hx fun v => ?_
    rw [spinElt_zero_zero_comp _ _ x.2, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
    exact spinElt_one v

end RealizeIota

section RealizeAll

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem spinElt_one_comp (c m c' m' : Fin 3 → K) (v : Fin (2 * 4) → K) :
    spinElt K c m 1 (spinElt K c' m' 1 v) =
      spinElt K (c + c' + altMat K m' *ᵥ m) (m + m') 1 v := by
  rw [spinElt_comp c m 1 Matrix.det_one c' m' 1 v]
  simp

private theorem realized_alpha_single (j : Fin 3) (t : K) :
    Realized (spinElt K (Pi.single j t) 0 1) := by
  have e : spinElt K (Pi.single j t) 0 1 = elemMap K 0 j.succ t := by
    funext v
    exact spinElt_single_zero_one j t v
  rw [e]
  exact exists_mem_spinSeven_elemMap _ _ (Fin.succ_ne_zero j).symm _

private theorem realized_one_mul {c₁ m₁ c₂ m₂ : Fin 3 → K} (h₁ : Realized (spinElt K c₁ m₁ 1))
    (h₂ : Realized (spinElt K c₂ m₂ 1)) :
    Realized (spinElt K (c₁ + c₂ + altMat K m₂ *ᵥ m₁) (m₁ + m₂) 1) := by
  have e : spinElt K (c₁ + c₂ + altMat K m₂ *ᵥ m₁) (m₁ + m₂) 1 =
      fun v => spinElt K c₁ m₁ 1 (spinElt K c₂ m₂ 1 v) :=
    funext fun v => (spinElt_one_comp c₁ m₁ c₂ m₂ v).symm
  rw [e]
  exact realized_comp h₁ h₂

private theorem realized_alpha (c : Fin 3 → K) : Realized (spinElt K c 0 1) := by
  have hc : c = Pi.single 0 (c 0) + (Pi.single 1 (c 1) + Pi.single 2 (c 2)) := by
    ext i
    fin_cases i <;> simp
  have h := realized_one_mul (realized_alpha_single 0 (c 0))
    (realized_one_mul (realized_alpha_single 1 (c 1)) (realized_alpha_single 2 (c 2)))
  simp only [altMat_zero, Matrix.zero_mulVec, add_zero] at h
  rw [← hc] at h
  exact h

private theorem realized_zeta_single (b : Fin 3) (t : K) :
    Realized (spinElt K 0 (Pi.single b t) 1) := by
  fin_cases b
  · have e : spinElt K 0 (Pi.single 0 t) 1 = longMap K 0 1 2 3 t := by
      funext v
      exact spinElt_zeta_zero t v
    exact e ▸ exists_mem_spinSeven_longMap (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) t
  · have e : spinElt K 0 (Pi.single 1 t) 1 = longMap K 0 2 1 3 t := by
      funext v
      exact spinElt_zeta_one t v
    exact e ▸ exists_mem_spinSeven_longMap (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) t
  · have e : spinElt K 0 (Pi.single 2 t) 1 = longMap K 0 3 1 2 t := by
      funext v
      exact spinElt_zeta_two t v
    exact e ▸ exists_mem_spinSeven_longMap (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) t

private theorem realized_spinElt_one (c m : Fin 3 → K) : Realized (spinElt K c m 1) := by
  have hm : m = Pi.single 0 (m 0) + (Pi.single 1 (m 1) + Pi.single 2 (m 2)) := by
    ext i
    fin_cases i <;> simp
  obtain ⟨c₀, h₀⟩ : ∃ c₀, Realized (spinElt K c₀ m 1) := by
    have h := realized_one_mul (realized_zeta_single 0 (m 0))
      (realized_one_mul (realized_zeta_single 1 (m 1)) (realized_zeta_single 2 (m 2)))
    rw [← hm] at h
    exact ⟨_, h⟩
  have hc₀ : c₀ + c₀ = 0 := by
    ext i
    exact CharTwo.add_self_eq_zero (c₀ i)
  have e : spinElt K c m 1 = fun v => spinElt K (c + c₀) 0 1 (spinElt K c₀ m 1 v) := by
    funext v
    rw [spinElt_one_comp]
    simp [add_assoc, hc₀]
  rw [e]
  exact realized_comp (realized_alpha _) h₀

theorem exists_mem_spinSeven_spinElt (c m : Fin 3 → K) (g : Matrix (Fin 3) (Fin 3) K)
    (hg : g.det = 1) :
    ∃ h ∈ spinSeven K, ∀ v, ((h : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v =
      spinElt K c m g v := by
  have e : spinElt K c m g = fun v => spinElt K c m 1 (spinElt K 0 0 g v) := by
    funext v
    rw [spinElt_comp c m 1 Matrix.det_one 0 0 g v]
    simp [altMat_zero]
  have h := realized_comp (realized_spinElt_one c m)
    (realized_iota (⟨g, hg⟩ : Matrix.SpecialLinearGroup (Fin 3) K))
  rw [← e] at h
  exact h

end RealizeAll

end CFSG.LieType.SpinGeom
