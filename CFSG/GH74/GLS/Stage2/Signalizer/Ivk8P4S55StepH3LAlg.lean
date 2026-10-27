module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3L

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification

variable {K : Type} [Field K] {n : ℕ}

@[expose] def elat (W : Submodule K (Fin n → K)) : Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := elationGenerators W
  one_mem' := one_mem_elationGenerators W
  mul_mem' := by
    intro g h hg hh
    obtain ⟨hg1, hg2⟩ := mem_elationGenerators.mp hg
    obtain ⟨hh1, hh2⟩ := mem_elationGenerators.mp hh
    have key : ∀ v, ((g : Matrix (Fin n) (Fin n) K) * (h : Matrix (Fin n) (Fin n) K) - 1) *ᵥ v
        = ((g : Matrix (Fin n) (Fin n) K) - 1) *ᵥ v +
          ((h : Matrix (Fin n) (Fin n) K) - 1) *ᵥ v := by
      intro v
      have e : (g : Matrix (Fin n) (Fin n) K) * (h : Matrix (Fin n) (Fin n) K) - 1 =
          ((g : Matrix (Fin n) (Fin n) K) - 1) * ((h : Matrix (Fin n) (Fin n) K) - 1) +
            ((g : Matrix (Fin n) (Fin n) K) - 1) + ((h : Matrix (Fin n) (Fin n) K) - 1) := by
        noncomm_ring
      rw [e, Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hg2 _ (hh1 v),
        zero_add]
    rw [mem_elationGenerators]
    change (∀ v, ((g : Matrix (Fin n) (Fin n) K) * (h : Matrix (Fin n) (Fin n) K) - 1) *ᵥ v ∈ W) ∧
      ∀ w ∈ W, ((g : Matrix (Fin n) (Fin n) K) * (h : Matrix (Fin n) (Fin n) K) - 1) *ᵥ w = 0
    exact ⟨fun v => by rw [key]; exact W.add_mem (hg1 v) (hh1 v),
      fun w hw => by rw [key, hg2 w hw, hh2 w hw, add_zero]⟩
  inv_mem' := by
    intro g hg
    obtain ⟨hg1, hg2⟩ := mem_elationGenerators.mp hg
    set M : Matrix (Fin n) (Fin n) K :=
      ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
    have hMg : M * (g : Matrix (Fin n) (Fin n) K) = 1 := by
      have h := congrArg (fun x : SpecialLinearGroup (Fin n) K => (x : Matrix (Fin n) (Fin n) K))
        (inv_mul_cancel g)
      exact h
    have hgw : ∀ w ∈ W, (g : Matrix (Fin n) (Fin n) K) *ᵥ w = w := fun w hw => by
      have h := hg2 w hw
      rwa [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    have hMw : ∀ w ∈ W, M *ᵥ w = w := fun w hw => by
      conv_lhs => rw [← hgw w hw]
      rw [Matrix.mulVec_mulVec, hMg, Matrix.one_mulVec]
    have key : ∀ v, (M - 1) *ᵥ v = -(((g : Matrix (Fin n) (Fin n) K) - 1) *ᵥ v) := by
      intro v
      have hv : (g : Matrix (Fin n) (Fin n) K) *ᵥ v -
          ((g : Matrix (Fin n) (Fin n) K) - 1) *ᵥ v = v := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        abel
      have h1 : M *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) = v := by
        rw [Matrix.mulVec_mulVec, hMg, Matrix.one_mulVec]
      have h2 : M *ᵥ v = v - ((g : Matrix (Fin n) (Fin n) K) - 1) *ᵥ v := by
        have h3 : M *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ v -
            ((g : Matrix (Fin n) (Fin n) K) - 1) *ᵥ v) =
              v - ((g : Matrix (Fin n) (Fin n) K) - 1) *ᵥ v := by
          rw [Matrix.mulVec_sub, h1, hMw _ (hg1 v)]
        rwa [hv] at h3
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, h2]
      abel
    rw [mem_elationGenerators]
    change (∀ v, (M - 1) *ᵥ v ∈ W) ∧ ∀ w ∈ W, (M - 1) *ᵥ w = 0
    exact ⟨fun v => by rw [key]; exact W.neg_mem (hg1 v),
      fun w hw => by rw [key, hg2 w hw, neg_zero]⟩

theorem mem_elat {W : Submodule K (Fin n → K)} {g : SpecialLinearGroup (Fin n) K} :
    g ∈ elat W ↔ (∀ v, ((g : Matrix (Fin n) (Fin n) K) - 1) *ᵥ v ∈ W) ∧
      ∀ w ∈ W, ((g : Matrix (Fin n) (Fin n) K) - 1) *ᵥ w = 0 :=
  mem_elationGenerators

theorem one_add_pow_of_mul_self {N : Matrix (Fin n) (Fin n) K} (hN : N * N = 0) (k : ℕ) :
    (1 + N) ^ k = 1 + (k : K) • N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_assoc, hN,
      smul_zero, add_zero, Nat.cast_succ, add_smul, one_smul]
    abel

theorem pow_char_eq_one_of_mem_elat {r : ℕ} [CharP K r] {W : Submodule K (Fin n → K)}
    {g : SpecialLinearGroup (Fin n) K} (hg : g ∈ elat W) : g ^ r = 1 := by
  set N : Matrix (Fin n) (Fin n) K := (g : Matrix (Fin n) (Fin n) K) - 1 with hN
  have hNN : N * N = 0 := by
    have h : ∀ v, (N * N) *ᵥ v = 0 := fun v => by
      rw [← Matrix.mulVec_mulVec]
      exact (mem_elat.mp hg).2 _ ((mem_elat.mp hg).1 v)
    exact Matrix.toLin'.injective (LinearMap.ext fun v => by
      rw [Matrix.toLin'_apply, h, map_zero, LinearMap.zero_apply])
  apply Subtype.ext
  change (g : Matrix (Fin n) (Fin n) K) ^ r = 1
  have hg' : (g : Matrix (Fin n) (Fin n) K) = 1 + N := by rw [hN]; abel
  rw [hg', one_add_pow_of_mul_self hNN, CharP.cast_eq_zero, zero_smul, add_zero]

theorem isPGroup_elat {r : ℕ} [CharP K r] (W : Submodule K (Fin n → K)) :
    IsPGroup r ↥(elat W) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  exact pow_char_eq_one_of_mem_elat g.2

theorem slConjugation_mem_elat {W : Submodule K (Fin n → K)} {A : GL (Fin n) K}
    (hA : ∀ w ∈ W, (A : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W)
    (hA' : ∀ w ∈ W, ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W)
    {g : SpecialLinearGroup (Fin n) K} (hg : g ∈ elat W) :
    CatalogueBHigherLinearAction.slConjugation n K A g ∈ elat W := by
  obtain ⟨hg1, hg2⟩ := mem_elat.mp hg
  have e : (A : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) *
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1 =
        (A : Matrix (Fin n) (Fin n) K) * ((g : Matrix (Fin n) (Fin n) K) - 1) *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.mul_inv]
  rw [mem_elat, coe_slConjugation, e]
  refine ⟨fun v => ?_, fun w hw => ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hA _ (hg1 _)
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg2 _ (hA' w hw), Matrix.mulVec_zero]

theorem conjAut_mem_map_elat {W : Submodule K (Fin n → K)} {A : GL (Fin n) K}
    (hA : ∀ w ∈ W, (A : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W)
    (hA' : ∀ w ∈ W, ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W)
    {x : projectiveSL n K} (hx : x ∈ (elat W).map (proj n K)) :
    conjAut n K A x ∈ (elat W).map (proj n K) := by
  obtain ⟨g, hg, rfl⟩ := hx
  rw [conjAut_proj]
  exact Subgroup.mem_map_of_mem _ (slConjugation_mem_elat hA hA' hg)

theorem map_elat_ne_bot {W : Submodule K (Fin n → K)} (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤) :
    (elat W).map (proj n K) ≠ ⊥ := by
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨φ, hφ0, hφW⟩ := W.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hWt)
  set u : Fin n → K := fun j => φ (Pi.single j 1) with hu
  have hφv : ∀ v : Fin n → K, u ⬝ᵥ v = φ v := by
    intro v
    conv_rhs => rw [pi_eq_sum_univ v]
    simp only [map_sum, map_smul, smul_eq_mul, dotProduct, hu]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    congr 1
    congr 1
    funext i
    simp [Pi.single_apply, eq_comm]
  have hφw : φ w = 0 := hφW hwW
  set T : Matrix (Fin n) (Fin n) K := 1 + vecMulVec w u with hT
  have hTdet : T.det = 1 := by
    rw [hT, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, hφv, hφw, add_zero]
  have hTv : ∀ v, (T - 1) *ᵥ v = φ v • w := by
    intro v
    rw [hT, add_sub_cancel_left, vecMulVec_mulVec, hφv, op_smul_eq_smul]
  set t : SpecialLinearGroup (Fin n) K := ⟨T, hTdet⟩ with ht
  have htmem : t ∈ elat W := by
    rw [mem_elat]
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · change (T - 1) *ᵥ v ∈ W
      rw [hTv]
      exact W.smul_mem _ hwW
    · change (T - 1) *ᵥ v = 0
      rw [hTv, hφW hv, zero_smul]
  intro hbot
  have h1 : proj n K t = 1 := by
    have : proj n K t ∈ (elat W).map (proj n K) := Subgroup.mem_map_of_mem _ htmem
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  obtain ⟨c, -, hc⟩ := proj_eq_one_iff.mp h1
  have htw : T *ᵥ w = w := by
    have h2 := hTv w
    rw [hφw, zero_smul, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h2
    exact h2
  have hcT : T = scalar (Fin n) (c : K) := hc
  have hc1 : (c : K) = 1 := by
    rw [hcT, scalar_apply] at htw
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hw0 (funext hall)
    have h3 := congrFun htw i
    rw [mulVec_diagonal] at h3
    exact mul_right_cancel₀ hi (by rw [h3, one_mul])
  apply hφ0
  refine LinearMap.ext fun v => ?_
  have h4 := hTv v
  rw [hcT, hc1, map_one, sub_self, zero_mulVec] at h4
  rw [LinearMap.zero_apply]
  by_contra hne
  apply hw0
  have h5 := congrArg (fun x => (φ v)⁻¹ • x) h4
  simp only [smul_zero, smul_smul, inv_mul_cancel₀ hne, one_smul] at h5
  exact h5.symm

@[expose] def orbitSpan (A : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    Submodule K (Fin n → K) :=
  Submodule.span K (Set.range fun j : Fin 3 => (A ^ (j : ℕ)) *ᵥ v)

theorem mem_orbitSpan_pow (A : Matrix (Fin n) (Fin n) K) (v : Fin n → K) (j : Fin 3) :
    (A ^ (j : ℕ)) *ᵥ v ∈ orbitSpan A v :=
  Submodule.subset_span ⟨j, rfl⟩

theorem mulVec_mem_orbitSpan {A : Matrix (Fin n) (Fin n) K} {c : K}
    (hA : A ^ 3 = c • (1 : Matrix (Fin n) (Fin n) K)) (v : Fin n → K) {w : Fin n → K}
    (hw : w ∈ orbitSpan A v) : A *ᵥ w ∈ orbitSpan A v := by
  refine Submodule.span_induction (p := fun w _ => A *ᵥ w ∈ orbitSpan A v) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨j, rfl⟩
    rw [Matrix.mulVec_mulVec, ← pow_succ']
    fin_cases j
    · exact mem_orbitSpan_pow A v 1
    · exact mem_orbitSpan_pow A v 2
    · change (A ^ 3) *ᵥ v ∈ orbitSpan A v
      rw [hA, Matrix.smul_mulVec, Matrix.one_mulVec]
      exact (orbitSpan A v).smul_mem c (by simpa using mem_orbitSpan_pow A v 0)
  · rw [Matrix.mulVec_zero]
    exact (orbitSpan A v).zero_mem
  · intro x y _ _ hx hy
    rw [Matrix.mulVec_add]
    exact (orbitSpan A v).add_mem hx hy
  · intro a x _ hx
    rw [Matrix.mulVec_smul]
    exact (orbitSpan A v).smul_mem a hx

theorem inv_mulVec_mem_orbitSpan {A : GL (Fin n) K} {c : K} (hc : c ≠ 0)
    (hA : (A : Matrix (Fin n) (Fin n) K) ^ 3 = c • (1 : Matrix (Fin n) (Fin n) K))
    (v : Fin n → K) {w : Fin n → K} (hw : w ∈ orbitSpan (A : Matrix (Fin n) (Fin n) K) v) :
    ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈
      orbitSpan (A : Matrix (Fin n) (Fin n) K) v := by
  have hinv : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c⁻¹ • (A : Matrix (Fin n) (Fin n) K) ^ 2 := by
    have h3 : (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) ^ 2 =
        (A : Matrix (Fin n) (Fin n) K) ^ 3 :=
      (pow_succ' (A : Matrix (Fin n) (Fin n) K) 2).symm
    have h1 : (A : Matrix (Fin n) (Fin n) K) * (c⁻¹ • (A : Matrix (Fin n) (Fin n) K) ^ 2) = 1 := by
      rw [Matrix.mul_smul, h3, hA, smul_smul, inv_mul_cancel₀ hc, one_smul]
    calc ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((A : Matrix (Fin n) (Fin n) K) * (c⁻¹ • (A : Matrix (Fin n) (Fin n) K) ^ 2)) := by
          rw [h1, Matrix.mul_one]
      _ = c⁻¹ • (A : Matrix (Fin n) (Fin n) K) ^ 2 := by
          rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  rw [hinv, Matrix.smul_mulVec, pow_two, ← Matrix.mulVec_mulVec]
  exact (orbitSpan _ v).smul_mem _ (mulVec_mem_orbitSpan hA v (mulVec_mem_orbitSpan hA v hw))

theorem orbitSpan_ne_bot (A : Matrix (Fin n) (Fin n) K) {v : Fin n → K} (hv : v ≠ 0) :
    orbitSpan A v ≠ ⊥ := by
  intro h
  have hmem := mem_orbitSpan_pow A v 0
  rw [h, Submodule.mem_bot] at hmem
  apply hv
  simpa using hmem

theorem orbitSpan_ne_top_of_four (hn : 4 ≤ n) (A : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    orbitSpan A v ≠ ⊤ := by
  intro h
  have h1 : Module.finrank K (orbitSpan A v) ≤ 3 := by
    have h2 := finrank_range_le_card (R := K) (fun j : Fin 3 => (A ^ (j : ℕ)) *ᵥ v)
    rw [Fintype.card_fin] at h2
    exact h2
  rw [h, finrank_top, Module.finrank_fin_fun] at h1
  omega

@[expose] def cycMat (A : Matrix (Fin 3) (Fin 3) K) (v : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => ((A ^ (j : ℕ)) *ᵥ v) i

theorem cycMat_mulVec (A : Matrix (Fin 3) (Fin 3) K) (v x : Fin 3 → K) :
    cycMat A v *ᵥ x = ∑ j, x j • ((A ^ (j : ℕ)) *ᵥ v) := by
  ext i
  simp only [cycMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem orbitSpan_ne_top_of_not_isUnit {A : Matrix (Fin 3) (Fin 3) K} {v : Fin 3 → K}
    (h : ¬ IsUnit (cycMat A v).det) : orbitSpan A v ≠ ⊤ := by
  intro htop
  apply h
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit]
  intro u
  have hu : u ∈ orbitSpan A v := by rw [htop]; exact Submodule.mem_top
  obtain ⟨x, hx⟩ := Submodule.mem_span_range_iff_exists_fun K |>.mp hu
  exact ⟨x, by rw [cycMat_mulVec, hx]⟩

@[expose] def compan (c : K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, c; 1, 0, 0; 0, 1, 0]

@[expose] def companInv (c : K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 1, 0; 0, 0, 1; c⁻¹, 0, 0]

theorem compan_mul_companInv {c : K} (hc : c ≠ 0) : compan c * companInv c = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compan, companInv, Matrix.mul_apply, Fin.sum_univ_three, hc]

theorem companInv_mul_compan {c : K} (hc : c ≠ 0) : companInv c * compan c = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compan, companInv, Matrix.mul_apply, Fin.sum_univ_three, hc]

@[expose] def companGL {c : K} (hc : c ≠ 0) : GL (Fin 3) K :=
  ⟨compan c, companInv c, compan_mul_companInv hc, companInv_mul_compan hc⟩

theorem mul_cycMat {A : Matrix (Fin 3) (Fin 3) K} {c : K}
    (hA : A ^ 3 = c • (1 : Matrix (Fin 3) (Fin 3) K)) (v : Fin 3 → K) :
    A * cycMat A v = cycMat A v * compan c := by
  have hcol : ∀ i (j : Fin 3), (A * cycMat A v) i j = ((A ^ ((j : ℕ) + 1)) *ᵥ v) i := by
    intro i j
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    rfl
  ext i j
  rw [hcol]
  fin_cases j
  · simp [cycMat, compan, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [cycMat, compan, Matrix.mul_apply, Fin.sum_univ_three]
  · change ((A ^ 3) *ᵥ v) i = _
    rw [hA, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp [cycMat, compan, Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

@[expose] def signDiag : Subgroup (SpecialLinearGroup (Fin 3) K) where
  carrier := {g | ∃ d : Fin 3 → K, (g : Matrix (Fin 3) (Fin 3) K) = diagonal d ∧
    ∀ i, d i * d i = 1}
  one_mem' := ⟨1, by simp, fun _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨d, hd, hd1⟩ ⟨e, he, he1⟩
    refine ⟨d * e, ?_, fun i => ?_⟩
    · change (g : Matrix (Fin 3) (Fin 3) K) * (h : Matrix (Fin 3) (Fin 3) K) = _
      rw [hd, he, diagonal_mul_diagonal]
      rfl
    · simp only [Pi.mul_apply]
      calc d i * e i * (d i * e i) = (d i * d i) * (e i * e i) := by ring
        _ = 1 := by rw [hd1, he1, one_mul]
  inv_mem' := by
    rintro g ⟨d, hd, hd1⟩
    have hgg : g * g = 1 := by
      apply Subtype.ext
      change (g : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) = 1
      rw [hd, diagonal_mul_diagonal]
      have : (fun i => d i * d i) = 1 := funext hd1
      rw [this]
      exact diagonal_one
    rw [inv_eq_of_mul_eq_one_right hgg]
    exact ⟨d, hd, hd1⟩

theorem mul_self_eq_one_of_mem_signDiag {g : SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ signDiag) : g * g = 1 := by
  obtain ⟨d, hd, hd1⟩ := hg
  apply Subtype.ext
  change (g : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) = 1
  rw [hd, diagonal_mul_diagonal]
  have : (fun i => d i * d i) = 1 := funext hd1
  rw [this]
  exact diagonal_one

theorem commute_of_mem_signDiag {g h : SpecialLinearGroup (Fin 3) K} (hg : g ∈ signDiag)
    (hh : h ∈ signDiag) : g * h = h * g := by
  obtain ⟨d, hd, -⟩ := hg
  obtain ⟨e, he, -⟩ := hh
  apply Subtype.ext
  change (g : Matrix (Fin 3) (Fin 3) K) * (h : Matrix (Fin 3) (Fin 3) K) =
    (h : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K)
  rw [hd, he, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem isPGroup_signDiag : IsPGroup 2 ↥(signDiag (K := K)) := fun g =>
  ⟨1, Subtype.ext (by
    rw [pow_one, sq, Subgroup.coe_mul, Subgroup.coe_one]
    exact mul_self_eq_one_of_mem_signDiag g.2)⟩

theorem compan_mul_diagonal_mul_companInv {c : K} (hc : c ≠ 0) (d : Fin 3 → K) :
    compan c * diagonal d * companInv c = diagonal ![d 2, d 0, d 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compan, companInv, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul_diagonal,
      mul_comm c, hc]

theorem slConjugation_companGL_mem_signDiag {c : K} (hc : c ≠ 0)
    {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ signDiag) :
    CatalogueBHigherLinearAction.slConjugation 3 K (companGL hc) g ∈ signDiag := by
  obtain ⟨d, hd, hd1⟩ := hg
  refine ⟨![d 2, d 0, d 1], ?_, fun i => ?_⟩
  · rw [coe_slConjugation, hd]
    exact compan_mul_diagonal_mul_companInv hc d
  · fin_cases i <;> simp [hd1]

@[expose] def sgn0 : SpecialLinearGroup (Fin 3) K :=
  ⟨diagonal ![-1, 1, -1], by simp [det_diagonal, Fin.prod_univ_three]⟩

@[expose] def sgn1 : SpecialLinearGroup (Fin 3) K :=
  ⟨diagonal ![-1, -1, 1], by simp [det_diagonal, Fin.prod_univ_three]⟩

theorem sgn0_mem : (sgn0 : SpecialLinearGroup (Fin 3) K) ∈ signDiag :=
  ⟨![-1, 1, -1], rfl, fun i => by fin_cases i <;> simp⟩

theorem slConjugation_companGL_sgn0 {c : K} (hc : c ≠ 0) :
    CatalogueBHigherLinearAction.slConjugation 3 K (companGL hc) sgn0 = sgn1 := by
  apply Subtype.ext
  rw [coe_slConjugation]
  change compan c * diagonal ![-1, 1, -1] * companInv c = diagonal ![-1, -1, 1]
  rw [compan_mul_diagonal_mul_companInv hc]
  congr 1

theorem proj_sgn1_ne_proj_sgn0 (h2 : (2 : K) ≠ 0) :
    proj 3 K (sgn1 : SpecialLinearGroup (Fin 3) K) ≠ proj 3 K sgn0 := by
  intro h
  obtain ⟨c, -, hc⟩ := proj_eq_proj_iff.mp h
  have hgg : (sgn1 : SpecialLinearGroup (Fin 3) K) * sgn1 = 1 :=
    mul_self_eq_one_of_mem_signDiag ⟨![-1, -1, 1], rfl, fun i => by fin_cases i <;> simp⟩
  rw [inv_eq_of_mul_eq_one_right hgg] at hc
  have h00 : ((diagonal ![-1, -1, 1] * diagonal ![-1, 1, -1] : Matrix (Fin 3) (Fin 3) K)) 0 0 =
      scalar (Fin 3) (c : K) 0 0 := congrFun (congrFun hc 0) 0
  have h11 : ((diagonal ![-1, -1, 1] * diagonal ![-1, 1, -1] : Matrix (Fin 3) (Fin 3) K)) 1 1 =
      scalar (Fin 3) (c : K) 1 1 := congrFun (congrFun hc 1) 1
  rw [diagonal_mul_diagonal] at h00 h11
  simp only [diagonal_apply_eq, scalar_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h11
  apply h2
  linear_combination h00 - h11

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3L
