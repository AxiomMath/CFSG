module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2Rows

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2

open CFSG Subgroup Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {R : Matrix ι ι K}

omit [Fintype ι] [DecidableEq ι] in
theorem mat_add_self (h2 : (2 : K) = 0) (A : Matrix ι ι K) : A + A = 0 := by
  ext i j
  rw [Matrix.add_apply, ← two_mul, h2, zero_mul, Matrix.zero_apply]

omit [Fintype ι] [DecidableEq ι] in
theorem pi_add_self (h2 : (2 : K) = 0) (x : ι → K) : x + x = 0 := by
  ext i
  rw [Pi.add_apply, ← two_mul, h2, zero_mul, Pi.zero_apply]

theorem exists_dual_of_notMem {W : Submodule K (ι → K)} {v : ι → K} (hv : v ∉ W) :
    ∃ χ : ι → K, χ ⬝ᵥ v = 1 ∧ ∀ w ∈ W, χ ⬝ᵥ w = 0 := by
  obtain ⟨f, hf, hW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  have key : ∀ w : ι → K, f w = (fun j => f (Pi.single j 1)) ⬝ᵥ w := by
    intro w
    conv_lhs => rw [← Finset.univ_sum_single w]
    rw [map_sum, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (Pi.single j (w j) : ι → K) = w j • Pi.single j 1 by
      ext k; by_cases hk : k = j <;> simp [hk], map_smul, smul_eq_mul, mul_comm]
  refine ⟨(f v)⁻¹ • fun j => f (Pi.single j 1), ?_, fun w hw => ?_⟩
  · rw [smul_dotProduct, ← key, smul_eq_mul, inv_mul_cancel₀ hf]
  · have h0 : f w = 0 := by
      have : f w ∈ W.map f := Submodule.mem_map_of_mem hw
      rwa [hW, Submodule.mem_bot] at this
    rw [smul_dotProduct, ← key, h0, smul_zero]

omit [DecidableEq ι] in
theorem vecMul_eq_mulVec (hR : Rᵀ = R) (v : ι → K) : v ᵥ* R = R *ᵥ v := by
  rw [← mulVec_transpose, hR]

omit [DecidableEq ι] in
theorem form_comm (hR : Rᵀ = R) (u v : ι → K) : (R *ᵥ u) ⬝ᵥ v = (R *ᵥ v) ⬝ᵥ u := by
  rw [dotProduct_comm, dotProduct_mulVec, vecMul_eq_mulVec hR]

omit [DecidableEq ι] in
theorem vecMulVec_transpose_mul (hR : Rᵀ = R) (v : ι → K) :
    (vecMulVec v (R *ᵥ v))ᵀ * R = R * vecMulVec v (R *ᵥ v) := by
  rw [transpose_vecMulVec, vecMulVec_mul, vecMul_eq_mulVec hR, mul_vecMulVec]

omit [DecidableEq ι] in
theorem vecMulVec_mul_mul_self (u w : ι → K) (M : Matrix ι ι K) :
    vecMulVec u w * M * vecMulVec u w = (w ⬝ᵥ (M *ᵥ u)) • vecMulVec u w := by
  rw [vecMulVec_mul, vecMulVec_mul_vecMulVec, ← dotProduct_mulVec, vecMulVec_smul]

omit [DecidableEq ι] in
theorem mul_vecMulVec_ne {M : Matrix ι ι K} {u w v φ : ι → K} (hwv : w ⬝ᵥ v = 1)
    (hφu : φ ⬝ᵥ u = 0) (hφM : φ ⬝ᵥ (M *ᵥ u) ≠ 0) : M * vecMulVec u w ≠ vecMulVec u w * M := by
  intro heq
  have h := congrArg (fun X => φ ⬝ᵥ (X *ᵥ v)) heq
  simp only [← mulVec_mulVec, vecMulVec_mulVec, hwv, MulOpposite.op_one, op_smul_eq_smul,
    one_smul, dotProduct_smul, hφu, smul_eq_mul, mul_zero] at h
  exact hφM h

theorem iso_one_add (h2 : (2 : K) = 0) {X : Matrix ι ι K} (hXR : Xᵀ * R = R * X)
    (hXX : X * X = 0) : (1 + X)ᵀ * R * (1 + X) = R := by
  rw [transpose_add, transpose_one,
    show (1 + Xᵀ) * R * (1 + X) = R + (R * X + Xᵀ * R) + Xᵀ * R * X by noncomm_ring, hXR,
    mat_add_self h2 (R * X), mul_assoc, hXX, mul_zero, add_zero, add_zero]

theorem det_eq_one_of_iso (h2 : (2 : K) = 0) (hR : R.det ≠ 0) {T : Matrix ι ι K}
    (hT : Tᵀ * R * T = R) : T.det = 1 := by
  have hd : T.det * T.det = 1 := by
    have h := congrArg Matrix.det hT
    rw [det_mul, det_mul, det_transpose] at h
    have h0 : (T.det * T.det - 1) * R.det = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right hR)
  have h0 : (T.det - 1) * (T.det - 1) = 0 := by
    rw [show (T.det - 1) * (T.det - 1) = T.det * T.det - 2 * T.det + 1 by ring, hd, h2,
      zero_mul, sub_zero, one_add_one_eq_two, h2]
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h0)

@[expose] def isoSL (h2 : (2 : K) = 0) (hR : R.det ≠ 0) (T : Matrix ι ι K)
    (hT : Tᵀ * R * T = R) : SpecialLinearGroup ι K :=
  ⟨T, det_eq_one_of_iso h2 hR hT⟩

@[simp]
theorem coe_isoSL (h2 : (2 : K) = 0) (hR : R.det ≠ 0) (T : Matrix ι ι K)
    (hT : Tᵀ * R * T = R) : (isoSL h2 hR T hT : Matrix ι ι K) = T :=
  rfl

theorem form_self_eq (h2 : (2 : K) = 0) (hR : Rᵀ = R) {d : ι → K}
    (hd : ∀ i, d i * d i = R i i) (x : ι → K) :
    (R *ᵥ x) ⬝ᵥ x = (d ⬝ᵥ x) * (d ⬝ᵥ x) := by
  let Q : (ι → K) →+ K :=
    { toFun := fun x => (R *ᵥ x) ⬝ᵥ x
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [mulVec_add, add_dotProduct, dotProduct_add]
        rw [form_comm hR y x]
        linear_combination ((R *ᵥ x) ⬝ᵥ y) * h2 }
  let Q' : (ι → K) →+ K :=
    { toFun := fun x => (d ⬝ᵥ x) * (d ⬝ᵥ x)
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [dotProduct_add]
        linear_combination (d ⬝ᵥ x * d ⬝ᵥ y) * h2 }
  have hQ : Q = Q' := AddMonoidHom.functions_ext _ Q Q' fun i c => by
    change (R *ᵥ Pi.single i c) ⬝ᵥ Pi.single i c = (d ⬝ᵥ Pi.single i c) * (d ⬝ᵥ Pi.single i c)
    rw [dotProduct_single, dotProduct_single, mulVec_single]
    simp only [Pi.smul_apply, col_apply, op_smul_eq_smul, smul_eq_mul]
    rw [← hd i]
    ring
  exact DFunLike.congr_fun hQ x

omit [DecidableEq ι] in
theorem exists_pair_ker_of {m : ℕ} (hmn : m + 2 ≤ Fintype.card ι) (Φ : Fin m → ι → K) :
    ∃ x₁ x₂ : ι → K, (∀ i, Φ i ⬝ᵥ x₁ = 0) ∧ (∀ i, Φ i ⬝ᵥ x₂ = 0) ∧
      LinearIndependent K ![x₁, x₂] := by
  set W := LinearMap.ker (Matrix.of Φ).mulVecLin with hW
  have hmem : ∀ x : ι → K, x ∈ W ↔ ∀ i, Φ i ⬝ᵥ x = 0 := by
    intro x
    rw [hW, LinearMap.mem_ker, mulVecLin_apply, funext_iff]
    simp [mulVec, Matrix.of_apply]
  have hrk := LinearMap.finrank_range_add_finrank_ker (Matrix.of Φ).mulVecLin
  have hle : Module.finrank K (LinearMap.range (Matrix.of Φ).mulVecLin) ≤ m := by
    have := Submodule.finrank_le (LinearMap.range (Matrix.of Φ).mulVecLin)
    simpa using this
  rw [Module.finrank_fintype_fun_eq_card, ← hW] at hrk
  have hW2 : 1 < Module.finrank K W := by omega
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < Module.finrank K W)
  obtain ⟨x', hxx'⟩ := exists_linearIndependent_pair_of_one_lt_finrank hW2 hx
  have hp := LinearIndependent.pair_iff.mp hxx'
  refine ⟨x, x', (hmem x).mp x.2, (hmem x').mp x'.2,
    LinearIndependent.pair_iff.mpr fun s t hst => hp s t ?_⟩
  exact Subtype.ext (by simpa using hst)

theorem exists_notMem_span_of_pair {A : Matrix ι ι K} (hAR : A * R = 1)
    (d : ι → K) {P : (ι → K) → Prop} {z₁ z₂ : ι → K} (h₁ : P z₁) (h₂ : P z₂)
    (hind : LinearIndependent K ![z₁, z₂]) :
    ∃ z, P z ∧ R *ᵥ z ∉ Submodule.span K {d} := by
  by_contra hc
  push Not at hc
  obtain ⟨c₁, hc₁⟩ := Submodule.mem_span_singleton.mp (hc z₁ h₁)
  obtain ⟨c₂, hc₂⟩ := Submodule.mem_span_singleton.mp (hc z₂ h₂)
  have hp := LinearIndependent.pair_iff.mp hind
  have hA : ∀ z, A *ᵥ (R *ᵥ z) = z := fun z => by rw [mulVec_mulVec, hAR, one_mulVec]
  have h0 : c₂ • z₁ + (-c₁) • z₂ = 0 := by
    rw [← hA (c₂ • z₁ + (-c₁) • z₂), mulVec_add, mulVec_smul, mulVec_smul, ← hc₁, ← hc₂,
      smul_smul, smul_smul, mul_comm c₂ c₁, neg_mul, neg_smul, add_neg_cancel, mulVec_zero]
  obtain ⟨-, hc₁0⟩ := hp _ _ h0
  rw [neg_eq_zero] at hc₁0
  rw [hc₁0, zero_smul] at hc₁
  have hz : z₁ = 0 := by rw [← hA z₁, ← hc₁, mulVec_zero]
  exact hind.ne_zero 0 (by simpa using hz)

theorem exists_hyp_pair (hn : 3 ≤ Fintype.card ι) {A : Matrix ι ι K} (hAR : A * R = 1)
    (d : ι → K) :
    ∃ x y : ι → K, d ⬝ᵥ x = 0 ∧ d ⬝ᵥ y = 0 ∧ (R *ᵥ x) ⬝ᵥ y = 1 := by
  obtain ⟨z₁, z₂, h₁, h₂, hind⟩ := exists_pair_ker_of (m := 1) (by omega) ![d]
  obtain ⟨x, hx, hxd⟩ := exists_notMem_span_of_pair hAR d (P := fun z => d ⬝ᵥ z = 0)
    (h₁ 0) (h₂ 0) hind
  obtain ⟨y, hy1, hyW⟩ := exists_dual_of_notMem hxd
  refine ⟨x, y, hx, ?_, ?_⟩
  · rw [dotProduct_comm]
    exact hyW d (Submodule.mem_span_singleton_self d)
  · rw [dotProduct_comm]
    exact hy1

theorem exists_hyp_pair_perp (hn : 5 ≤ Fintype.card ι) (hR : Rᵀ = R) {A : Matrix ι ι K}
    (hAR : A * R = 1) {d x₁ y₁ : ι → K} (hx₁ : d ⬝ᵥ x₁ = 0) (hy₁ : d ⬝ᵥ y₁ = 0)
    (hxx : (R *ᵥ x₁) ⬝ᵥ x₁ = 0) (hyy : (R *ᵥ y₁) ⬝ᵥ y₁ = 0) (hxy : (R *ᵥ x₁) ⬝ᵥ y₁ = 1) :
    ∃ x y : ι → K, d ⬝ᵥ x = 0 ∧ d ⬝ᵥ y = 0 ∧ (R *ᵥ x) ⬝ᵥ y = 1 ∧
      (R *ᵥ x₁) ⬝ᵥ x = 0 ∧ (R *ᵥ y₁) ⬝ᵥ x = 0 ∧ (R *ᵥ x₁) ⬝ᵥ y = 0 ∧
        (R *ᵥ y₁) ⬝ᵥ y = 0 := by
  obtain ⟨z₁, z₂, h₁, h₂, hind⟩ :=
    exists_pair_ker_of (m := 3) (by omega) ![d, R *ᵥ x₁, R *ᵥ y₁]
  obtain ⟨x, hx, hxd⟩ := exists_notMem_span_of_pair hAR d
    (P := fun z => d ⬝ᵥ z = 0 ∧ (R *ᵥ x₁) ⬝ᵥ z = 0 ∧ (R *ᵥ y₁) ⬝ᵥ z = 0)
    ⟨h₁ 0, h₁ 1, h₁ 2⟩ ⟨h₂ 0, h₂ 1, h₂ 2⟩ hind
  obtain ⟨hxd0, hxx₁, hxy₁⟩ := hx
  have hyx : (R *ᵥ y₁) ⬝ᵥ x₁ = 1 := by rw [form_comm hR]; exact hxy
  have hW : R *ᵥ x ∉ Submodule.span K {d, R *ᵥ x₁, R *ᵥ y₁} := by
    intro hmem
    apply hxd
    obtain ⟨a, w, hw, hxw⟩ := Submodule.mem_span_insert.mp hmem
    obtain ⟨b, c, rfl⟩ := Submodule.mem_span_pair.mp hw
    have e₁ := congrArg (· ⬝ᵥ x₁) hxw
    have e₂ := congrArg (· ⬝ᵥ y₁) hxw
    simp only [add_dotProduct, smul_dotProduct, hx₁, hy₁, hxx, hyy, hxy, hyx, smul_eq_mul,
      mul_zero, mul_one, zero_add, add_zero] at e₁ e₂
    rw [form_comm hR, hxx₁] at e₁
    rw [form_comm hR, hxy₁] at e₂
    rw [← e₁, ← e₂, zero_smul, zero_smul, add_zero, add_zero] at hxw
    rw [hxw]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self d)
  obtain ⟨y, hy1, hyW⟩ := exists_dual_of_notMem hW
  have hyv : ∀ v ∈ ({d, R *ᵥ x₁, R *ᵥ y₁} : Set (ι → K)), v ⬝ᵥ y = 0 := fun v hv => by
    rw [dotProduct_comm]
    exact hyW v (Submodule.subset_span hv)
  refine ⟨x, y, hxd0, hyv d (by simp), ?_, hxx₁, hxy₁, hyv _ (by simp), hyv _ (by simp)⟩
  rw [dotProduct_comm]
  exact hy1

end CFSG.ComponentClassification.HarrisLit.L33.C2
