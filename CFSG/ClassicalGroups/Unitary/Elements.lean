module

public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.ClassicalGroups.Unitary

open Matrix CFSG.LieType.Universal.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

variable (σ) in
@[expose] noncomputable def tvMat (a : Fin n → K) (c : K) : Matrix (Fin n) (Fin n) K :=
  1 + c • vecMulVec a (fun i => σ (a i))

theorem tvMat_mulVec (a : Fin n → K) (c : K) (v : Fin n → K) :
    tvMat σ a c *ᵥ v = v + (c * herm σ a v) • a := by
  rw [tvMat, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    op_smul_eq_smul, smul_smul]
  rfl

theorem tvMat_det {a : Fin n → K} (ha : herm σ a a = 0) (c : K) : (tvMat σ a c).det = 1 := by
  rw [tvMat, ← Matrix.vecMulVec_smul, Matrix.vecMulVec_eq (Fin 1),
    Matrix.det_one_add_replicateCol_mul_replicateRow, smul_dotProduct, smul_eq_mul]
  have : (fun i => σ (a i)) ⬝ᵥ a = herm σ a a := rfl
  rw [this, ha, mul_zero, add_zero]

theorem tvMat_isometry (hσ : ∀ c, σ (σ c) = c) {a : Fin n → K} (ha : herm σ a a = 0) {c : K}
    (hc : c + σ c = 0) (x y : Fin n → K) :
    herm σ (tvMat σ a c *ᵥ x) (tvMat σ a c *ᵥ y) = herm σ x y := by
  rw [tvMat_mulVec, tvMat_mulVec]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, ha, map_mul,
    mul_zero, add_zero]
  rw [herm_conj σ hσ a x]
  linear_combination σ (herm σ a x) * herm σ a y * hc

@[expose] noncomputable def tv (hσ : ∀ c, σ (σ c) = c) {a : Fin n → K} (ha : herm σ a a = 0)
    {c : K} (hc : c + σ c = 0) : SUid σ n :=
  mkSU σ (tvMat σ a c) (tvMat_det ha c) (tvMat_isometry hσ ha hc)

theorem tv_smul (hσ : ∀ c, σ (σ c) = c) {a : Fin n → K} (ha : herm σ a a = 0) {c : K}
    (hc : c + σ c = 0) (v : Fin n → K) : tv hσ ha hc • v = v + (c * herm σ a v) • a :=
  tvMat_mulVec a c v

variable (σ n) in
@[expose] def tvSet : Set (SUid σ n) :=
  {g | ∃ (a : Fin n → K) (c : K), herm σ a a = 0 ∧ c + σ c = 0 ∧
    ∀ v, g • v = v + (c * herm σ a v) • a}

variable (σ n) in
@[expose] def T : Subgroup (SUid σ n) := Subgroup.closure (tvSet σ n)

theorem mem_T_of_smul {g : SUid σ n} {a : Fin n → K} (ha : herm σ a a = 0) {c : K}
    (hc : c + σ c = 0) (h : ∀ v, g • v = v + (c * herm σ a v) • a) : g ∈ T σ n :=
  Subgroup.subset_closure ⟨a, c, ha, hc, h⟩

theorem tv_mem_T (hσ : ∀ c, σ (σ c) = c) {a : Fin n → K} (ha : herm σ a a = 0) {c : K}
    (hc : c + σ c = 0) : tv hσ ha hc ∈ T σ n :=
  mem_T_of_smul ha hc (tv_smul hσ ha hc)

theorem exists_mem_T_tv (hσ : ∀ c, σ (σ c) = c) {a : Fin n → K} (ha : herm σ a a = 0) {c : K}
    (hc : c + σ c = 0) : ∃ g ∈ T σ n, ∀ v, g • v = v + (c * herm σ a v) • a :=
  ⟨tv hσ ha hc, tv_mem_T hσ ha hc, tv_smul hσ ha hc⟩

theorem tv_mul_tv (hσ : ∀ c, σ (σ c) = c) {a : Fin n → K} (ha : herm σ a a = 0) {c d : K}
    (hc : c + σ c = 0) (hd : d + σ d = 0) (hcd : (c + d) + σ (c + d) = 0) :
    tv hσ ha hc * tv hσ ha hd = tv hσ ha hcd := by
  apply ext_smul
  intro v
  rw [mul_smul, tv_smul, tv_smul, tv_smul]
  simp only [herm_add_right, herm_smul_right, ha, mul_zero, add_zero]
  module

theorem tv_zero (hσ : ∀ c, σ (σ c) = c) {a : Fin n → K} (ha : herm σ a a = 0)
    (h0 : (0 : K) + σ 0 = 0) : tv hσ ha h0 = 1 := by
  apply ext_smul
  intro v
  rw [tv_smul, one_smul, zero_mul, zero_smul, add_zero]

theorem conj_smul_of_tv (g t : SUid σ n) {a : Fin n → K} {c : K}
    (h : ∀ v, t • v = v + (c * herm σ a v) • a) (v : Fin n → K) :
    (g * t * g⁻¹) • v = v + (c * herm σ (g • a) v) • (g • a) := by
  rw [mul_smul, mul_smul, h, smul_add, smul_inv_smul, smul_comm g (c * _) a]
  congr 3
  rw [← herm_smul_smul σ g a (g⁻¹ • v), smul_inv_smul]

theorem conj_mem_tvSet (g : SUid σ n) {t : SUid σ n}
    (ht : t ∈ tvSet σ n) : g * t * g⁻¹ ∈ tvSet σ n := by
  obtain ⟨a, c, ha, hc, h⟩ := ht
  exact ⟨g • a, c, by rw [herm_smul_smul, ha], hc, conj_smul_of_tv g t h⟩

theorem T_normal : (T σ n).Normal := by
  refine ⟨fun x hx g => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem t ht => exact Subgroup.subset_closure (conj_mem_tvSet g ht)
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact (T σ n).mul_mem hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact (T σ n).inv_mem hx

theorem exists_mem_T_siegel (hσ : IsUnitaryInvolution σ) {e w : Fin n → K}
    (he : herm σ e e = 0) (hw : herm σ w w = 0) (hew : herm σ e w = 0) (μ : K) :
    ∃ g ∈ T σ n, ∀ x, g • x = x + (μ * herm σ e x) • w - (σ μ * herm σ w x) • e := by
  obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
  have hwe : herm σ w e = 0 := herm_eq_zero_comm σ hσ.invol hew
  have hστ : σ τ = -τ := by linear_combination hτ
  obtain ⟨l, hτl⟩ : ∃ l, τ * l = μ := ⟨μ / τ, by field_simp⟩
  have hτσl : τ * σ l = -σ μ := by
    have := congrArg σ hτl
    rw [map_mul, hστ] at this
    linear_combination -this
  have hiso : herm σ (e + l • w) (e + l • w) = 0 := by
    simp [he, hw, hew, hwe]
  have h2 : -τ + σ (-τ) = 0 := by rw [map_neg]; linear_combination -hτ
  have h3 : -(τ * (σ l * l)) + σ (-(τ * (σ l * l))) = 0 := by
    rw [map_neg, map_mul, hσ.norm_fixed]
    linear_combination -(σ l * l) * hτ
  obtain ⟨t1, ht1, ht1s⟩ := exists_mem_T_tv hσ.invol hiso hτ
  obtain ⟨t2, ht2, ht2s⟩ := exists_mem_T_tv hσ.invol he h2
  obtain ⟨t3, ht3, ht3s⟩ := exists_mem_T_tv hσ.invol hw h3
  refine ⟨t1 * t2 * t3, (T σ n).mul_mem ((T σ n).mul_mem ht1 ht2) ht3, fun x => ?_⟩
  rw [mul_smul, mul_smul, ht3s, ht2s, ht1s]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, he,
    hw, hew, hwe, mul_zero, add_zero]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (herm σ e x * w i) * hτl + (herm σ w x * e i) * hτσl

@[expose] noncomputable def eichlerMat (σ : K ≃+* K) (e y : Fin n → K) (c : K) :
    Matrix (Fin n) (Fin n) K :=
  (1 + vecMulVec (y + c • e) (fun i => σ (e i))) * (1 + vecMulVec (-e) (fun i => σ (y i)))

theorem eichlerMat_mulVec {e y : Fin n → K} (he : herm σ e e = 0) (c : K) (x : Fin n → K) :
    eichlerMat σ e y c *ᵥ x = x + herm σ e x • (y + c • e) - herm σ y x • e := by
  rw [eichlerMat, ← Matrix.mulVec_mulVec]
  have h1 : ∀ (u : Fin n → K) (w : Fin n → K) (z : Fin n → K),
      (1 + vecMulVec u (fun i => σ (w i))) *ᵥ z = z + herm σ w z • u := by
    intro u w z
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
    rfl
  rw [h1, h1]
  simp only [herm_add_right, herm_smul_right, herm_neg_right, he, mul_zero, neg_zero, add_zero]
  module

theorem eichlerMat_det (hσ : ∀ c, σ (σ c) = c) {e y : Fin n → K} (he : herm σ e e = 0)
    (hey : herm σ e y = 0) (c : K) : (eichlerMat σ e y c).det = 1 := by
  rw [eichlerMat, Matrix.det_mul, Matrix.vecMulVec_eq (Fin 1), Matrix.vecMulVec_eq (Fin 1),
    Matrix.det_one_add_replicateCol_mul_replicateRow,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  have e1 : (fun i => σ (e i)) ⬝ᵥ (y + c • e) = herm σ e (y + c • e) := rfl
  have e2 : (fun i => σ (y i)) ⬝ᵥ (-e) = herm σ y (-e) := rfl
  rw [e1, e2, herm_add_right, herm_smul_right, he, hey, herm_neg_right,
    herm_eq_zero_comm σ hσ hey]
  ring

theorem eichler_isometry (hσ : ∀ c, σ (σ c) = c) {e y : Fin n → K} (he : herm σ e e = 0)
    (hey : herm σ e y = 0) {c : K} (hc : c + σ c = -herm σ y y) (x x' : Fin n → K) :
    herm σ (x + herm σ e x • (y + c • e) - herm σ y x • e)
      (x' + herm σ e x' • (y + c • e) - herm σ y x' • e) = herm σ x x' := by
  have hye : herm σ y e = 0 := herm_eq_zero_comm σ hσ hey
  simp only [herm_add_left, herm_add_right, herm_sub_left, herm_sub_right, herm_smul_left,
    herm_smul_right, he, hey, hye, mul_zero, add_zero, sub_zero]
  simp only [herm_conj σ hσ e x, herm_conj σ hσ x y, hσ]
  linear_combination σ (herm σ e x) * herm σ e x' * hc

@[expose] noncomputable def eichler (hσ : ∀ c, σ (σ c) = c) {e y : Fin n → K}
    (he : herm σ e e = 0) (hey : herm σ e y = 0) {c : K} (hc : c + σ c = -herm σ y y) :
    SUid σ n :=
  mkSU σ (eichlerMat σ e y c) (eichlerMat_det hσ he hey c) (fun x x' => by
    rw [eichlerMat_mulVec he, eichlerMat_mulVec he]
    exact eichler_isometry hσ he hey hc x x')

theorem eichler_smul (hσ : ∀ c, σ (σ c) = c) {e y : Fin n → K} (he : herm σ e e = 0)
    (hey : herm σ e y = 0) {c : K} (hc : c + σ c = -herm σ y y) (x : Fin n → K) :
    eichler hσ he hey hc • x = x + herm σ e x • (y + c • e) - herm σ y x • e :=
  eichlerMat_mulVec he c x

theorem eichler_smul_self (hσ : ∀ c, σ (σ c) = c) {e y : Fin n → K} (he : herm σ e e = 0)
    (hey : herm σ e y = 0) {c : K} (hc : c + σ c = -herm σ y y) :
    eichler hσ he hey hc • e = e := by
  rw [eichler_smul, he, herm_eq_zero_comm σ hσ hey, zero_smul, zero_smul, add_zero, sub_zero]

theorem eichler_mul_eichler (hσ : ∀ c, σ (σ c) = c) {e y y' : Fin n → K} (he : herm σ e e = 0)
    (hey : herm σ e y = 0) (hey' : herm σ e y' = 0) {c c' : K} (hc : c + σ c = -herm σ y y)
    (hc' : c' + σ c' = -herm σ y' y')
    (ht : (herm σ y' y - herm σ y y') + σ (herm σ y' y - herm σ y y') = 0) :
    eichler hσ he hey hc * eichler hσ he hey' hc' =
      tv hσ he ht * (eichler hσ he hey' hc' * eichler hσ he hey hc) := by
  have hye : herm σ y e = 0 := herm_eq_zero_comm σ hσ hey
  have hy'e : herm σ y' e = 0 := herm_eq_zero_comm σ hσ hey'
  apply ext_smul
  intro x
  rw [mul_smul, mul_smul, mul_smul, eichler_smul, eichler_smul, eichler_smul, eichler_smul,
    tv_smul]
  simp only [herm_add_right, herm_sub_right, herm_smul_right, he, hey, hey', hye,
    hy'e, mul_zero, add_zero, sub_zero]
  match_scalars <;> ring

end CFSG.ClassicalGroups.Unitary
