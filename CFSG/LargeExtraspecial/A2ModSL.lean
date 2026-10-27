module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

public section

namespace CFSG.LargeExtraspecial.A2Mod

open Matrix
open scoped commutatorElement

variable {n : ℕ} {R : Type*} [CommRing R]

theorem det_one_add_vecMulVec_eq (v φ : Fin n → R) : (1 + vecMulVec v φ).det = 1 + φ ⬝ᵥ v := by
  rw [vecMulVec_eq (Fin 1), det_one_add_replicateCol_mul_replicateRow]

private def tvAux {v φ : Fin n → R} (h : φ ⬝ᵥ v = 0) : SpecialLinearGroup (Fin n) R :=
  ⟨1 + vecMulVec v φ, by rw [det_one_add_vecMulVec_eq, h, add_zero]⟩

open Classical in
noncomputable def tv (v φ : Fin n → R) : SpecialLinearGroup (Fin n) R :=
  if h : φ ⬝ᵥ v = 0 then tvAux h else 1

theorem coe_tv {v φ : Fin n → R} (h : φ ⬝ᵥ v = 0) :
    ((tv v φ : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 + vecMulVec v φ := by
  simp only [tv, h, ↓reduceDIte]
  rfl

theorem tv_of_dotProduct_ne_zero {v φ : Fin n → R} (h : φ ⬝ᵥ v ≠ 0) : tv v φ = 1 := by
  simp only [tv, h, ↓reduceDIte]

theorem tv_mulVec {v φ : Fin n → R} (h : φ ⬝ᵥ v = 0) (x : Fin n → R) :
    ((tv v φ : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ x =
      x + (φ ⬝ᵥ x) • v := by
  rw [coe_tv h, add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]

theorem tv_mulVec_of_dotProduct_eq_zero {v φ x : Fin n → R} (hx : φ ⬝ᵥ x = 0) :
    ((tv v φ : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ x = x := by
  by_cases h : φ ⬝ᵥ v = 0
  · rw [tv_mulVec h, hx, zero_smul, add_zero]
  · rw [tv_of_dotProduct_ne_zero h, SpecialLinearGroup.coe_one, one_mulVec]

@[simp]
theorem tv_zero_left (φ : Fin n → R) : tv 0 φ = 1 :=
  Subtype.ext (by rw [coe_tv (dotProduct_zero φ), zero_vecMulVec, add_zero]; rfl)

@[simp]
theorem tv_zero_right (v : Fin n → R) : tv v 0 = 1 :=
  Subtype.ext (by rw [coe_tv (zero_dotProduct v), vecMulVec_zero, add_zero]; rfl)

theorem tv_mul_tv_left {v φ ψ : Fin n → R} (h : φ ⬝ᵥ v = 0) (h' : ψ ⬝ᵥ v = 0) :
    tv v φ * tv v ψ = tv v (φ + ψ) := by
  have h'' : (φ + ψ) ⬝ᵥ v = 0 := by rw [add_dotProduct, h, h', add_zero]
  refine Subtype.ext ?_
  rw [SpecialLinearGroup.coe_mul, coe_tv h, coe_tv h', coe_tv h'', add_mul, mul_add, mul_add,
    one_mul, mul_one, one_mul, vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero, add_zero,
    vecMulVec_add]
  abel

theorem tv_mul_tv_right {v w φ : Fin n → R} (h : φ ⬝ᵥ v = 0) (h' : φ ⬝ᵥ w = 0) :
    tv v φ * tv w φ = tv (v + w) φ := by
  have h'' : φ ⬝ᵥ (v + w) = 0 := by rw [dotProduct_add, h, h', add_zero]
  refine Subtype.ext ?_
  rw [SpecialLinearGroup.coe_mul, coe_tv h, coe_tv h', coe_tv h'', add_mul, mul_add, mul_add,
    one_mul, mul_one, one_mul, vecMulVec_mul_vecMulVec, h', zero_smul, vecMulVec_zero, add_zero,
    add_vecMulVec]
  abel

theorem tv_inv {v φ : Fin n → R} (h : φ ⬝ᵥ v = 0) : (tv v φ)⁻¹ = tv v (-φ) := by
  have h' : (-φ) ⬝ᵥ v = 0 := by rw [neg_dotProduct, h, neg_zero]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [tv_mul_tv_left h h', add_neg_cancel, tv_zero_right]

theorem tv_neg_left (v φ : Fin n → R) : tv (-v) φ = tv v (-φ) := by
  by_cases h : φ ⬝ᵥ v = 0
  · have h₁ : φ ⬝ᵥ (-v) = 0 := by rw [dotProduct_neg, h, neg_zero]
    have h₂ : (-φ) ⬝ᵥ v = 0 := by rw [neg_dotProduct, h, neg_zero]
    exact Subtype.ext (by rw [coe_tv h₁, coe_tv h₂, neg_vecMulVec, vecMulVec_neg])
  · have h₁ : φ ⬝ᵥ (-v) ≠ 0 := by rwa [dotProduct_neg, neg_ne_zero]
    have h₂ : (-φ) ⬝ᵥ v ≠ 0 := by rwa [neg_dotProduct, neg_ne_zero]
    rw [tv_of_dotProduct_ne_zero h₁, tv_of_dotProduct_ne_zero h₂]

theorem tv_smul_left (c : R) (v φ : Fin n → R) : tv (c • v) φ = tv v (c • φ) := by
  have hdot : φ ⬝ᵥ (c • v) = (c • φ) ⬝ᵥ v := by rw [dotProduct_smul, smul_dotProduct]
  by_cases h : φ ⬝ᵥ (c • v) = 0
  · exact Subtype.ext (by rw [coe_tv h, coe_tv (hdot ▸ h), smul_vecMulVec, vecMulVec_smul])
  · rw [tv_of_dotProduct_ne_zero h, tv_of_dotProduct_ne_zero (hdot ▸ h)]

theorem transvection_eq_tv {i j : Fin n} (hij : i ≠ j) (c : R) :
    SpecialLinearGroup.transvection hij c = tv (Pi.single i c) (Pi.single j 1) := by
  have h : (Pi.single j (1 : R) : Fin n → R) ⬝ᵥ Pi.single i c = 0 := by
    rw [single_dotProduct, one_mul, Pi.single_eq_of_ne hij.symm]
  refine Subtype.ext ?_
  rw [coe_tv h, SpecialLinearGroup.transvection_coe]
  congr 1
  ext a b
  simp only [single_apply, vecMulVec_apply, Pi.single_apply]
  by_cases ha : a = i <;> by_cases hb : b = j
  · subst ha hb
    simp
  · subst ha
    simp [hb, Ne.symm hb]
  · subst hb
    simp [ha, Ne.symm ha]
  · simp [ha, hb, Ne.symm ha, Ne.symm hb]

theorem transvection_eq_tv' {i j : Fin n} (hij : i ≠ j) (c : R) :
    SpecialLinearGroup.transvection hij c = tv (Pi.single i 1) (Pi.single j c) := by
  have e1 : (Pi.single i c : Fin n → R) = c • Pi.single i 1 := by
    funext a
    by_cases ha : a = i <;> simp [ha]
  have e2 : (Pi.single j c : Fin n → R) = c • Pi.single j 1 := by
    funext a
    by_cases ha : a = j <;> simp [ha]
  rw [transvection_eq_tv hij, e1, e2, tv_smul_left]

@[expose] def contra (g : SpecialLinearGroup (Fin n) R) (φ : Fin n → R) : Fin n → R :=
  φ ᵥ* ((g⁻¹ : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)

theorem contra_def (g : SpecialLinearGroup (Fin n) R) (φ : Fin n → R) :
    contra g φ = φ ᵥ* ((g⁻¹ : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) :=
  rfl

theorem sl_coe_mul_coe_inv (g : SpecialLinearGroup (Fin n) R) :
    (g : Matrix (Fin n) (Fin n) R) * ((g⁻¹ : SpecialLinearGroup (Fin n) R) :
      Matrix (Fin n) (Fin n) R) = 1 := by
  rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]

theorem sl_coe_inv_mul_coe (g : SpecialLinearGroup (Fin n) R) :
    ((g⁻¹ : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) *
      (g : Matrix (Fin n) (Fin n) R) = 1 := by
  rw [← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one]

theorem sl_mulVec_mul (g h : SpecialLinearGroup (Fin n) R) (x : Fin n → R) :
    ((g * h : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ x =
      (g : Matrix (Fin n) (Fin n) R) *ᵥ ((h : Matrix (Fin n) (Fin n) R) *ᵥ x) := by
  rw [SpecialLinearGroup.coe_mul, mulVec_mulVec]

theorem sl_inv_mulVec_mulVec (g : SpecialLinearGroup (Fin n) R) (x : Fin n → R) :
    ((g⁻¹ : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ
      ((g : Matrix (Fin n) (Fin n) R) *ᵥ x) = x := by
  rw [mulVec_mulVec, sl_coe_inv_mul_coe, one_mulVec]

theorem sl_mulVec_inv_mulVec (g : SpecialLinearGroup (Fin n) R) (x : Fin n → R) :
    (g : Matrix (Fin n) (Fin n) R) *ᵥ
      (((g⁻¹ : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ x) = x := by
  rw [mulVec_mulVec, sl_coe_mul_coe_inv, one_mulVec]

theorem sl_mulVec_eq_zero_iff (g : SpecialLinearGroup (Fin n) R) {x : Fin n → R} :
    (g : Matrix (Fin n) (Fin n) R) *ᵥ x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, mulVec_zero]⟩
  rw [← sl_inv_mulVec_mulVec g x, h, mulVec_zero]

@[simp]
theorem contra_one (φ : Fin n → R) : contra 1 φ = φ := by
  rw [contra_def, inv_one, SpecialLinearGroup.coe_one, vecMul_one]

theorem contra_mul (g h : SpecialLinearGroup (Fin n) R) (φ : Fin n → R) :
    contra (g * h) φ = contra g (contra h φ) := by
  rw [contra_def, contra_def, contra_def, _root_.mul_inv_rev, SpecialLinearGroup.coe_mul,
    vecMul_vecMul]

theorem contra_dotProduct_mulVec (g : SpecialLinearGroup (Fin n) R) (φ x : Fin n → R) :
    contra g φ ⬝ᵥ ((g : Matrix (Fin n) (Fin n) R) *ᵥ x) = φ ⬝ᵥ x := by
  rw [contra_def, dotProduct_mulVec, vecMul_vecMul, sl_coe_inv_mul_coe, vecMul_one]

theorem contra_add (g : SpecialLinearGroup (Fin n) R) (φ ψ : Fin n → R) :
    contra g (φ + ψ) = contra g φ + contra g ψ :=
  add_vecMul _ φ ψ

theorem contra_smul (g : SpecialLinearGroup (Fin n) R) (c : R) (φ : Fin n → R) :
    contra g (c • φ) = c • contra g φ :=
  smul_vecMul c φ _

@[simp]
theorem contra_zero (g : SpecialLinearGroup (Fin n) R) : contra g (0 : Fin n → R) = 0 :=
  zero_vecMul _

theorem contra_inv_contra (g : SpecialLinearGroup (Fin n) R) (φ : Fin n → R) :
    contra g⁻¹ (contra g φ) = φ := by
  rw [← contra_mul, inv_mul_cancel, contra_one]

theorem contra_contra_inv (g : SpecialLinearGroup (Fin n) R) (φ : Fin n → R) :
    contra g (contra g⁻¹ φ) = φ := by
  rw [← contra_mul, mul_inv_cancel, contra_one]

theorem contra_injective (g : SpecialLinearGroup (Fin n) R) : Function.Injective (contra g) :=
  fun φ ψ h => by rw [← contra_inv_contra g φ, h, contra_inv_contra]

theorem contra_eq_zero_iff (g : SpecialLinearGroup (Fin n) R) {φ : Fin n → R} :
    contra g φ = 0 ↔ φ = 0 :=
  ⟨fun h => contra_injective g (h.trans (contra_zero g).symm), fun h => h ▸ contra_zero g⟩

theorem contra_tv {v φ : Fin n → R} (h : φ ⬝ᵥ v = 0) (ψ : Fin n → R) :
    contra (tv v φ) ψ = ψ - (ψ ⬝ᵥ v) • φ := by
  have h' : (-φ) ⬝ᵥ v = 0 := by rw [neg_dotProduct, h, neg_zero]
  rw [contra_def, tv_inv h, coe_tv h', vecMul_add, vecMul_one, vecMul_vecMulVec, smul_neg,
    sub_eq_add_neg]

theorem contra_tv_of_dotProduct_eq_zero {v φ ψ : Fin n → R} (hψ : ψ ⬝ᵥ v = 0) :
    contra (tv v φ) ψ = ψ := by
  by_cases h : φ ⬝ᵥ v = 0
  · rw [contra_tv h, hψ, zero_smul, sub_zero]
  · rw [tv_of_dotProduct_ne_zero h, contra_one]

theorem conj_tv (g : SpecialLinearGroup (Fin n) R) (v φ : Fin n → R) :
    g * tv v φ * g⁻¹ = tv ((g : Matrix (Fin n) (Fin n) R) *ᵥ v) (contra g φ) := by
  by_cases h : φ ⬝ᵥ v = 0
  · have h' : contra g φ ⬝ᵥ ((g : Matrix (Fin n) (Fin n) R) *ᵥ v) = 0 := by
      rw [contra_dotProduct_mulVec, h]
    refine Subtype.ext ?_
    rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, coe_tv h, coe_tv h', mul_add,
      mul_one, add_mul, sl_coe_mul_coe_inv, mul_vecMulVec, vecMulVec_mul, contra_def]
  · have h' : contra g φ ⬝ᵥ ((g : Matrix (Fin n) (Fin n) R) *ᵥ v) ≠ 0 := by
      rwa [contra_dotProduct_mulVec]
    rw [tv_of_dotProduct_ne_zero h, tv_of_dotProduct_ne_zero h', mul_one, mul_inv_cancel]

def pointGroup (v : Fin n → R) : Subgroup (SpecialLinearGroup (Fin n) R) where
  carrier := {g | ∃ φ : Fin n → R, φ ⬝ᵥ v = 0 ∧ tv v φ = g}
  mul_mem' := by
    rintro _ _ ⟨φ, h, rfl⟩ ⟨ψ, h', rfl⟩
    exact ⟨φ + ψ, by rw [add_dotProduct, h, h', add_zero], (tv_mul_tv_left h h').symm⟩
  one_mem' := ⟨0, zero_dotProduct v, tv_zero_right v⟩
  inv_mem' := by
    rintro _ ⟨φ, h, rfl⟩
    exact ⟨-φ, by rw [neg_dotProduct, h, neg_zero], (tv_inv h).symm⟩

def hyperplaneGroup (φ : Fin n → R) : Subgroup (SpecialLinearGroup (Fin n) R) where
  carrier := {g | ∃ v : Fin n → R, φ ⬝ᵥ v = 0 ∧ tv v φ = g}
  mul_mem' := by
    rintro _ _ ⟨v, h, rfl⟩ ⟨w, h', rfl⟩
    exact ⟨v + w, by rw [dotProduct_add, h, h', add_zero], (tv_mul_tv_right h h').symm⟩
  one_mem' := ⟨0, dotProduct_zero φ, tv_zero_left φ⟩
  inv_mem' := by
    rintro _ ⟨v, h, rfl⟩
    refine ⟨-v, by rw [dotProduct_neg, h, neg_zero], ?_⟩
    rw [tv_inv h, tv_neg_left]

theorem mem_pointGroup {v : Fin n → R} {g : SpecialLinearGroup (Fin n) R} :
    g ∈ pointGroup v ↔ ∃ φ : Fin n → R, φ ⬝ᵥ v = 0 ∧ tv v φ = g :=
  Iff.rfl

theorem mem_hyperplaneGroup {φ : Fin n → R} {g : SpecialLinearGroup (Fin n) R} :
    g ∈ hyperplaneGroup φ ↔ ∃ v : Fin n → R, φ ⬝ᵥ v = 0 ∧ tv v φ = g :=
  Iff.rfl

theorem tv_mem_pointGroup (v φ : Fin n → R) : tv v φ ∈ pointGroup v := by
  by_cases h : φ ⬝ᵥ v = 0
  · exact ⟨φ, h, rfl⟩
  · rw [tv_of_dotProduct_ne_zero h]
    exact (pointGroup v).one_mem

theorem tv_mem_hyperplaneGroup (v φ : Fin n → R) : tv v φ ∈ hyperplaneGroup φ := by
  by_cases h : φ ⬝ᵥ v = 0
  · exact ⟨v, h, rfl⟩
  · rw [tv_of_dotProduct_ne_zero h]
    exact (hyperplaneGroup φ).one_mem

theorem pointGroup_commute {v : Fin n → R} {a b : SpecialLinearGroup (Fin n) R}
    (ha : a ∈ pointGroup v) (hb : b ∈ pointGroup v) : Commute a b := by
  obtain ⟨φ, h, rfl⟩ := ha
  obtain ⟨ψ, h', rfl⟩ := hb
  rw [Commute, SemiconjBy, tv_mul_tv_left h h', tv_mul_tv_left h' h, add_comm]

theorem conj_mem_pointGroup (g : SpecialLinearGroup (Fin n) R) {v : Fin n → R}
    {a : SpecialLinearGroup (Fin n) R} (ha : a ∈ pointGroup v) :
    g * a * g⁻¹ ∈ pointGroup ((g : Matrix (Fin n) (Fin n) R) *ᵥ v) := by
  obtain ⟨φ, -, rfl⟩ := ha
  rw [conj_tv]
  exact tv_mem_pointGroup _ _

theorem conj_mem_hyperplaneGroup (g : SpecialLinearGroup (Fin n) R) {φ : Fin n → R}
    {a : SpecialLinearGroup (Fin n) R} (ha : a ∈ hyperplaneGroup φ) :
    g * a * g⁻¹ ∈ hyperplaneGroup (contra g φ) := by
  obtain ⟨v, -, rfl⟩ := ha
  rw [conj_tv]
  exact tv_mem_hyperplaneGroup _ _

theorem pointGroup_map_conj (g : SpecialLinearGroup (Fin n) R) (v : Fin n → R) :
    (pointGroup v).map (MulAut.conj g).toMonoidHom =
      pointGroup ((g : Matrix (Fin n) (Fin n) R) *ᵥ v) := by
  ext b
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine ⟨fun ⟨a, ha, hab⟩ => hab ▸ conj_mem_pointGroup g ha, fun hb => ?_⟩
  refine ⟨g⁻¹ * b * g⁻¹⁻¹, ?_, by group⟩
  have h := conj_mem_pointGroup g⁻¹ hb
  rwa [sl_inv_mulVec_mulVec] at h

theorem hyperplaneGroup_map_conj (g : SpecialLinearGroup (Fin n) R) (φ : Fin n → R) :
    (hyperplaneGroup φ).map (MulAut.conj g).toMonoidHom = hyperplaneGroup (contra g φ) := by
  ext b
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine ⟨fun ⟨a, ha, hab⟩ => hab ▸ conj_mem_hyperplaneGroup g ha, fun hb => ?_⟩
  refine ⟨g⁻¹ * b * g⁻¹⁻¹, ?_, by group⟩
  have h := conj_mem_hyperplaneGroup g⁻¹ hb
  rwa [contra_inv_contra] at h

def transvectionSet (n : ℕ) (R : Type*) [CommRing R] : Set (SpecialLinearGroup (Fin n) R) :=
  {g | ∃ v φ : Fin n → R, v ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ v = 0 ∧ tv v φ = g}

theorem mem_transvectionSet {g : SpecialLinearGroup (Fin n) R} :
    g ∈ transvectionSet n R ↔ ∃ v φ : Fin n → R, v ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ v = 0 ∧ tv v φ = g :=
  Iff.rfl

theorem tv_mem_transvectionSet {v φ : Fin n → R} (hv : v ≠ 0) (hφ : φ ≠ 0) (h : φ ⬝ᵥ v = 0) :
    tv v φ ∈ transvectionSet n R :=
  ⟨v, φ, hv, hφ, h, rfl⟩

theorem eq_one_or_mem_transvectionSet_of_mem_pointGroup {v : Fin n → R}
    {a : SpecialLinearGroup (Fin n) R} (ha : a ∈ pointGroup v) :
    a = 1 ∨ a ∈ transvectionSet n R := by
  obtain ⟨φ, h, rfl⟩ := ha
  by_cases hv : v = 0
  · exact .inl (by rw [hv, tv_zero_left])
  by_cases hφ : φ = 0
  · exact .inl (by rw [hφ, tv_zero_right])
  exact .inr (tv_mem_transvectionSet hv hφ h)

theorem eq_one_or_mem_transvectionSet_of_mem_hyperplaneGroup {φ : Fin n → R}
    {a : SpecialLinearGroup (Fin n) R} (ha : a ∈ hyperplaneGroup φ) :
    a = 1 ∨ a ∈ transvectionSet n R := by
  obtain ⟨v, h, rfl⟩ := ha
  exact eq_one_or_mem_transvectionSet_of_mem_pointGroup (tv_mem_pointGroup v φ)

theorem mem_transvectionSet_of_mem_pointGroup {v : Fin n → R}
    {a : SpecialLinearGroup (Fin n) R} (ha : a ∈ pointGroup v) (h1 : a ≠ 1) :
    a ∈ transvectionSet n R :=
  (eq_one_or_mem_transvectionSet_of_mem_pointGroup ha).resolve_left h1

theorem mem_transvectionSet_of_mem_hyperplaneGroup {φ : Fin n → R}
    {a : SpecialLinearGroup (Fin n) R} (ha : a ∈ hyperplaneGroup φ) (h1 : a ≠ 1) :
    a ∈ transvectionSet n R :=
  (eq_one_or_mem_transvectionSet_of_mem_hyperplaneGroup ha).resolve_left h1

theorem conj_mem_transvectionSet (g : SpecialLinearGroup (Fin n) R)
    {a : SpecialLinearGroup (Fin n) R} (ha : a ∈ transvectionSet n R) :
    g * a * g⁻¹ ∈ transvectionSet n R := by
  obtain ⟨v, φ, hv, hφ, h, rfl⟩ := ha
  rw [conj_tv]
  refine tv_mem_transvectionSet ?_ ?_ (by rw [contra_dotProduct_mulVec, h])
  · exact fun h0 => hv ((sl_mulVec_eq_zero_iff g).mp h0)
  · exact fun h0 => hφ ((contra_eq_zero_iff g).mp h0)

section Field

variable {F : Type*} [Field F]

theorem pointGroup_sup_hyperplaneGroup (i : Fin n) :
    pointGroup (Pi.single i (1 : F)) ⊔ hyperplaneGroup (Pi.single i (1 : F)) = ⊤ := by
  set H := pointGroup (Pi.single i (1 : F)) ⊔ hyperplaneGroup (Pi.single i (1 : F))
  have hA : ∀ {j : Fin n} (hij : i ≠ j) (c : F), SpecialLinearGroup.transvection hij c ∈ H :=
    fun hij c => Subgroup.mem_sup_left (by
      rw [transvection_eq_tv']
      exact tv_mem_pointGroup _ _)
  have hB : ∀ {j : Fin n} (hji : j ≠ i) (c : F), SpecialLinearGroup.transvection hji c ∈ H :=
    fun hji c => Subgroup.mem_sup_right (by
      rw [transvection_eq_tv]
      exact tv_mem_hyperplaneGroup _ _)
  rw [eq_top_iff,
    ← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin n) (K := F),
    Subgroup.closure_le]
  rintro _ ⟨⟨j, k, hjk, c⟩, rfl⟩
  rw [TransvectionStruct.toSpecialLinearGroup_mk]
  by_cases hj : j = i
  · subst hj
    exact hA hjk c
  by_cases hk : k = i
  · subst hk
    exact hB hjk c
  have hcomm := SpecialLinearGroup.commutatorElement_transvection hj (Ne.symm hk) hjk c (1 : F)
  rw [mul_one] at hcomm
  rw [← hcomm, commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem (hB hj c) (hA (Ne.symm hk) 1))
    (H.inv_mem (hB hj c))) (H.inv_mem (hA (Ne.symm hk) 1))

theorem transvection_mem_transvectionSet {i j : Fin n} (hij : i ≠ j) {c : F} (hc : c ≠ 0) :
    SpecialLinearGroup.transvection hij c ∈ transvectionSet n F := by
  rw [transvection_eq_tv]
  exact tv_mem_transvectionSet (Pi.single_ne_zero_iff.mpr hc)
    (Pi.single_ne_zero_iff.mpr one_ne_zero)
    (by rw [single_dotProduct, one_mul, Pi.single_eq_of_ne hij.symm])

theorem closure_transvectionSet : Subgroup.closure (transvectionSet n F) = ⊤ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  set i : Fin n := ⟨0, hn⟩
  rw [eq_top_iff, ← pointGroup_sup_hyperplaneGroup i, sup_le_iff]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · rcases eq_one_or_mem_transvectionSet_of_mem_pointGroup ha with rfl | h
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure h
  · rcases eq_one_or_mem_transvectionSet_of_mem_hyperplaneGroup ha with rfl | h
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure h

end Field

end CFSG.LargeExtraspecial.A2Mod
