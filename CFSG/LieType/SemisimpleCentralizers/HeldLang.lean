module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.Hilbert90
public import CFSG.LieType.SemisimpleCentralizers.HeldLangCentral

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open Matrix CFSG.HardMathSupport.Foote.ModuleExclusions

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev glMap (σ : F ≃+* F) : GL ι F →* GL ι F :=
  Matrix.GeneralLinearGroup.map (σ : F →+* F)

theorem coe_glMap (σ : F ≃+* F) (g : GL ι F) :
    ((glMap σ g : GL ι F) : Matrix ι ι F) = (g : Matrix ι ι F).map σ := rfl

@[expose] def normProd (σ : F ≃+* F) (g : GL ι F) : ℕ → GL ι F
  | 0 => 1
  | k + 1 => g * glMap σ (normProd σ g k)

theorem coe_normProd (σ : F ≃+* F) (g : GL ι F) (k : ℕ) :
    ((normProd σ g k : GL ι F) : Matrix ι ι F) = Ai σ (g : Matrix ι ι F) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (g : Matrix ι ι F) * ((normProd σ g k : GL ι F) : Matrix ι ι F).map σ = _
    rw [ih]
    rfl

theorem scalar_mul_comm (l : Fˣ) (g : GL ι F) :
    Matrix.GeneralLinearGroup.scalar ι l * g = g * Matrix.GeneralLinearGroup.scalar ι l := by
  ext i j
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    mul_comm]

theorem exists_inv_mul_glMap [Finite F] (σ : F ≃+* F) (g : GL ι F)
    (hg : normProd σ g (orderOf σ) = 1) : ∃ y : GL ι F, g = y⁻¹ * glMap σ y := by
  have hr0 : 0 < orderOf σ := orderOf_pos σ
  have hAi : Ai σ (g : Matrix ι ι F) (orderOf σ) = 1 := by
    rw [← coe_normProd, hg]; rfl
  obtain ⟨B, hB, hgB⟩ := speiser σ (g : Matrix ι ι F) (orderOf σ) rfl hr0 hAi
  obtain ⟨u, hu⟩ : IsUnit B :=
    (Matrix.isUnit_iff_isUnit_det B).2 (isUnit_iff_ne_zero.2 hB)
  refine ⟨u⁻¹, ?_⟩
  have h1 : g * glMap σ u = u := Units.ext (by rw [Units.val_mul, coe_glMap, hu]; exact hgB)
  rw [inv_inv, map_inv]
  exact eq_mul_inv_of_mul_eq h1

theorem exists_smul_eq_inv_mul_glMap [Finite F] [Nonempty ι] (σ : F ≃+* F) (g : GL ι F) (c : F)
    (hg : Ai σ (g : Matrix ι ι F) (orderOf σ) = c • (1 : Matrix ι ι F)) :
    ∃ (l : Fˣ) (y : GL ι F), Matrix.GeneralLinearGroup.scalar ι l * g = y⁻¹ * glMap σ y := by
  obtain ⟨l, B, hl, hB, hlB⟩ := hilbert90_matrix σ (g : Matrix ι ι F) g.det_ne_zero c hg
  obtain ⟨u, hu⟩ : IsUnit B :=
    (Matrix.isUnit_iff_isUnit_det B).2 (isUnit_iff_ne_zero.2 hB)
  refine ⟨Units.mk0 l hl, u⁻¹, ?_⟩
  have h1 : Matrix.GeneralLinearGroup.scalar ι (Units.mk0 l hl) * g * glMap σ u = u := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_glMap, hu, Matrix.GeneralLinearGroup.coe_scalar]
    simpa [Matrix.smul_eq_diagonal_mul] using hlB
  rw [inv_inv, map_inv]
  exact eq_mul_inv_of_mul_eq h1

theorem twist_eq_conj_of_eq (σ : F ≃+* F) {g y : GL ι F} (h : g = y⁻¹ * glMap σ y) (x : GL ι F) :
    g * glMap σ x * g⁻¹ = y⁻¹ * glMap σ (y * x * y⁻¹) * y := by
  subst h
  simp only [map_mul, map_inv]
  group

theorem twist_eq_conj_of_smul (σ : F ≃+* F) {g y : GL ι F} (l : Fˣ)
    (h : Matrix.GeneralLinearGroup.scalar ι l * g = y⁻¹ * glMap σ y) (x : GL ι F) :
    g * glMap σ x * g⁻¹ = y⁻¹ * glMap σ (y * x * y⁻¹) * y := by
  rw [← twist_eq_conj_of_eq σ h x]
  set s := Matrix.GeneralLinearGroup.scalar ι l
  have hs : ∀ z : GL ι F, s * z * s⁻¹ = z := fun z => by
    rw [scalar_mul_comm l z, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : s * g * glMap σ x * (s * g)⁻¹ = s * (g * glMap σ x * g⁻¹) * s⁻¹ := by group
  rw [h2, hs]

theorem exists_twist_eq_conj [Finite F] [Nonempty ι] (σ : F ≃+* F) (g : GL ι F) (c : F)
    (hg : Ai σ (g : Matrix ι ι F) (orderOf σ) = c • (1 : Matrix ι ι F)) :
    ∃ y : GL ι F, ∀ x : GL ι F, g * glMap σ x * g⁻¹ = y⁻¹ * glMap σ (y * x * y⁻¹) * y := by
  obtain ⟨l, y, hy⟩ := exists_smul_eq_inv_mul_glMap σ g c hg
  exact ⟨y, twist_eq_conj_of_smul σ l hy⟩

@[expose] def fixField (σ : F ≃+* F) : Subfield F := FixedPoints.subfield (Subgroup.zpowers σ) F

theorem mem_fixField {σ : F ≃+* F} {x : F} : x ∈ fixField σ ↔ σ x = x :=
  ⟨fun h => h ⟨σ, Subgroup.mem_zpowers σ⟩, mem_fixedPoints_subfield_of_apply_eq σ x⟩

abbrev glFix (σ : F ≃+* F) : Subgroup (GL ι F) := fixHom (glMap σ)

theorem mem_glFix {σ : F ≃+* F} {x : GL ι F} : x ∈ glFix σ ↔ glMap σ x = x := Iff.rfl

theorem mem_glFix_iff {σ : F ≃+* F} {x : GL ι F} : x ∈ glFix σ ↔ ∀ i j, σ (x i j) = x i j := by
  rw [mem_glFix, Units.ext_iff, coe_glMap]
  constructor
  · intro h i j
    exact congrFun (congrFun h i) j
  · intro h
    ext i j
    exact h i j

@[expose] def glFixEmb (σ : F ≃+* F) : GL ι (fixField σ) →* GL ι F :=
  Matrix.GeneralLinearGroup.map (fixField σ).subtype

theorem glFixEmb_apply (σ : F ≃+* F) (x : GL ι (fixField σ)) (i j : ι) :
    (glFixEmb σ x : GL ι F) i j = ((x i j : fixField σ) : F) := by
  simp [glFixEmb, Matrix.GeneralLinearGroup.map_apply]

theorem glFixEmb_injective (σ : F ≃+* F) : Function.Injective (glFixEmb (ι := ι) σ) := by
  intro x y h
  apply Units.ext
  ext i j
  have := congrFun (congrFun (congrArg (fun z : GL ι F => (z : Matrix ι ι F)) h) i) j
  simpa [glFixEmb_apply] using this

theorem glFixEmb_mem (σ : F ≃+* F) (x : GL ι (fixField σ)) : glFixEmb σ x ∈ glFix σ := by
  rw [mem_glFix_iff]
  intro i j
  rw [glFixEmb_apply]
  exact mem_fixField.1 (x i j).2

theorem glFixEmb_range (σ : F ≃+* F) : (glFixEmb (ι := ι) σ).range = glFix σ := by
  refine le_antisymm (by rintro _ ⟨x, rfl⟩; exact glFixEmb_mem σ x) fun x hx => ?_
  have hx' : x⁻¹ ∈ glFix σ := Subgroup.inv_mem _ hx
  rw [mem_glFix_iff] at hx hx'
  let M : Matrix ι ι (fixField σ) := Matrix.of fun i j => ⟨x i j, mem_fixField.2 (hx i j)⟩
  let M' : Matrix ι ι (fixField σ) := Matrix.of fun i j => ⟨(x⁻¹ : GL ι F) i j, mem_fixField.2 (hx' i j)⟩
  have hM : M.map (fixField σ).subtype = (x : Matrix ι ι F) := by ext i j; rfl
  have hM' : M'.map (fixField σ).subtype = ((x⁻¹ : GL ι F) : Matrix ι ι F) := by ext i j; rfl
  have hinj : Function.Injective (fun N : Matrix ι ι (fixField σ) => N.map (fixField σ).subtype) :=
    Matrix.map_injective (fixField σ).subtype_injective
  have h1 : M * M' = 1 := by
    apply hinj
    simp only [Matrix.map_mul, hM, hM', ← Units.val_mul, mul_inv_cancel, Units.val_one]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have h2 : M' * M = 1 := by
    apply hinj
    simp only [Matrix.map_mul, hM, hM', ← Units.val_mul, inv_mul_cancel, Units.val_one]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  refine ⟨⟨M, M', h1, h2⟩, ?_⟩
  apply Units.ext
  ext i j
  rw [glFixEmb_apply]
  rfl

end CFSG.LieType.SemisimpleCentralizers.HeldLang
