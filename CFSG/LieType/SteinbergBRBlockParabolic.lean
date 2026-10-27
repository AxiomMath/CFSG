module

public import CFSG.Assembly.Defs

public section

namespace CFSG.LieType.SteinbergBR.BlockPar

open Matrix

variable {F : Type*} [Field F] {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a]
  [DecidableEq b]

@[expose] def grade : a ⊕ b → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)

omit [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] in
theorem blockTriangular_iff (M : Matrix (a ⊕ b) (a ⊕ b) F) :
    M.BlockTriangular grade ↔ M.toBlocks₂₁ = 0 := by
  constructor
  · intro h
    ext i j
    exact h (show grade (Sum.inl j : a ⊕ b) < grade (Sum.inr i : a ⊕ b) by simp [grade])
  · intro h i j hij
    rcases i with i | i <;> rcases j with j | j
    · exact absurd hij (by simp [grade])
    · exact absurd hij (by simp [grade])
    · exact congrFun₂ h i j
    · exact absurd hij (by simp [grade])

theorem coe_inv_eq_inv (g : SpecialLinearGroup (a ⊕ b) F) :
    (g⁻¹).val =
      g.val⁻¹ := by
  have h : g.val * (g⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel g)
  exact (Matrix.inv_eq_right_inv h).symm

@[expose] def parQ : Subgroup (SpecialLinearGroup (a ⊕ b) F) where
  carrier := {g | g.val.toBlocks₂₁ = 0}
  one_mem' := by
    ext i j
    simp [toBlocks₂₁]
  mul_mem' {g h} hg hh := by
    change (g * h).val.toBlocks₂₁ = 0
    have hg' : g.val.toBlocks₂₁ = 0 := hg
    have hh' : h.val.toBlocks₂₁ = 0 := hh
    rw [← blockTriangular_iff] at hg' hh' ⊢
    exact hg'.mul hh'
  inv_mem' {g} hg := by
    change (g⁻¹).val.toBlocks₂₁ = 0
    have hg' : g.val.toBlocks₂₁ = 0 := hg
    rw [← blockTriangular_iff] at hg' ⊢
    have := Matrix.invertibleOfIsUnitDet g.val (by rw [g.prop]; exact isUnit_one)
    rw [coe_inv_eq_inv]
    exact blockTriangular_inv_of_blockTriangular hg'

theorem mem_parQ {g : SpecialLinearGroup (a ⊕ b) F} :
    g ∈ parQ ↔ g.val.toBlocks₂₁ = 0 :=
  Iff.rfl

theorem eq_fromBlocks_of_mem_parQ {g : SpecialLinearGroup (a ⊕ b) F} (hg : g ∈ parQ) :
    g.val = fromBlocks g.val.toBlocks₁₁
      g.val.toBlocks₁₂ 0 g.val.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks g.val]
  rw [show g.val.toBlocks₂₁ = 0 from hg]

theorem toBlocks₁₁_mul {g h : SpecialLinearGroup (a ⊕ b) F} (hh : h ∈ parQ) :
    (g * h).val.toBlocks₁₁ =
      g.val.toBlocks₁₁ * h.val.toBlocks₁₁ := by
  change (g.val * h.val).toBlocks₁₁ = _
  conv_lhs => rw [← fromBlocks_toBlocks g.val, ← fromBlocks_toBlocks h.val]
  rw [fromBlocks_multiply, toBlocks_fromBlocks₁₁, show h.val.toBlocks₂₁ = 0
    from hh, Matrix.mul_zero, add_zero]

theorem toBlocks₂₂_mul {g h : SpecialLinearGroup (a ⊕ b) F} (hg : g ∈ parQ) :
    (g * h).val.toBlocks₂₂ =
      g.val.toBlocks₂₂ * h.val.toBlocks₂₂ := by
  change (g.val * h.val).toBlocks₂₂ = _
  conv_lhs => rw [← fromBlocks_toBlocks g.val, ← fromBlocks_toBlocks h.val]
  rw [fromBlocks_multiply, toBlocks_fromBlocks₂₂, show g.val.toBlocks₂₁ = 0
    from hg, Matrix.zero_mul, zero_add]

theorem det_eq_of_mem_parQ {g : SpecialLinearGroup (a ⊕ b) F} (hg : g ∈ parQ) :
    g.val.toBlocks₁₁.det *
      g.val.toBlocks₂₂.det = 1 := by
  rw [← det_fromBlocks_zero₂₁ _ g.val.toBlocks₁₂, ←
    eq_fromBlocks_of_mem_parQ hg]
  exact g.prop

variable (F) in
@[expose] def uniMat (X : Matrix a b F) : Matrix (a ⊕ b) (a ⊕ b) F :=
  fromBlocks 1 X 0 1

theorem det_uniMat (X : Matrix a b F) : (uniMat F X).det = 1 := by
  rw [uniMat, det_fromBlocks_zero₂₁, det_one, det_one, mul_one]

theorem uniMat_add (X Y : Matrix a b F) : uniMat F (X + Y) = uniMat F X * uniMat F Y := by
  rw [uniMat, uniMat, uniMat, fromBlocks_multiply]
  simp [add_comm]

variable (a b F) in
@[expose] def uniHom : Multiplicative (Matrix a b F) →* SpecialLinearGroup (a ⊕ b) F where
  toFun x := ⟨uniMat F (Multiplicative.toAdd x), det_uniMat _⟩
  map_one' := Subtype.ext (by simp [uniMat, fromBlocks_one])
  map_mul' x y := Subtype.ext (uniMat_add _ _)

theorem uniHom_val (X : Matrix a b F) :
    (uniHom F a b (Multiplicative.ofAdd X)).val = fromBlocks 1 X 0 1 :=
  rfl

theorem uniHom_injective : Function.Injective (uniHom F a b) := by
  intro x y hxy
  have h : (fromBlocks 1 (Multiplicative.toAdd x) 0 1 : Matrix (a ⊕ b) (a ⊕ b) F).toBlocks₁₂ =
      (fromBlocks 1 (Multiplicative.toAdd y) 0 1 : Matrix (a ⊕ b) (a ⊕ b) F).toBlocks₁₂ :=
    congrArg (fun g : SpecialLinearGroup (a ⊕ b) F => g.val.toBlocks₁₂) hxy
  rw [toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₁₂] at h
  exact Multiplicative.toAdd.injective h

theorem uniHom_mem_parQ (x : Multiplicative (Matrix a b F)) : uniHom F a b x ∈ parQ := by
  change (uniMat F (Multiplicative.toAdd x)).toBlocks₂₁ = 0
  simp [uniMat]

variable (a F) in
@[expose] def levR : SpecialLinearGroup b F →* SpecialLinearGroup (a ⊕ b) F where
  toFun D := ⟨fromBlocks 1 0 0 D.val, by rw [det_fromBlocks_zero₂₁, det_one, D.prop, one_mul]⟩
  map_one' := Subtype.ext (by simp [fromBlocks_one])
  map_mul' D E := Subtype.ext (by
    change fromBlocks 1 0 0 (D.val * E.val) = fromBlocks 1 0 0 D.val * fromBlocks 1 0 0 E.val
    rw [fromBlocks_multiply]
    simp)

variable (b F) in
@[expose] def levL : SpecialLinearGroup a F →* SpecialLinearGroup (a ⊕ b) F where
  toFun A := ⟨fromBlocks A.val 0 0 1, by rw [det_fromBlocks_zero₂₁, det_one, A.prop, one_mul]⟩
  map_one' := Subtype.ext (by simp [fromBlocks_one])
  map_mul' A E := Subtype.ext (by
    change fromBlocks (A.val * E.val) 0 0 1 = fromBlocks A.val 0 0 1 * fromBlocks E.val 0 0 1
    rw [fromBlocks_multiply]
    simp)

theorem levR_val (D : SpecialLinearGroup b F) : (levR F a D).val = fromBlocks 1 0 0 D.val :=
  rfl

theorem levL_val (A : SpecialLinearGroup a F) : (levL F b A).val = fromBlocks A.val 0 0 1 :=
  rfl

theorem levR_injective : Function.Injective (levR F a : SpecialLinearGroup b F →* _) := by
  intro D E h
  apply Subtype.ext
  have h' : (fromBlocks 1 0 0 D.val : Matrix (a ⊕ b) (a ⊕ b) F).toBlocks₂₂ =
      (fromBlocks 1 0 0 E.val : Matrix (a ⊕ b) (a ⊕ b) F).toBlocks₂₂ :=
    congrArg (fun g : SpecialLinearGroup (a ⊕ b) F => g.val.toBlocks₂₂) h
  rwa [toBlocks_fromBlocks₂₂, toBlocks_fromBlocks₂₂] at h'

theorem levL_injective : Function.Injective (levL F b : SpecialLinearGroup a F →* _) := by
  intro A E h
  apply Subtype.ext
  have h' : (fromBlocks A.val 0 0 1 : Matrix (a ⊕ b) (a ⊕ b) F).toBlocks₁₁ =
      (fromBlocks E.val 0 0 1 : Matrix (a ⊕ b) (a ⊕ b) F).toBlocks₁₁ :=
    congrArg (fun g : SpecialLinearGroup (a ⊕ b) F => g.val.toBlocks₁₁) h
  rwa [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₁] at h'

theorem inv_val_mul_val {c : Type*} [Fintype c] [DecidableEq c] (D : SpecialLinearGroup c F) :
    (D⁻¹).val * D.val = 1 :=
  congrArg Subtype.val (inv_mul_cancel D)

theorem val_mul_inv_val {c : Type*} [Fintype c] [DecidableEq c] (D : SpecialLinearGroup c F) :
    D.val * (D⁻¹).val = 1 :=
  congrArg Subtype.val (mul_inv_cancel D)

theorem levR_conj_uni (D : SpecialLinearGroup b F) (X : Matrix a b F) :
    levR F a D * uniHom F a b (Multiplicative.ofAdd X) * (levR F a D)⁻¹ =
      uniHom F a b (Multiplicative.ofAdd (X * (D⁻¹).val)) := by
  apply Subtype.ext
  rw [← map_inv]
  change fromBlocks 1 0 0 D.val * fromBlocks 1 X 0 1 * fromBlocks 1 0 0 (D⁻¹).val =
    fromBlocks 1 (X * (D⁻¹).val) 0 1
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    val_mul_inv_val]

theorem levL_conj_uni (A : SpecialLinearGroup a F) (X : Matrix a b F) :
    levL F b A * uniHom F a b (Multiplicative.ofAdd X) * (levL F b A)⁻¹ =
      uniHom F a b (Multiplicative.ofAdd (A.val * X)) := by
  apply Subtype.ext
  rw [← map_inv]
  change fromBlocks A.val 0 0 1 * fromBlocks 1 X 0 1 * fromBlocks (A⁻¹).val 0 0 1 =
    fromBlocks 1 (A.val * X) 0 1
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    val_mul_inv_val]

end CFSG.LieType.SteinbergBR.BlockPar
