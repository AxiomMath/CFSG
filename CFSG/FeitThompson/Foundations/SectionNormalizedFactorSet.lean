module

public import CFSG.FeitThompson.Foundations.QuotientActsOnAbelianNormal
public import CFSG.FeitThompson.Foundations.NormalizedSectionCoordinates

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G] {A : Subgroup G} [A.Normal] [IsMulCommutative ↥A]
  {s : G ⧸ A → G}

omit [IsMulCommutative ↥A] in
theorem mul_mul_inv_mem_of_section (hs : ∀ x, ((s x : G) : G ⧸ A) = x) (x y : G ⧸ A) :
    s x * s y * (s (x * y))⁻¹ ∈ A := by
  rw [← QuotientGroup.eq_one_iff]
  simp [hs]

def sectionFactorSet (hs : ∀ x, ((s x : G) : G ⧸ A) = x) (x y : G ⧸ A) : Additive ↥A :=
  Additive.ofMul ⟨s x * s y * (s (x * y))⁻¹, mul_mul_inv_mem_of_section hs x y⟩

omit [IsMulCommutative ↥A] in
@[simp] theorem coe_toMul_sectionFactorSet (hs : ∀ x, ((s x : G) : G ⧸ A) = x) (x y : G ⧸ A) :
    (((sectionFactorSet hs x y).toMul : ↥A) : G) = s x * s y * (s (x * y))⁻¹ := (rfl)

omit [IsMulCommutative ↥A] in
theorem coe_toMul_sectionFactorSet_mul_section (hs : ∀ x, ((s x : G) : G ⧸ A) = x) (x y : G ⧸ A) :
    (((sectionFactorSet hs x y).toMul : ↥A) : G) * s (x * y) = s x * s y := by
  simp [mul_assoc]

omit [IsMulCommutative ↥A] in
theorem sectionFactorSet_one_left (hs1 : s 1 = 1) (hs : ∀ x, ((s x : G) : G ⧸ A) = x)
    (x : G ⧸ A) : sectionFactorSet hs 1 x = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  simp [hs1]

omit [IsMulCommutative ↥A] in
theorem sectionFactorSet_one_right (hs1 : s 1 = 1) (hs : ∀ x, ((s x : G) : G ⧸ A) = x)
    (x : G ⧸ A) : sectionFactorSet hs x 1 = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  simp [hs1]

theorem sectionFactorSet_cocycle (hs : ∀ x, ((s x : G) : G ⧸ A) = x) (x y z : G ⧸ A) :
    sectionFactorSet hs x y + sectionFactorSet hs (x * y) z
      = x • sectionFactorSet hs y z + sectionFactorSet hs x (y * z) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  have hx : x • sectionFactorSet hs y z = ((s x : G) : G ⧸ A) • sectionFactorSet hs y z := by
    rw [hs]
  rw [hx]
  simp [mul_assoc]

noncomputable def normalizedSectionFactorSet (A : Subgroup G) [A.Normal] [IsMulCommutative ↥A] :
    (G ⧸ A) → (G ⧸ A) → Additive ↥A :=
  sectionFactorSet (mk_normalizedSection A)

theorem normalizedSectionFactorSet_eq (A : Subgroup G) [A.Normal] [IsMulCommutative ↥A] :
    normalizedSectionFactorSet A = sectionFactorSet (mk_normalizedSection A) := (rfl)

theorem coe_toMul_normalizedSectionFactorSet (A : Subgroup G) [A.Normal] [IsMulCommutative ↥A]
    (x y : G ⧸ A) : (((normalizedSectionFactorSet A x y).toMul : ↥A) : G)
      = normalizedSection A x * normalizedSection A y * (normalizedSection A (x * y))⁻¹ := by
  rw [normalizedSectionFactorSet_eq, coe_toMul_sectionFactorSet]

@[simp] theorem normalizedSectionFactorSet_one_left (A : Subgroup G) [A.Normal]
    [IsMulCommutative ↥A] (x : G ⧸ A) : normalizedSectionFactorSet A 1 x = 0 :=
  sectionFactorSet_one_left (normalizedSection_one A) (mk_normalizedSection A) x

@[simp] theorem normalizedSectionFactorSet_one_right (A : Subgroup G) [A.Normal]
    [IsMulCommutative ↥A] (x : G ⧸ A) : normalizedSectionFactorSet A x 1 = 0 :=
  sectionFactorSet_one_right (normalizedSection_one A) (mk_normalizedSection A) x

theorem normalizedSectionFactorSet_cocycle (A : Subgroup G) [A.Normal] [IsMulCommutative ↥A]
    (x y z : G ⧸ A) :
    normalizedSectionFactorSet A x y + normalizedSectionFactorSet A (x * y) z
      = x • normalizedSectionFactorSet A y z + normalizedSectionFactorSet A x (y * z) :=
  sectionFactorSet_cocycle (mk_normalizedSection A) x y z

end CFSG.FeitThompson
