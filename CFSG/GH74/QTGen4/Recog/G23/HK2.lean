module

public import CFSG.GH74.QTGen4.Recog.G23.HK
public meta import Mathlib.Data.ZMod.Defs
public meta import Mathlib.Algebra.Field.ZMod
public meta import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.Quasithin.G23Type

variable {G : Type} [Group G]

theorem sl_prod_order3 : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 3), A.det = 1 →
    ∃ B₁ ∈ Finset.univ.filter (fun B : Matrix (Fin 2) (Fin 2) (ZMod 3) =>
      B.det = 1 ∧ B * B * B = 1),
    ∃ B₂ ∈ Finset.univ.filter (fun B : Matrix (Fin 2) (Fin 2) (ZMod 3) =>
      B.det = 1 ∧ B * B * B = 1),
    ∃ B₃ ∈ Finset.univ.filter (fun B : Matrix (Fin 2) (Fin 2) (ZMod 3) =>
      B.det = 1 ∧ B * B * B = 1),
    ∃ B₄ ∈ Finset.univ.filter (fun B : Matrix (Fin 2) (Fin 2) (ZMod 3) =>
      B.det = 1 ∧ B * B * B = 1),
    A = B₁ * B₂ * B₃ * B₄ := by
  let letter : Fin 5 → Matrix (Fin 2) (Fin 2) (ZMod 3) :=
    ![!![1, 1; 0, 1], !![1, 2; 0, 1], !![1, 0; 1, 1], !![1, 0; 2, 1], 1]
  let wordFor : Matrix (Fin 2) (Fin 2) (ZMod 3) → Fin 4 → Fin 5 := fun A =>
    match (A 0 0).val, (A 0 1).val, (A 1 0).val, (A 1 1).val with
    | 0, 1, 2, 0 => ![0, 3, 0, 4]
    | 0, 1, 2, 1 => ![0, 3, 4, 4]
    | 0, 1, 2, 2 => ![0, 3, 1, 4]
    | 0, 2, 1, 0 => ![1, 2, 1, 4]
    | 0, 2, 1, 1 => ![1, 2, 4, 4]
    | 0, 2, 1, 2 => ![1, 2, 0, 4]
    | 1, 0, 0, 1 => ![4, 4, 4, 4]
    | 1, 0, 1, 1 => ![2, 4, 4, 4]
    | 1, 0, 2, 1 => ![3, 4, 4, 4]
    | 1, 1, 0, 1 => ![0, 4, 4, 4]
    | 1, 1, 1, 2 => ![2, 0, 4, 4]
    | 1, 1, 2, 0 => ![3, 0, 4, 4]
    | 1, 2, 0, 1 => ![1, 4, 4, 4]
    | 1, 2, 1, 0 => ![2, 1, 4, 4]
    | 1, 2, 2, 2 => ![3, 1, 4, 4]
    | 2, 0, 0, 2 => ![0, 2, 0, 2]
    | 2, 0, 1, 2 => ![0, 2, 0, 4]
    | 2, 0, 2, 2 => ![1, 3, 1, 4]
    | 2, 1, 0, 2 => ![2, 0, 2, 4]
    | 2, 1, 1, 1 => ![0, 2, 4, 4]
    | 2, 1, 2, 0 => ![1, 3, 0, 4]
    | 2, 2, 0, 2 => ![3, 1, 3, 4]
    | 2, 2, 1, 0 => ![0, 2, 1, 4]
    | 2, 2, 2, 1 => ![1, 3, 4, 4]
    | _, _, _, _ => ![4, 4, 4, 4]
  let factors (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) (i : Fin 4) := letter (wordFor A i)
  have checked : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 3), A.det = 1 →
      (∀ i : Fin 4, (factors A i).det = 1 ∧
        factors A i * factors A i * factors A i = 1) ∧
      A = factors A 0 * factors A 1 * factors A 2 * factors A 3 := by
    dsimp only [factors, wordFor, letter]
    decide +kernel
  intro A hA
  refine ⟨factors A 0, ?_, factors A 1, ?_, factors A 2, ?_, factors A 3, ?_,
    (checked A hA).2⟩
  all_goals exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (checked A hA).1 _⟩

@[expose] def slOf (B : Matrix (Fin 2) (Fin 2) (ZMod 3)) (hd : B.det = 1) :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) :=
  ⟨B, hd⟩

theorem slOf_val (B : Matrix (Fin 2) (Fin 2) (ZMod 3)) (hd : B.det = 1) :
    (slOf B hd).1 = B := rfl

theorem sl_hom_trivial {Y : Type*} [Group Y] (hY : ∀ y : Y, y ^ 2 = 1)
    (φ : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) →* Y)
    (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) : φ A = 1 := by
  have hB : ∀ (B : Matrix (Fin 2) (Fin 2) (ZMod 3)) (hd : B.det = 1), B * B * B = 1 →
      φ (slOf B hd) = 1 := by
    intro B hd hc
    have hc' : slOf B hd * slOf B hd * slOf B hd = 1 :=
      Subtype.ext (by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
          Matrix.SpecialLinearGroup.coe_one, slOf_val]
        exact hc)
    have h3 : φ (slOf B hd) * φ (slOf B hd) * φ (slOf B hd) = 1 := by
      rw [← map_mul, ← map_mul, hc', map_one]
    have h2 : φ (slOf B hd) * φ (slOf B hd) = 1 := by
      rw [← pow_two]; exact hY _
    have h1 : φ (slOf B hd) * φ (slOf B hd) * φ (slOf B hd) = φ (slOf B hd) := by
      rw [h2, one_mul]
    calc φ (slOf B hd) = φ (slOf B hd) * φ (slOf B hd) * φ (slOf B hd) := h1.symm
      _ = 1 := h3
  obtain ⟨B₁, hB₁, B₂, hB₂, B₃, hB₃, B₄, hB₄, hA⟩ := sl_prod_order3 A.1 A.2
  obtain ⟨-, d₁, c₁⟩ := Finset.mem_filter.mp hB₁
  obtain ⟨-, d₂, c₂⟩ := Finset.mem_filter.mp hB₂
  obtain ⟨-, d₃, c₃⟩ := Finset.mem_filter.mp hB₃
  obtain ⟨-, d₄, c₄⟩ := Finset.mem_filter.mp hB₄
  have hAS : A = slOf B₁ d₁ * slOf B₂ d₂ * slOf B₃ d₃ * slOf B₄ d₄ := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, slOf_val]
    exact hA
  rw [hAS, map_mul, map_mul, map_mul, hB B₁ d₁ c₁, hB B₂ d₂ c₂, hB B₃ d₃ c₃, hB B₄ d₄ c₄,
    one_mul, one_mul, one_mul]

theorem G23One.inf_comm {H H₁ H₂ : Subgroup G} (hH : G23One H H₁ H₂) {y₁ y₂ : G}
    (h₁ : y₁ ∈ H₁ ⊓ H₂) (h₂ : y₂ ∈ H₁ ⊓ H₂) : y₁ * y₂ = y₂ * y₁ := by
  obtain ⟨_, -, -, huniq⟩ := G23One.exists_unique_inf hH
  rcases huniq y₁ h₁ with h | h <;> rcases huniq y₂ h₂ with h' | h' <;> simp [h, h']

theorem G23One.sq_inf {H H₁ H₂ : Subgroup G} (hH : G23One H H₁ H₂) {y : G}
    (hy : y ∈ H₁ ⊓ H₂) : y ^ 2 = 1 := by
  obtain ⟨z, hzmem, hz1, huniq⟩ := G23One.exists_unique_inf hH
  rcases huniq y hy with h | h
  · rw [h]; simp
  · have hz2 : z * z ∈ H₁ ⊓ H₂ := (H₁ ⊓ H₂).mul_mem hzmem hzmem
    rw [h, pow_two]
    rcases huniq (z * z) hz2 with h' | h'
    · exact h'
    · exact absurd (mul_left_cancel (a := z) (b := z) (c := 1) (by rw [mul_one]; exact h')) hz1

theorem G23One.comm_one_two {H H₁ H₂ : Subgroup G} (hH : G23One H H₁ H₂) {a b : G}
    (ha : a ∈ H₁) (hb : b ∈ H₂) : a * b = b * a := by
  have haH : a ∈ H := hH.le_one ha
  have hmem : ∀ x ∈ H₂, a * x * a⁻¹ * x⁻¹ ∈ H₁ ⊓ H₂ := by
    intro x hx
    have hxH : x ∈ H := hH.le_two hx
    constructor
    · have h1 : x * a⁻¹ * x⁻¹ ∈ H₁ :=
        (Subgroup.mem_normalizer_iff.mp (hH.normal_one hxH) a⁻¹).mp (H₁.inv_mem ha)
      have h2 : a * x * a⁻¹ * x⁻¹ = a * (x * a⁻¹ * x⁻¹) := by group
      rw [h2]
      exact H₁.mul_mem ha h1
    · have h2 : a * x * a⁻¹ ∈ H₂ :=
        (Subgroup.mem_normalizer_iff.mp (hH.normal_two haH) x).mp hx
      exact H₂.mul_mem h2 (H₂.inv_mem hx)
  have hkey : ∀ x ∈ H₂, ∀ y ∈ H₂,
      a * (x * y) * a⁻¹ * (x * y)⁻¹ = (a * y * a⁻¹ * y⁻¹) * (a * x * a⁻¹ * x⁻¹) := by
    intro x hx y hy
    have huH : a * x * a⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem haH (hH.le_two hx)) (H.inv_mem haH)
    have hcen : (a * x * a⁻¹) * (a * y * a⁻¹ * y⁻¹) = (a * y * a⁻¹ * y⁻¹) * (a * x * a⁻¹) :=
      G23One.mul_comm_of_mem_inf hH huH (hmem y hy)
    calc a * (x * y) * a⁻¹ * (x * y)⁻¹
        = (a * x * a⁻¹) * (a * y * a⁻¹ * y⁻¹) * x⁻¹ := by group
      _ = (a * y * a⁻¹ * y⁻¹) * (a * x * a⁻¹) * x⁻¹ := by rw [hcen]
      _ = (a * y * a⁻¹ * y⁻¹) * (a * x * a⁻¹ * x⁻¹) := by group
  let φ : ↥H₂ →* ↥(H₁ ⊓ H₂) := MonoidHom.mk'
    (fun x => ⟨a * x.1 * a⁻¹ * x.1⁻¹, hmem x.1 x.2⟩) (by
      intro x y
      apply Subtype.ext
      show a * (x.1 * y.1) * a⁻¹ * (x.1 * y.1)⁻¹ =
        (a * x.1 * a⁻¹ * x.1⁻¹) * (a * y.1 * a⁻¹ * y.1⁻¹)
      rw [hkey x.1 x.2 y.1 y.2]
      exact G23One.inf_comm hH (hmem y.1 y.2) (hmem x.1 x.2))
  obtain ⟨τ⟩ := hH.iso_two
  have hY : ∀ y : ↥(H₁ ⊓ H₂), y ^ 2 = 1 := fun y =>
    Subtype.ext (by simpa using G23One.sq_inf hH y.2)
  have hψ := sl_hom_trivial hY (φ.comp τ.symm.toMonoidHom) (τ ⟨b, hb⟩)
  have hφ : φ ⟨b, hb⟩ = 1 := by simpa using hψ
  have hc1 : a * b * a⁻¹ * b⁻¹ = 1 := congrArg Subtype.val hφ
  have h2 : a * b * a⁻¹ = b := mul_inv_eq_one.mp hc1
  calc a * b = a * b * a⁻¹ * a := by group
    _ = b * a := by rw [h2]

end CFSG.GH74.QTGen4.Recog.G23
