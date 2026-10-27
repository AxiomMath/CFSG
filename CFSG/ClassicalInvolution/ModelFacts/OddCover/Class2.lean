module

public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Bilinear
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Central

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OddCover

open scoped commutatorElement

section Class2

variable {E : Type*} [Group E] {G Y : Subgroup E}

theorem mul_eq_of_mem_of_mem_of_comm_eq_one (hcent : ∀ y ∈ Y, ∀ g ∈ G, ⁅g, y⁆ = 1) {g y : E}
    (hg : g ∈ G) (hy : y ∈ Y) : g * y = y * g :=
  commutatorElement_eq_one_iff_mul_comm.1 (hcent y hy g hg)

theorem comm_mul_mem_left (hcent : ∀ y ∈ Y, ∀ g ∈ G, ⁅g, y⁆ = 1) {a b y : E} (hb : b ∈ G)
    (hy : y ∈ Y) : ⁅a * y, b⁆ = ⁅a, b⁆ := by
  have h : y * b = b * y := (mul_eq_of_mem_of_mem_of_comm_eq_one hcent hb hy).symm
  simp only [commutatorElement_def]
  calc a * y * b * (a * y)⁻¹ * b⁻¹ = a * (y * b * y⁻¹) * a⁻¹ * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h]; group

theorem comm_mul_mem_right (hcent : ∀ y ∈ Y, ∀ g ∈ G, ⁅g, y⁆ = 1) {a b y : E} (ha : a ∈ G)
    (hy : y ∈ Y) : ⁅a, b * y⁆ = ⁅a, b⁆ := by
  have h : y * a = a * y := (mul_eq_of_mem_of_mem_of_comm_eq_one hcent ha hy).symm
  simp only [commutatorElement_def]
  calc a * (b * y) * a⁻¹ * (b * y)⁻¹ = a * b * (y * a⁻¹ * y⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by
      rw [(Commute.inv_right (show Commute y a from h)).eq, mul_inv_cancel_right]

theorem comm_mul_left_of_mem (hcent : ∀ y ∈ Y, ∀ g ∈ G, ⁅g, y⁆ = 1) {a b c : E} (ha : a ∈ G)
    (hbc : ⁅b, c⁆ ∈ Y) : ⁅a * b, c⁆ = ⁅b, c⁆ * ⁅a, c⁆ := by
  have h : a * ⁅b, c⁆ = ⁅b, c⁆ * a := mul_eq_of_mem_of_mem_of_comm_eq_one hcent ha hbc
  have e : ⁅a * b, c⁆ = (a * ⁅b, c⁆ * a⁻¹) * ⁅a, c⁆ := by
    simp only [commutatorElement_def]; group
  rw [e, h, mul_inv_cancel_right]

theorem comm_mul_right_of_mem (hcent : ∀ y ∈ Y, ∀ g ∈ G, ⁅g, y⁆ = 1) {a b c : E} (hb : b ∈ G)
    (hac : ⁅a, c⁆ ∈ Y) : ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have h : b * ⁅a, c⁆ = ⁅a, c⁆ * b := mul_eq_of_mem_of_mem_of_comm_eq_one hcent hb hac
  rw [comm_mul_right_eq, h, mul_inv_cancel_right]

theorem kappa_comm_eq_one (hYG : Y ≤ G) (hcent : ∀ y ∈ Y, ∀ g ∈ G, ⁅g, y⁆ = 1)
    (hcomm : ∀ g ∈ G, ∀ h ∈ G, ⁅g, h⁆ ∈ Y) {κ : E → E}
    (hmul : ∀ y ∈ Y, ∀ y' ∈ Y, κ (y * y') = κ y * κ y')
    (hκZ : ∀ y ∈ Y, κ y ∈ Subgroup.center E) {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] (h5 : ∃ a : F, a ≠ 0 ∧ a + 1 ≠ 0 ∧ a ^ 2 + a + 1 ≠ 0) (ℓ : V → E)
    (hℓ : ∀ v, ℓ v ∈ G) (hgen : ∀ g ∈ G, ∃ v, ∃ y ∈ Y, g = ℓ v * y)
    (hadd : ∀ v w, ∃ y ∈ Y, ℓ (v + w) = ℓ v * ℓ w * y)
    (hscale : ∀ a : F, a ≠ 0 → ∃ h : E, (∀ y ∈ Y, κ (h * y * h⁻¹) = κ y) ∧
      ∀ v, ∃ k ∈ Subgroup.center E, h * ℓ v * h⁻¹ = ℓ (a • v) * k) :
    ∀ g ∈ G, ∀ h ∈ G, κ ⁅g, h⁆ = 1 := by
  let _ : CommGroup (Subgroup.center E) :=
    { (inferInstance : Group (Subgroup.center E)) with
      mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.1 b.2 a) }
  let B : V → V → Subgroup.center E := fun v w =>
    ⟨κ ⁅ℓ v, ℓ w⁆, hκZ _ (hcomm _ (hℓ v) _ (hℓ w))⟩
  have hB : ∀ v w, ((B v w : Subgroup.center E) : E) = κ ⁅ℓ v, ℓ w⁆ := fun v w => rfl
  have hadd₁ : ∀ x x' y, B (x + x') y = B x y * B x' y := by
    intro x x' y
    apply Subtype.ext
    obtain ⟨y₀, hy₀, hxx⟩ := hadd x x'
    rw [Subgroup.coe_mul, hB, hB, hB, hxx, comm_mul_mem_left hcent (hℓ y) hy₀,
      comm_mul_left_of_mem hcent (hℓ x) (hcomm _ (hℓ x') _ (hℓ y)),
      hmul _ (hcomm _ (hℓ x') _ (hℓ y)) _ (hcomm _ (hℓ x) _ (hℓ y))]
    exact Subgroup.mem_center_iff.1 (hκZ _ (hcomm _ (hℓ x) _ (hℓ y))) _
  have hadd₂ : ∀ x y y', B x (y + y') = B x y * B x y' := by
    intro x y y'
    apply Subtype.ext
    obtain ⟨y₀, hy₀, hyy⟩ := hadd y y'
    rw [Subgroup.coe_mul, hB, hB, hB, hyy, comm_mul_mem_right hcent (hℓ x) hy₀,
      comm_mul_right_of_mem hcent (hℓ y) (hcomm _ (hℓ x) _ (hℓ y')),
      hmul _ (hcomm _ (hℓ x) _ (hℓ y)) _ (hcomm _ (hℓ x) _ (hℓ y'))]
  have hinv : ∀ a : F, a ≠ 0 → ∀ x y, B (a • x) (a • y) = B x y := by
    intro a ha x y
    apply Subtype.ext
    obtain ⟨h, hκh, hact⟩ := hscale a ha
    obtain ⟨k₁, hk₁, hx⟩ := hact x
    obtain ⟨k₂, hk₂, hy⟩ := hact y
    rw [hB, hB, ← hκh _ (hcomm _ (hℓ x) _ (hℓ y)), conj_comm, hx, hy,
      comm_central_mul_right hk₁, comm_mul_central_right hk₂]
  have hone := eq_one_of_scalar_invariant h5 B hadd₁ hadd₂ hinv
  intro g hg h hh
  obtain ⟨v, y, hy, rfl⟩ := hgen g hg
  obtain ⟨w, y', hy', rfl⟩ := hgen h hh
  have h1 : ⁅ℓ v * y, ℓ w * y'⁆ = ⁅ℓ v, ℓ w⁆ := by
    rw [comm_mul_mem_right hcent (G := G) (Y := Y) (a := ℓ v * y) (b := ℓ w)
      (G.mul_mem (hℓ v) (hYG hy)) hy', comm_mul_mem_left hcent (hℓ w) hy]
  rw [h1]
  exact congrArg Subtype.val (hone v w)

end Class2

end CFSG.ClassicalInvolution.ModelFacts.OddCover
