module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneBasic

public section

namespace CFSG.ProperTwoGeneratedCore.ExceptionalEight

variable {Y : Type*} [Group Y]

namespace PlaneHyp

variable {U B : Subgroup Y} {b₁ b₂ u₀ : Y} [U.Normal] [IsElementaryAbelian 2 U]
  (h : PlaneHyp U B b₁ b₂ u₀)
include h

theorem commutator_mem_B {x y : Y} (hx : x ∈ Subgroup.centralizer (B : Set Y))
    (hy : y ∈ Subgroup.centralizer (B : Set Y)) : x * y * x⁻¹ * y⁻¹ ∈ B := by
  have hxx := h.mul_self_mem_B hx
  have hyy := h.mul_self_mem_B hy
  have hxy := h.mul_self_mem_B (Subgroup.mul_mem _ hx hy)
  have hcomm : (x * x)⁻¹ * y = y * (x * x)⁻¹ :=
    ((Subgroup.mem_centralizer_iff.mp hy) _ (B.inv_mem hxx))
  have heq : x * y * x⁻¹ * y⁻¹ = x * y * (x * y) * ((x * x)⁻¹ * (y * y)⁻¹) := by
    calc x * y * x⁻¹ * y⁻¹ = x * y * (x * (x * x)⁻¹) * (y * (y * y)⁻¹) := by group
      _ = x * y * x * ((x * x)⁻¹ * y) * (y * y)⁻¹ := by group
      _ = x * y * x * (y * (x * x)⁻¹) * (y * y)⁻¹ := by rw [hcomm]
      _ = x * y * (x * y) * ((x * x)⁻¹ * (y * y)⁻¹) := by group
  rw [heq]
  exact B.mul_mem hxy (B.mul_mem (B.inv_mem hxx) (B.inv_mem hyy))

theorem commutator_u₀ {y : Y} (hy : y ∈ Subgroup.centralizer (B : Set Y)) :
    y * u₀ * y⁻¹ * u₀⁻¹ = planeTau u₀ y := by
  have hτU : planeTau u₀ y ∈ U := h.le (h.planeTau_mem hy)
  rw [h.conj_u₀ y, mul_assoc, mul_comm_of_mem hτU (U.inv_mem h.u₀_mem), ← mul_assoc,
    mul_inv_cancel, one_mul]

theorem commutator_u₀' {y : Y} (hy : y ∈ Subgroup.centralizer (B : Set Y)) :
    u₀ * y * u₀⁻¹ * y⁻¹ = planeTau u₀ y := by
  have hτU : planeTau u₀ y ∈ U := h.le (h.planeTau_mem hy)
  have h1 := h.commutator_u₀ hy
  have h2 : u₀ * y * u₀⁻¹ * y⁻¹ = (y * u₀ * y⁻¹ * u₀⁻¹)⁻¹ := by group
  rw [h2, h1, inv_eq_self_of_mem hτU]

omit h in
theorem commutator_mul_left {x y z : Y} (hx : x ∈ Subgroup.centralizer (B : Set Y))
    (hyz : y * z * y⁻¹ * z⁻¹ ∈ B) :
    x * y * z * (x * y)⁻¹ * z⁻¹ = (y * z * y⁻¹ * z⁻¹) * (x * z * x⁻¹ * z⁻¹) := by
  have hc := conj_eq_of_mem_centralizer hx hyz
  calc x * y * z * (x * y)⁻¹ * z⁻¹ = x * (y * z * y⁻¹ * z⁻¹) * x⁻¹ * (x * z * x⁻¹ * z⁻¹) := by
        group
    _ = (y * z * y⁻¹ * z⁻¹) * (x * z * x⁻¹ * z⁻¹) := by rw [hc]

omit h in
theorem commutator_mul_right {x y z : Y} (hy : y ∈ Subgroup.centralizer (B : Set Y))
    (hxz : x * z * x⁻¹ * z⁻¹ ∈ B) :
    x * (y * z) * x⁻¹ * (y * z)⁻¹ = (x * y * x⁻¹ * y⁻¹) * (x * z * x⁻¹ * z⁻¹) := by
  have hc := conj_eq_of_mem_centralizer hy hxz
  calc x * (y * z) * x⁻¹ * (y * z)⁻¹ = (x * y * x⁻¹ * y⁻¹) * (y * (x * z * x⁻¹ * z⁻¹) * y⁻¹) := by
        group
    _ = (x * y * x⁻¹ * y⁻¹) * (x * z * x⁻¹ * z⁻¹) := by rw [hc]

theorem exists_commuting_lifts : ∃ c₁ ∈ Subgroup.centralizer (B : Set Y),
    ∃ c₂ ∈ Subgroup.centralizer (B : Set Y),
      planeTau u₀ c₁ = b₁ ∧ planeTau u₀ c₂ = b₂ ∧ c₁ * c₂ = c₂ * c₁ := by
  obtain ⟨c₁, hc₁, hτ₁⟩ := h.exists_translation h.b₁_mem
  obtain ⟨c₂, hc₂, hτ₂⟩ := h.exists_translation h.b₂_mem
  have hu₀C : u₀ ∈ Subgroup.centralizer (B : Set Y) := h.U_le_centralizer h.u₀_mem
  have hτu₀ : planeTau u₀ u₀ = 1 := h.planeTau_of_mem_U h.u₀_mem
  have hβ := h.commutator_mem_B hc₁ hc₂
  have hcomm_iff : ∀ x y : Y, x * y * x⁻¹ * y⁻¹ = 1 → x * y = y * x := by
    intro x y hxy
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [hxy, one_mul]
  have hb₁U := h.b₁_mem_U
  have hb₂U := h.b₂_mem_U
  have hτ1 : ∀ x ∈ Subgroup.centralizer (B : Set Y), planeTau u₀ (x * u₀) = planeTau u₀ x := by
    intro x hx
    rw [h.planeTau_mul hx hu₀C, hτu₀, mul_one]
  rcases h.mem_B_cases hβ with hβ1 | hβ1 | hβ1 | hβ1
  · exact ⟨c₁, hc₁, c₂, hc₂, hτ₁, hτ₂, hcomm_iff _ _ hβ1⟩
  · refine ⟨c₁, hc₁, c₂ * u₀, Subgroup.mul_mem _ hc₂ hu₀C, hτ₁, by rw [hτ1 c₂ hc₂, hτ₂], ?_⟩
    apply hcomm_iff
    have hc1u : c₁ * u₀ * c₁⁻¹ * u₀⁻¹ ∈ B := by rw [h.commutator_u₀ hc₁]; exact h.planeTau_mem hc₁
    rw [commutator_mul_right hc₂ hc1u, hβ1, h.commutator_u₀ hc₁, hτ₁,
      mul_self_eq_one_of_mem hb₁U]
  · refine ⟨c₁ * u₀, Subgroup.mul_mem _ hc₁ hu₀C, c₂, hc₂, by rw [hτ1 c₁ hc₁, hτ₁], hτ₂, ?_⟩
    apply hcomm_iff
    have hu2 : u₀ * c₂ * u₀⁻¹ * c₂⁻¹ ∈ B := by
      rw [h.commutator_u₀' hc₂]; exact h.planeTau_mem hc₂
    rw [commutator_mul_left hc₁ hu2, h.commutator_u₀' hc₂, hτ₂, hβ1,
      mul_self_eq_one_of_mem hb₂U]
  · refine ⟨c₁ * u₀, Subgroup.mul_mem _ hc₁ hu₀C, c₂ * u₀, Subgroup.mul_mem _ hc₂ hu₀C,
      by rw [hτ1 c₁ hc₁, hτ₁], by rw [hτ1 c₂ hc₂, hτ₂], ?_⟩
    apply hcomm_iff
    have hmem : ∀ x ∈ Subgroup.centralizer (B : Set Y), ∀ y ∈ Subgroup.centralizer (B : Set Y),
        x * y * x⁻¹ * y⁻¹ ∈ B := fun x hx y hy => h.commutator_mem_B hx hy
    rw [commutator_mul_left hc₁ (hmem _ hu₀C _ (Subgroup.mul_mem _ hc₂ hu₀C)),
      commutator_mul_right hc₂ (hmem _ hu₀C _ hu₀C),
      commutator_mul_right hc₂ (hmem _ hc₁ _ hu₀C), h.commutator_u₀' hc₂,
      h.commutator_u₀ hc₁, hτ₁, hτ₂, hβ1,
      show u₀ * u₀ * u₀⁻¹ * u₀⁻¹ = 1 by group, mul_one]
    calc b₂ * (b₁ * b₂ * b₁) = (b₂ * b₂) * (b₁ * b₁) := by
          rw [mul_comm_of_mem hb₁U hb₂U]; group
      _ = 1 := by rw [mul_self_eq_one_of_mem hb₂U, mul_self_eq_one_of_mem hb₁U, one_mul]

theorem commutator_centralizer_eq :
    ⁅Subgroup.centralizer (B : Set Y), Subgroup.centralizer (B : Set Y)⁆ = B := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact h.commutator_mem_B hx hy
  · intro b hb
    obtain ⟨y, hy, hτ⟩ := h.exists_translation hb
    have hu₀C : u₀ ∈ Subgroup.centralizer (B : Set Y) := h.U_le_centralizer h.u₀_mem
    have := Subgroup.commutator_mem_commutator hy hu₀C
    rwa [commutatorElement_def, h.commutator_u₀ hy, hτ] at this

theorem center_centralizer_eq :
    (Subgroup.center (Subgroup.centralizer (B : Set Y))).map
      (Subgroup.centralizer (B : Set Y)).subtype = B := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    have hzU : (z : Y) ∈ U := by
      rw [← h.centralizer_U, Subgroup.mem_centralizer_iff]
      intro x hx
      have := Subgroup.mem_center_iff.mp hz ⟨x, h.U_le_centralizer hx⟩
      exact congrArg Subtype.val this
    by_contra hzB
    obtain ⟨y, hy, hτ⟩ := h.exists_translation h.b₁_mem
    have hc := h.conj_of_not_mem hy hzU hzB
    have hcomm := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)
    simp only [Subgroup.coe_mul] at hcomm
    rw [hcomm, mul_inv_cancel_right, hτ] at hc
    exact h.b₁_ne_one (left_eq_mul.mp hc)
  · intro b hb
    refine ⟨⟨b, Subgroup.mem_centralizer_iff.mpr fun c hc => ?_⟩, ?_, rfl⟩
    · exact mul_comm_of_mem (h.le hc) (h.le hb)
    · exact Subgroup.mem_center_iff.mpr fun y =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp y.2 b hb).symm

omit [U.Normal] [IsElementaryAbelian 2 U] h in
theorem le_centralizer_of_le {B : Subgroup Y} (hBU : B ≤ U) [IsElementaryAbelian 2 U] :
    B ≤ Subgroup.centralizer (B : Set Y) := by
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  exact mul_comm_of_mem (hBU hc) (hBU hb)

omit [U.Normal] [IsElementaryAbelian 2 U] h in
theorem normal_B_subgroupOf : (B.subgroupOf (Subgroup.centralizer (B : Set Y))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    conj_eq_of_mem_centralizer g.2 hn]
  exact hn

theorem quotient_B_spec :
    ∃ _ : (B.subgroupOf (Subgroup.centralizer (B : Set Y))).Normal,
      IsElementaryAbelian 2
          (Subgroup.centralizer (B : Set Y) ⧸ B.subgroupOf (Subgroup.centralizer (B : Set Y))) ∧
        Nat.card
          (Subgroup.centralizer (B : Set Y) ⧸ B.subgroupOf (Subgroup.centralizer (B : Set Y))) =
          8 := by
  have hBC : B ≤ Subgroup.centralizer (B : Set Y) := le_centralizer_of_le h.le
  have hN := normal_B_subgroupOf (B := B)
  refine ⟨hN, ?_, ?_⟩
  · refine { is_comm := ⟨fun a b => ?_⟩, exponent_dvd_p := ?_ }
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have := h.commutator_mem_B (Subgroup.inv_mem _ y.2) (Subgroup.inv_mem _ x.2)
      simp only [inv_inv] at this
      simpa [mul_assoc] using this
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun q => ?_
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.coe_pow, pow_two]
      exact h.mul_self_mem_B x.2
  · have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (B.subgroupOf (Subgroup.centralizer (B : Set Y)))
    rw [h.card_C, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv, h.card_B] at hcard
    omega

end PlaneHyp

end CFSG.ProperTwoGeneratedCore.ExceptionalEight
