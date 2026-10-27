module

public import CFSG.ClassicalInvolution.Q3.Q3TAxis
public import CFSG.ClassicalInvolution.Q3.Q3YQuat
public import CFSG.ClassicalInvolution.Q3.Q3ABoot

public section

namespace CFSG.ClassicalInvolution.Q3.Q3CH

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

theorem exists_noncomm_involutions_of_triangle [Finite G] {Ω : Set (Subgroup G)}
    {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ : G} (h : IsTriangle3 Ω K₁ K₂ K₃ z₁ z₂) :
    ∃ a b : G, a ∈ Subgroup.centralizer ({z₁} : Set G) ∧
      b ∈ Subgroup.centralizer ({z₁} : Set G) ∧ orderOf a = 2 ∧ orderOf b = 2 ∧
        a * b ≠ b * a := by
  obtain ⟨x₁, hx₁, -, -, hx₁sq, -⟩ := h.edge.cls₁.exists_quaternion_pair
  obtain ⟨x₂, hx₂, y₂, hy₂, hx₂sq, hy₂sq, hcomm₂⟩ := h.edge.cls₂.exists_quaternion_pair_sq
  obtain ⟨x₃, hx₃, -, -, hx₃sq, -⟩ := h.cls₃.exists_quaternion_pair
  have hA : AxisData3 Ω K₁ K₂ K₃ z₁ z₂ x₁ x₂ x₃ := ⟨h, hx₁, hx₂, hx₃, hx₁sq, hx₂sq, hx₃sq⟩
  have hB : AxisData3 Ω K₁ K₂ K₃ z₁ z₂ x₁ y₂ x₃ := ⟨h, hx₁, hy₂, hx₃, hx₁sq, hy₂sq, hx₃sq⟩
  have hinv : ∀ {s : G}, s * s = 1 → s ∉ Subgroup.closure ({z₁, z₂} : Set G) →
      orderOf s = 2 := fun {s} hs hs' =>
    orderOf_eq_prime (by rw [pow_two]; exact hs) (fun h1 => hs' (h1 ▸ Subgroup.one_mem _))
  have hle : K₁ ⊔ K₂ ⊔ K₃ ≤ Subgroup.centralizer ({z₁} : Set G) :=
    sup_le (sup_le (isSubnormal_le h.edge.cls₁.subnormal) h.edge.le_centralizer_left)
      (fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr
        (h.comm₁₃ z₁ h.edge.cls₁.mem k hk).symm)
  have hmem : ∀ {u v w : G}, u ∈ K₁ → v ∈ K₂ → w ∈ K₃ → u * v * w ∈ K₁ ⊔ K₂ ⊔ K₃ :=
    fun hu hv hw => Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left hu))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hv))) (Subgroup.mem_sup_right hw)
  refine ⟨x₁ * x₂ * x₃, x₁ * y₂ * x₃, hle (hmem hx₁ hx₂ hx₃), hle (hmem hx₁ hy₂ hx₃),
    hinv hA.s_mul_self hA.s_not_mem_pair, hinv hB.s_mul_self hB.s_not_mem_pair, ?_⟩
  intro hc
  have c12 : ∀ v ∈ K₂, x₁ * v = v * x₁ := fun v hv => h.edge.comm x₁ hx₁ v hv
  have c23 : ∀ v ∈ K₂, v * x₃ = x₃ * v := fun v hv => h.comm₂₃ v hv x₃ hx₃
  have e1 : x₁ * x₂ * x₃ * (x₁ * y₂ * x₃) = (x₁ * x₃) * (x₁ * x₃) * (x₂ * y₂) := by
    calc x₁ * x₂ * x₃ * (x₁ * y₂ * x₃) = x₁ * (x₂ * x₃) * x₁ * y₂ * x₃ := by group
      _ = x₁ * x₃ * (x₂ * x₁) * y₂ * x₃ := by rw [c23 x₂ hx₂]; group
      _ = x₁ * x₃ * x₁ * x₂ * (y₂ * x₃) := by rw [← c12 x₂ hx₂]; group
      _ = x₁ * x₃ * x₁ * (x₂ * x₃) * y₂ := by rw [c23 y₂ hy₂]; group
      _ = (x₁ * x₃) * (x₁ * x₃) * (x₂ * y₂) := by rw [c23 x₂ hx₂]; group
  have e2 : x₁ * y₂ * x₃ * (x₁ * x₂ * x₃) = (x₁ * x₃) * (x₁ * x₃) * (y₂ * x₂) := by
    calc x₁ * y₂ * x₃ * (x₁ * x₂ * x₃) = x₁ * (y₂ * x₃) * x₁ * x₂ * x₃ := by group
      _ = x₁ * x₃ * (y₂ * x₁) * x₂ * x₃ := by rw [c23 y₂ hy₂]; group
      _ = x₁ * x₃ * x₁ * y₂ * (x₂ * x₃) := by rw [← c12 y₂ hy₂]; group
      _ = x₁ * x₃ * x₁ * (y₂ * x₃) * x₂ := by rw [c23 x₂ hx₂]; group
      _ = (x₁ * x₃) * (x₁ * x₃) * (y₂ * x₂) := by rw [c23 y₂ hy₂]; group
  rw [e1, e2] at hc
  have h22 : x₂ * y₂ = y₂ * x₂ := mul_left_cancel hc
  apply h.edge.cls₂.ne_one
  rw [← hcomm₂, h22]
  group

theorem mem_closure_pair {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    {x : G} (hx : x ∈ Subgroup.closure ({a, b} : Set G)) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b :=
  CFSG.ClassicalInvolution.Q3.mem_closure_pair_cases ha hb hab hx

theorem isPGroup_sup_of_commute {A B : Subgroup G} (hA : IsPGroup 2 A) (hB : IsPGroup 2 B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : IsPGroup 2 ↥(A ⊔ B) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  hA.to_sup_of_normal_right' hB fun a ha =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (hAB a ha b hb).symm)

end CFSG.ClassicalInvolution.Q3.Q3CH
