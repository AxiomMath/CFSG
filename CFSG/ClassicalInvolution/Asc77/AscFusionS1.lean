module

public import CFSG.ClassicalInvolution.Asc77.AscL62Aut

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open Matrix
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F]

open CFSG.ClassicalInvolution.Asc77.AscL62 in
theorem matrix_eq_smul_add_of_commute (hF : (2 : F) ≠ 0) (g M : Matrix (Fin 2) (Fin 2) F)
    (hg : g * g = -1) (hgt : g.trace = 0) (hM : M * g = g * M) :
    ∃ m c : F, M = m • (1 : Matrix (Fin 2) (Fin 2) F) + c • g := by
  set m : F := M.trace / 2 with hm
  set M₀ : Matrix (Fin 2) (Fin 2) F := M - m • 1 with hM₀
  have hM₀t : M₀.trace = 0 := by
    rw [hM₀, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
    simp only [Fintype.card_fin, smul_eq_mul, hm]
    field_simp
    ring
  have hM₀a : M₀ * g = g * M₀ := by
    rw [hM₀, sub_mul, mul_sub, hM]
    simp
  have hA := mul_eq_half_trace hF g M₀ hgt hM₀t hM₀a
  set u : F := (g * M₀).trace / 2 with hu
  have e1 : M₀ = -(u • g) := by
    have : -(g * (g * M₀)) = M₀ := by
      rw [← mul_assoc, hg]; simp
    rw [← this, hA]
    simp
  refine ⟨m, -u, ?_⟩
  have : M = M₀ + m • 1 := by rw [hM₀]; abel
  rw [this, e1]
  simp [neg_smul]
  abel

open CFSG.ClassicalInvolution.Asc77.AscL62 in
theorem sl2_commute_of_commute_sq_neg_one (hF : (2 : F) ≠ 0) (g h₁ h₂ : SL(2, F))
    (hg : g * g = -1) (h₁g : h₁ * g = g * h₁) (h₂g : h₂ * g = g * h₂) : h₁ * h₂ = h₂ * h₁ := by
  have hgm : (g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) = -1 := by
    have := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F)) hg
    simpa [Matrix.SpecialLinearGroup.coe_mul] using this
  have hgt := trace_eq_zero_of_mul_self_eq_neg_one g hg
  have c1 : (h₁ : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
      (g : Matrix (Fin 2) (Fin 2) F) * (h₁ : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F)) h₁g
    simpa [Matrix.SpecialLinearGroup.coe_mul] using this
  have c2 : (h₂ : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
      (g : Matrix (Fin 2) (Fin 2) F) * (h₂ : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F)) h₂g
    simpa [Matrix.SpecialLinearGroup.coe_mul] using this
  obtain ⟨m₁, a₁, e₁⟩ := matrix_eq_smul_add_of_commute hF _ _ hgm hgt c1
  obtain ⟨m₂, a₂, e₂⟩ := matrix_eq_smul_add_of_commute hF _ _ hgm hgt c2
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, e₁, e₂]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one]
  module

theorem sl2_neg_one_central (x : SL(2, F)) : (-1 : SL(2, F)) * x = x * (-1) := by
  apply Subtype.ext
  simp

theorem commute_mul_inv_of_sign {M : Type*} [Group M] (g w₁ w₂ η : M)
    (hη : ∀ x, η * x = x * η) (hηη : η * η = 1) (h₁ : w₁ * g = η * g * w₁)
    (h₂ : w₂ * g = η * g * w₂) : w₁ * w₂⁻¹ * g = g * (w₁ * w₂⁻¹) := by
  have h2' : w₂⁻¹ * g = η * g * w₂⁻¹ := by
    have : w₂⁻¹ * (w₂ * g) * w₂⁻¹ = w₂⁻¹ * (η * g * w₂) * w₂⁻¹ := by rw [h₂]
    have e1 : w₂⁻¹ * (w₂ * g) * w₂⁻¹ = g * w₂⁻¹ := by group
    have e2 : w₂⁻¹ * (η * g * w₂) * w₂⁻¹ = w₂⁻¹ * η * g := by group
    rw [e1, e2] at this
    calc w₂⁻¹ * g = η * η * (w₂⁻¹ * g) := by rw [hηη, one_mul]
      _ = η * (η * w₂⁻¹ * g) := by group
      _ = η * (w₂⁻¹ * η * g) := by rw [hη w₂⁻¹]
      _ = η * (g * w₂⁻¹) := by rw [this]
      _ = η * g * w₂⁻¹ := by group
  calc w₁ * w₂⁻¹ * g = w₁ * (w₂⁻¹ * g) := by group
    _ = w₁ * (η * g * w₂⁻¹) := by rw [h2']
    _ = η * (w₁ * g) * w₂⁻¹ := by
        have : w₁ * η = η * w₁ := (hη w₁).symm
        calc w₁ * (η * g * w₂⁻¹) = (w₁ * η) * g * w₂⁻¹ := by group
          _ = (η * w₁) * g * w₂⁻¹ := by rw [this]
          _ = η * (w₁ * g) * w₂⁻¹ := by group
    _ = η * (η * g * w₁) * w₂⁻¹ := by rw [h₁]
    _ = g * (w₁ * w₂⁻¹) := by
        have e : η * (η * g * w₁) * w₂⁻¹ = (η * η) * g * w₁ * w₂⁻¹ := by group
        rw [e, hηη]
        group

theorem sl2_isSolvable_of_commute_pm (hF : (2 : F) ≠ 0) (g : SL(2, F)) (hg : g * g = -1)
    (S : Subgroup SL(2, F)) (hS : ∀ h ∈ S, h * g = g * h ∨ h * g = (-1) * g * h) :
    Group.IsSolvable S := by
  classical
  set c : SL(2, F) := -1 with hc
  have hcc : c * c = 1 := by
    apply Subtype.ext
    simp [hc]
  have hcen : ∀ x : SL(2, F), c * x = x * c := fun x => sl2_neg_one_central x
  have hsign : ∀ x ∈ S, ∃ ε : SL(2, F), (ε = 1 ∨ ε = c) ∧ x * g = ε * g * x := by
    intro x hx
    rcases hS x hx with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_mul]⟩
    · exact ⟨c, Or.inr rfl, h⟩
  have hεcen : ∀ ε : SL(2, F), (ε = 1 ∨ ε = c) → ∀ x, ε * x = x * ε := by
    rintro ε (rfl | rfl) x
    · simp
    · exact hcen x
  have hεε : ∀ ε : SL(2, F), (ε = 1 ∨ ε = c) → ε * ε = 1 := by
    rintro ε (rfl | rfl)
    · simp
    · exact hcc
  have hεmul : ∀ ε₁ ε₂ : SL(2, F), (ε₁ = 1 ∨ ε₁ = c) → (ε₂ = 1 ∨ ε₂ = c) →
      (ε₁ * ε₂ = 1 ∨ ε₁ * ε₂ = c) := by
    rintro ε₁ ε₂ (rfl | rfl) (rfl | rfl)
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
    · exact Or.inr (by simp)
    · exact Or.inl hcc
  have hcomm : ∀ x ∈ S, ∀ y ∈ S, ⁅x, y⁆ * g = g * ⁅x, y⁆ := by
    intro x hx y hy
    obtain ⟨εx, hεx, hxg⟩ := hsign x hx
    obtain ⟨εy, hεy, hyg⟩ := hsign y hy
    have h1 : (x * y) * g = (εx * εy) * g * (x * y) := by
      calc (x * y) * g = x * (y * g) := by group
        _ = x * (εy * g * y) := by rw [hyg]
        _ = εy * (x * g) * y := by
            have := hεcen εy hεy x
            calc x * (εy * g * y) = (x * εy) * g * y := by group
              _ = (εy * x) * g * y := by rw [← this]
              _ = εy * (x * g) * y := by group
        _ = εy * (εx * g * x) * y := by rw [hxg]
        _ = (εx * εy) * g * (x * y) := by
            have := hεcen εy hεy εx
            calc εy * (εx * g * x) * y = (εy * εx) * g * (x * y) := by group
              _ = (εx * εy) * g * (x * y) := by rw [this]
    have h2 : (y * x) * g = (εx * εy) * g * (y * x) := by
      calc (y * x) * g = y * (x * g) := by group
        _ = y * (εx * g * x) := by rw [hxg]
        _ = εx * (y * g) * x := by
            have := hεcen εx hεx y
            calc y * (εx * g * x) = (y * εx) * g * x := by group
              _ = (εx * y) * g * x := by rw [← this]
              _ = εx * (y * g) * x := by group
        _ = εx * (εy * g * y) * x := by rw [hyg]
        _ = (εx * εy) * g * (y * x) := by group
    have hη := hεmul εx εy hεx hεy
    have key := commute_mul_inv_of_sign g (x * y) (y * x) (εx * εy)
      (hεcen _ hη) (hεε _ hη) h1 h2
    have e : ⁅x, y⁆ = x * y * (y * x)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact key
  rw [Group.isSolvable_def]
  refine ⟨2, ?_⟩
  set N : Subgroup ↥S := (Subgroup.centralizer ({g} : Set SL(2, F))).subgroupOf S with hN
  have hN1 : ⁅(⊤ : Subgroup ↥S), ⊤⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [hN, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    have := hcomm x.1 x.2 y.1 y.2
    simpa [commutatorElement_def] using this
  have hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    intro a ha b hb
    rw [hN, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at ha hb
    apply Subtype.ext
    exact sl2_commute_of_commute_sq_neg_one hF g a.1 b.1 hg ha hb
  have hN2 : ⁅N, N⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hNab a ha b hb).symm
  rw [derivedSeries_succ, derivedSeries_succ, derivedSeries_zero]
  exact le_bot_iff.mp (hN2 ▸ Subgroup.commutator_mono hN1 hN1)

end CFSG.ClassicalInvolution.Asc77.AscFusion
