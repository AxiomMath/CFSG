module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSecXg
public import CFSG.ClassicalInvolution.Q3.TL3T4

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

namespace TwinThin

variable {G : Type} [Group G] [Finite G]

theorem false_of_conj_commute (hS : IsSimpleGroup ↥(genFittingFStar G))
    (hnab : ∃ a b : ↥(genFittingFStar G), a * b ≠ b * a) {z : G} (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hc : ∀ h : G, z * (h * z * h⁻¹) = (h * z * h⁻¹) * z) : False := by
  set T : Set G := {w | ∃ h : G, w = h * z * h⁻¹} with hT
  have hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have h1 := hc (a⁻¹ * b)
    calc a * z * a⁻¹ * (b * z * b⁻¹) = a * (z * (a⁻¹ * b * z * (a⁻¹ * b)⁻¹)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * b * z * (a⁻¹ * b)⁻¹) * z) * a⁻¹ := by rw [h1]
      _ = b * z * b⁻¹ * (a * z * a⁻¹) := by group
  have hT2 : ∀ x ∈ T, ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    rintro _ ⟨a, rfl⟩
    refine ⟨1, ?_⟩
    have : (a * z * a⁻¹) * (a * z * a⁻¹) = 1 := by
      calc (a * z * a⁻¹) * (a * z * a⁻¹) = a * (z * z) * a⁻¹ := by group
        _ = 1 := by rw [hz2]; group
    simpa [pow_two] using this
  have hP : IsPGroup 2 ↥(Subgroup.closure T) := CFSG.ClassicalInvolution.Q3.TC.Thin.isPGroup_closure_of_comm hTcomm hT2
  have hNorm : (Subgroup.closure T).Normal := by
    refine ⟨fun x hx g => ?_⟩
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Subgroup.subset_closure ⟨g * a, by group⟩
    | one => simp
    | mul x y hx hy ihx ihy =>
      have := (Subgroup.closure T).mul_mem ihx ihy
      simpa [mul_assoc] using this
    | inv x hx ihx =>
      have := (Subgroup.closure T).inv_mem ihx
      simpa [mul_assoc] using this
  have hzT : z ∈ Subgroup.closure T := Subgroup.subset_closure ⟨1, by group⟩
  have hbot := TwinSecXg.normalTwo_eq_bot_of_fstar_simple hS hnab hNorm hP
  rw [hbot, Subgroup.mem_bot] at hzT
  exact hz1 hzT

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
