module

public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters
import CFSG.FeitThompson.Representations.CentralSubgroupBoundsDegreeSquare
import CFSG.FeitThompson.Representations.QuotientIrreducibleCharsDegreeSum

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {H : Type*} [Group H] {A B : Subgroup H} [B.Normal]

theorem map_mk'_le_center_iff :
    A.map (QuotientGroup.mk' B) ≤ Subgroup.center (H ⧸ B) ↔
      ∀ a ∈ A, ∀ h : H, a * h * a⁻¹ * h⁻¹ ∈ B := by
  constructor
  · intro hle a ha h
    have hmem : (QuotientGroup.mk' B) a ∈ Subgroup.center (H ⧸ B) :=
      hle (Subgroup.mem_map_of_mem (QuotientGroup.mk' B) ha)
    have hcomm := Subgroup.mem_center_iff.1 hmem ((QuotientGroup.mk' B) h)
    rw [← QuotientGroup.ker_mk' B, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [← hcomm]
    group
  · intro hcomm q hq
    obtain ⟨a, ha, rfl⟩ := hq
    rw [Subgroup.mem_center_iff]
    intro g
    induction g using QuotientGroup.induction_on with
    | _ h =>
      have h1 : (QuotientGroup.mk' B) (a * h * a⁻¹ * h⁻¹) = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk' B]; exact hcomm a ha h
      simp only [map_mul, map_inv] at h1
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm

variable [Finite H]

theorem exists_degree_eq_and_sq_le_index_of_map_le_center (hBA : B ≤ A)
    (hcen : A.map (QuotientGroup.mk' B) ≤ Subgroup.center (H ⧸ B))
    {θ : H → ℂ} (hθ : θ ∈ Irr H) (hker : (B : Set H) ⊆ charValueKernel θ) :
    ∃ n : ℕ, θ 1 = n ∧ n ^ 2 ≤ A.index := by
  obtain ⟨ψ, hψ, hcomp⟩ := exists_comp_mk_eq_of_mem_irrTrivialOn (N := B)
    (mem_irrTrivialOn.2 ⟨hθ, fun n hn => mem_charValueKernel.1 (hker hn)⟩)
  obtain ⟨n, hn1, hn2⟩ := exists_degree_eq_and_sq_le_index_of_le_center hψ hcen
  refine ⟨n, ?_, ?_⟩
  · rw [← hcomp, comp_mk_one, hn1]
  ·
    rwa [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective B)
      (by rwa [QuotientGroup.ker_mk'])] at hn2

theorem norm_apply_one_sq_le_index_of_map_le_center (hBA : B ≤ A)
    (hcen : A.map (QuotientGroup.mk' B) ≤ Subgroup.center (H ⧸ B))
    {θ : H → ℂ} (hθ : θ ∈ Irr H) (hker : (B : Set H) ⊆ charValueKernel θ) :
    ‖θ 1‖ ^ 2 ≤ (A.index : ℝ) := by
  obtain ⟨n, hn1, hn2⟩ := exists_degree_eq_and_sq_le_index_of_map_le_center hBA hcen hθ hker
  have hn : ((n : ℝ)) ^ 2 ≤ (A.index : ℝ) := by exact_mod_cast hn2
  simpa [hn1] using hn

theorem exists_degree_eq_and_sq_le_index_of_commutator_mem (hBA : B ≤ A)
    (hcen : ∀ a ∈ A, ∀ h : H, a * h * a⁻¹ * h⁻¹ ∈ B)
    {θ : H → ℂ} (hθ : θ ∈ Irr H) (hker : (B : Set H) ⊆ charValueKernel θ) :
    ∃ n : ℕ, θ 1 = n ∧ n ^ 2 ≤ A.index :=
  exists_degree_eq_and_sq_le_index_of_map_le_center hBA (map_mk'_le_center_iff.2 hcen) hθ hker

end CFSG.FeitThompson
