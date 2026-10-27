module

public import CFSG.FeitThompson.Representations.QuotientIrreducibleCharsDegreeSum
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters
import CFSG.FeitThompson.Foundations.CommutatorMonotone
import CFSG.FeitThompson.Representations.TensorAndDualCharacters
import Mathlib.Analysis.Complex.Polynomial.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module

variable {K : Type*} [Group K]

theorem commutator_top_eq_closure_inv_mul_inv_mul_mul :
    commutator K = Subgroup.closure {g : K | ∃ x y : K, x⁻¹ * y⁻¹ * x * y = g} := by
  rw [commutator_def, commutator_eq_closure_inv_mul_inv_mul_mul]
  congr 1
  ext g
  simp

namespace Irr

theorem commutator_subset_charValueKernel {θ : K → ℂ} (hθ : θ ∈ Irr K) (h1 : θ 1 = 1) :
    (commutator K : Set K) ⊆ charValueKernel θ := by
  obtain ⟨W, hW, rfl⟩ := mem_Irr.1 hθ
  have hfr : finrank ℂ W.V = 1 := by
    have h := W.char_one
    rw [h1] at h
    exact_mod_cast h.symm
  obtain ⟨χ, hχ⟩ := Representation.exists_monoidHom_units_of_finrank_eq_one W.ρ hfr
  have hval : ∀ g : K, W.character g = (χ g : ℂ) := fun g => by
    have hg : W.ρ g = (χ g : ℂ) • LinearMap.id := by ext v; simpa using hχ g v
    rw [FDRep.character, hg]
    simp [hfr]
  intro g hg
  have hk : χ g = 1 := MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker χ hg)
  rw [mem_charValueKernel, hval g, hval 1, hk]
  simp

theorem apply_one_eq_one_of_commutator_subset_charValueKernel [Finite K] {θ : K → ℂ}
    (hθ : θ ∈ Irr K) (h : (commutator K : Set K) ⊆ charValueKernel θ) : θ 1 = 1 := by
  obtain ⟨ψ, hψ, hcomp⟩ := exists_comp_mk_eq_of_mem_irrTrivialOn (N := commutator K)
    (mem_irrTrivialOn.2 ⟨hθ, fun n hn => mem_charValueKernel.1 (h hn)⟩)
  obtain ⟨W, hW, rfl⟩ := mem_Irr.1 hψ
  have : IsMulCommutative (K ⧸ commutator K) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.2 le_rfl
  have : Representation.IsIrreducible W.ρ := hW
  have hfr : finrank ℂ W.V = 1 :=
    Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative W.ρ
  have he := congrFun hcomp 1
  rw [← he]
  change W.character (1 : K ⧸ commutator K) = 1
  rw [W.char_one, hfr, Nat.cast_one]

theorem apply_one_eq_one_iff [Finite K] {θ : K → ℂ} (hθ : θ ∈ Irr K) :
    θ 1 = 1 ↔ (commutator K : Set K) ⊆ charValueKernel θ :=
  ⟨commutator_subset_charValueKernel hθ, apply_one_eq_one_of_commutator_subset_charValueKernel hθ⟩

theorem apply_inv_mul_inv_mul_mul {θ : K → ℂ} (hθ : θ ∈ Irr K) (h1 : θ 1 = 1) (x y : K) :
    θ (x⁻¹ * y⁻¹ * x * y) = 1 := by
  have hmem : x⁻¹ * y⁻¹ * x * y ∈ commutator K := by
    rw [commutator_top_eq_closure_inv_mul_inv_mul_mul]
    exact Subgroup.subset_closure ⟨x, y, rfl⟩
  rw [mem_charValueKernel.1 (commutator_subset_charValueKernel hθ h1 hmem), h1]

theorem setOf_apply_one_eq_one_eq_irrTrivialOn_commutator [Finite K] :
    {θ ∈ Irr K | θ 1 = 1} = irrTrivialOn (commutator K) := by
  ext θ
  rw [Set.mem_sep_iff, mem_irrTrivialOn]
  refine and_congr_right fun hθ => ?_
  rw [apply_one_eq_one_iff hθ]
  exact ⟨fun h n hn => mem_charValueKernel.1 (h hn), fun h n hn => mem_charValueKernel.2 (h n hn)⟩

end Irr

end CFSG.FeitThompson
