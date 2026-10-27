module

public import CFSG.CharacterTheory.OddOrderBasics.Schur
public import CFSG.CharacterTheory.TwoRankLowerBound.InvolutionTrace
public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open scoped BigOperators Classical

namespace CFSG.DihedralTIFusion

theorem class_sum_square_trace {G V : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : ρ.IsIrreducible)
    (t : G) :
    (∑ x ∈ Finset.univ.filter (IsConj t), ∑ y ∈ Finset.univ.filter (IsConj t),
        ρ.character (x * y)) * ρ.character 1 =
      ((Finset.univ.filter (IsConj t)).card * ρ.character t) ^ 2 := by
  set C := Finset.univ.filter (IsConj t) with hC
  have hmemC : ∀ x, x ∈ C ↔ IsConj t x := fun x => by simp [hC]
  set T : Module.End ℂ V := ∑ x ∈ C, ρ x with hTdef
  have hT : ∀ g : G, T ∘ₗ ρ g = ρ g ∘ₗ T := by
    intro g
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, hTdef, Finset.sum_mul,
      Finset.mul_sum]
    simp only [← map_mul]
    refine (Finset.sum_nbij' (fun y => g⁻¹ * y * g) (fun x => g * x * g⁻¹) ?_ ?_ ?_ ?_ ?_)
    · intro y hy
      rw [hmemC] at hy ⊢
      exact hy.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)
    · intro x hx
      rw [hmemC] at hx ⊢
      exact hx.trans (isConj_iff.mpr ⟨g, rfl⟩)
    · intro y _
      group
    · intro x _
      group
    · intro y _
      congr 1
      group
  obtain ⟨a, ha⟩ := OddOrderBasics.complex_irreducible_commuting_scalar ρ hρ T hT
  have hvalue : ∀ x ∈ C, ρ.character x = ρ.character t := by
    intro x hx
    obtain ⟨c, hc⟩ := isConj_iff.mp ((hmemC x).mp hx)
    rw [← hc, Representation.char_conj]
  have htr : LinearMap.trace ℂ V T = C.card * ρ.character t := by
    rw [hTdef, map_sum]
    change ∑ x ∈ C, ρ.character x = _
    rw [Finset.sum_congr rfl hvalue, Finset.sum_const, nsmul_eq_mul]
  have htr2 : LinearMap.trace ℂ V (T * T) =
      ∑ x ∈ C, ∑ y ∈ C, ρ.character (x * y) := by
    rw [hTdef, Finset.sum_mul_sum, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← map_mul]
    rfl
  have hsq : T * T = (a * a) • LinearMap.id := by
    rw [ha, smul_mul_smul_comm, ← Module.End.one_eq_id, mul_one]
  rw [ha, map_smul, LinearMap.trace_id, smul_eq_mul] at htr
  rw [hsq, map_smul, LinearMap.trace_id, smul_eq_mul] at htr2
  rw [← htr2, Representation.char_one, ← htr]
  ring

theorem involution_class_square_degree_gap_kernel {G V U : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup U] [Module ℂ U]
    [FiniteDimensional ℂ U] (ρ : Representation ℂ G V) (σ : Representation ℂ G U)
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible)
    (hdeg : ρ.character 1 = σ.character 1 + 1) {t : G} (ht : orderOf t = 2)
    (hαt : ρ.character t - σ.character t - 1 = 0)
    (hαC : ∀ x y : G, IsConj t x → IsConj t y →
      ρ.character (x * y) - σ.character (x * y) - 1 = 0) :
    t ∈ ρ.ker ⊓ σ.ker := by
  have : Fintype G := Fintype.ofFinite G
  set C := Finset.univ.filter (IsConj t) with hC
  have hmemC : ∀ x, x ∈ C ↔ IsConj t x := fun x => by simp [hC]
  have hρtr := class_sum_square_trace ρ hρ t
  have hσtr := class_sum_square_trace σ hσ t
  rw [← hC] at hρtr hσtr
  have hsum : ∑ x ∈ C, ∑ y ∈ C, ρ.character (x * y) =
      ∑ x ∈ C, ∑ y ∈ C, σ.character (x * y) + (C.card : ℂ) ^ 2 := by
    have hpt : ∀ x ∈ C, ∀ y ∈ C, ρ.character (x * y) = σ.character (x * y) + 1 := by
      intro x hx y hy
      linear_combination hαC x y ((hmemC x).mp hx) ((hmemC y).mp hy)
    rw [Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => hpt x hx y hy]
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    ring
  have hc : (C.card : ℂ) ≠ 0 := by
    have : t ∈ C := (hmemC t).mpr (IsConj.refl t)
    exact Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem this)
  have hχt : ρ.character t = σ.character t + 1 := by linear_combination hαt
  set d := σ.character 1
  set b := σ.character t
  have hkey : (C.card : ℂ) ^ 2 * (b - d) ^ 2 = 0 := by
    rw [hdeg, hχt] at hρtr
    rw [hsum] at hρtr
    linear_combination d * hρtr - (d + 1) * hσtr
  have hbd : b = d := by
    have h2 := (mul_eq_zero.mp hkey).resolve_left (pow_ne_zero 2 hc)
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
  have hsq : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact MonoidHom.mem_ker.mpr
      (TwoRankLowerBound.Helpers.representation_involution_eq_one_of_character_eq_degree ρ t hsq
        (by rw [hχt, hdeg, hbd]))
  · exact MonoidHom.mem_ker.mpr
      (TwoRankLowerBound.Helpers.representation_involution_eq_one_of_character_eq_degree σ t hsq
        hbd)

end CFSG.DihedralTIFusion
