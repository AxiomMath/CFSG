module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Components

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

open Matrix Subgroup
open scoped MatrixGroups commutatorElement

variable {K : Type*} [Field K] {n : ℕ}

theorem isQuasisimple_SL (hn : 3 ≤ n) : CFSG.IsQuasisimple SL(n, K) := by
  have hperf := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := K) hn
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := K) (n := n) (by omega) (Or.inl hn)
  refine ⟨hperf, hsimple, ?_⟩
  by_contra h
  push Not at h
  have : IsMulCommutative (SL(n, K) ⧸ center SL(n, K)) := ⟨⟨h⟩⟩
  exact Group.IsPerfect.not_isMulCommutative (SL(n, K) ⧸ center SL(n, K)) this

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem descendAut_injective (hn : 3 ≤ n) : Function.Injective (descendAut n K) := by
  rw [injective_iff_map_eq_one]
  intro e he
  have hz : ∀ g : SL(n, K), g⁻¹ * e g ∈ center SL(n, K) := by
    intro g
    have h1 := congrArg (fun φ : MulAut (projectiveSL n K) => φ (proj n K g)) he
    simp only [descendAut_proj, MulAut.one_apply] at h1
    rw [← scalars_eq_center]
    exact (QuotientGroup.eq).1 h1.symm
  have hfix : ⁅(⊤ : Subgroup SL(n, K)), ⊤⁆ ≤ (e : SL(n, K) →* SL(n, K)).eqLocus (MonoidHom.id _) := by
    rw [commutator_le]
    intro a _ b _
    show e ⁅a, b⁆ = ⁅a, b⁆
    have ea : e a = a * (a⁻¹ * e a) := by group
    have eb : e b = b * (b⁻¹ * e b) := by group
    rw [map_commutatorElement, ea, eb]
    exact commutatorElement_mul_eq ((mem_center_iff.1 (hz a) b).symm)
      ((mem_center_iff.1 (hz b) a).symm) (mem_center_iff.1 (hz b) (a⁻¹ * e a))
  have hperf := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := K) hn
  rw [← _root_.commutator_def, hperf.commutator_eq_top] at hfix
  refine MulEquiv.ext fun g => ?_
  rw [MulAut.one_apply]
  exact hfix (mem_top g)

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem descendAut_conj (g : SL(n, K)) :
    descendAut n K (MulAut.conj g) = MulAut.conj (proj n K g) := by
  ext x
  obtain ⟨h, rfl⟩ := proj_surjective n K x
  rw [descendAut_proj, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem derivedSeries_mulAut_SL_le [Finite K] (hn : 3 ≤ n) :
    derivedSeries (MulAut SL(n, K)) 3 ≤ (MulAut.conj : SL(n, K) →* MulAut SL(n, K)).range := by
  intro φ hφ
  have h1 : descendAut n K φ ∈ derivedSeries (MulAut (projectiveSL n K)) 3 :=
    map_derivedSeries_le_derivedSeries (descendAut n K) 3 ⟨φ, hφ, rfl⟩
  have htop := (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation
    (K := K) hn).1
  have hR := (standard_outer_quotients (n := n) (K := K)).2.2.2.2.2.2.2.2.2
  have h3 : derivedSeries (MulAut (projectiveSL n K)) 3 ≤
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
    simp only [derivedSeries_succ, derivedSeries_zero]
    rw [← htop]
    exact hR
  obtain ⟨p, hp⟩ := h3 h1
  obtain ⟨g, rfl⟩ := proj_surjective n K p
  exact ⟨g, descendAut_injective hn (by rw [descendAut_conj, hp])⟩

theorem isSolvable_out_SL [Finite K] (hn : 3 ≤ n) :
    Group.IsSolvable (MulAut SL(n, K) ⧸ (MulAut.conj : SL(n, K) →* MulAut SL(n, K)).range) := by
  refine ⟨⟨3, ?_⟩⟩
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective _), eq_bot_iff]
  rintro _ ⟨φ, hφ, rfl⟩
  rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact derivedSeries_mulAut_SL_le hn hφ

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
