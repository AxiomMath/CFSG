module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualHigherTrace
public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem outerCommutative_of_outer_comm {G : Type*} [Group G]
    (h : ∀ a b : Outer G, a * b = b * a) : OuterCommutative G := by
  intro μ θ
  have h1 := h (μ : Outer G) (θ : Outer G)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
  have h2 := (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal G).conj_mem _
    (inv_mem h1) (θ * μ)
  convert h2 using 1
  group

variable {K : Type} [Field K] [Finite K] [CharP K 2]

variable (K) in
@[expose] noncomputable def spOneEquiv :
    StatedProj (StatedSp 1 K) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
  (spProjEquivCharTwo K 1).trans (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).symm

theorem outerCommutative_statedProj_statedSp_one : OuterCommutative (StatedProj (StatedSp 1 K)) :=
  outerCommutative_of_mulEquiv (spOneEquiv K) (outerCommutative_of_outer_comm fun a b =>
    (CFSG.RankThree.PartOne.KCRootAxis.out_sl2_isCyclic (K := K)).commGroup.mul_comm a b)

theorem spTraceRead_conj_one (μ : MulAut (StatedProj (StatedSp 1 K)))
    {θ : MulAut (StatedProj (StatedSp 1 K))} {σ : K ≃+* K} (h : SpTraceRead 1 θ σ) :
    SpTraceRead 1 (μ * θ * μ⁻¹) σ :=
  spTraceRead_conj_of_outerCommutative outerCommutative_statedProj_statedSp_one μ h

omit [Finite K] in
theorem isSimpleGroup_statedProj_statedSp_one (hq : 4 ≤ Nat.card K) :
    IsSimpleGroup (StatedProj (StatedSp 1 K)) := by
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.RankThree.PartOne.KCRootAxis.sl2_isSimpleGroup hq
  exact MulEquiv.isSimpleGroup (spOneEquiv K)

theorem isPerfect_statedProj_statedSp_one (hq : 4 ≤ Nat.card K) :
    Group.IsPerfect (StatedProj (StatedSp 1 K)) := by
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
    LinearPilot.InvPlacement.isPerfect_specialLinearGroup_of_four_le hq (Fin 2)
  exact Group.IsPerfect.ofSurjective (f := (spOneEquiv K).symm.toMonoidHom)
    (spOneEquiv K).symm.surjective

end CFSG.SeitzReduction.OmegaPilot
