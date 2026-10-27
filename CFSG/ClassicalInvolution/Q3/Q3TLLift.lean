module

public import CFSG.ClassicalInvolution.Orders.OrthogonalNeg
public import CFSG.ClassicalInvolution.Q3.Q3TLFam

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable {K : Type} [Field K]

theorem exists_lift_of_sq_eq_one (t : StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    (ht : t ^ 2 = 1) (ht1 : t ≠ 1) :
    ∃ g : StatedOmega (StatedQuadPlus 4 K), (QuotientGroup.mk g : StatedProj _) = t ∧
      toLinEquiv _ K g.val ∉ scalars K (Fin 4 ⊕ Fin 4 → K) ∧
      (toLinEquiv _ K g.val * toLinEquiv _ K g.val = 1 ∨
        ∀ x, toLinEquiv _ K g.val (toLinEquiv _ K g.val x) = -x) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
  refine ⟨g, rfl, fun hs => ht1 ?_, ?_⟩
  · rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, mem_statedScalars_iff]
    exact hs
  · have h2 : g ^ 2 ∈ (StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf
        (StatedOmega (StatedQuadPlus 4 K)) := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ht]
    rw [Subgroup.mem_subgroupOf, mem_statedScalars_iff, SubgroupClass.coe_pow, map_pow, sq] at h2
    have hO := toLinEquiv_mem_orthogonalGroup ((StatedOmega (StatedQuadPlus 4 K)).pow_mem g.2 2)
    rw [map_pow, sq] at hO
    have hv : ∃ v, quadPlus 4 K v ≠ 0 :=
      ⟨(plusPair K (0 : Fin 4)).e + (1 : K) • (plusPair K 0).f, by
        rw [CFSG.ClassicalInvolution.map_hypPair_add_smul]
        exact one_ne_zero⟩
    rcases CFSG.ClassicalInvolution.eq_one_or_eq_neg_of_mem_scalars h2 hO hv with h | h
    · exact Or.inl h
    · refine Or.inr fun x => ?_
      have := LinearEquiv.congr_fun h x
      rwa [LinearEquiv.mul_apply] at this

theorem smul_eq_of_sq_smul_eq_odd {A X : Type*} [Group A] [MulAction A X] {β : A}
    (hβ : Odd (orderOf β)) {x : X} (h : (β ^ 2) • x = x) : β • x = x := by
  obtain ⟨m, hm⟩ := hβ
  have h1 : β = (β ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf β + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have h2 : ∀ j : ℕ, ((β ^ 2) ^ j) • x = x := by
    intro j
    induction j with
    | zero => rw [pow_zero, one_smul]
    | succ j ih => rw [pow_succ, mul_smul, h, ih]
  rw [h1]
  exact h2 _

theorem fixFam_iff_of_smul_ne_odd [Finite K]
    (β : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 K)))) (hβ : Odd (orderOf β))
    (hβF : β • statedPointFamily (coe_quadPlus 4 K) ≠ statedPointFamily (coe_quadPlus 4 K))
    {H : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 K)))}
    (hH : H.map β.toMonoidHom = H) :
    FixFam (statedPointFamily (coe_quadPlus 4 K)) H ↔
      FixFam (conjugacyFamily
        (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (flag 4 K 4))) H := by
  set F := statedPointFamily (coe_quadPlus 4 K) with hF
  set CX := conjugacyFamily
    (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (flag 4 K 4)) with hCX
  set CXs := conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
    (Xstar 4 K (by omega))) with hCXs
  have h1 : β • F ∈ ({F, CX, CXs} : Set _) :=
    stated_pointFamily_orbit_subset (K := K) (n := 4) rfl (MulAction.mem_orbit _ β)
  have h2 : (β ^ 2) • F ∈ ({F, CX, CXs} : Set _) :=
    stated_pointFamily_orbit_subset (K := K) (n := 4) rfl (MulAction.mem_orbit _ (β ^ 2))
  have h2F : (β ^ 2) • F ≠ F := fun h => hβF (smul_eq_of_sq_smul_eq_odd hβ h)
  have h21 : (β ^ 2) • F ≠ β • F := by
    intro h
    apply hβF
    have h' := congrArg (fun 𝔊 => β⁻¹ • 𝔊) h
    simp only [smul_smul, sq, inv_mul_cancel_left, inv_mul_cancel, one_smul] at h'
    exact h'
  have hfix1 := fixFam_smul_iff β hH F
  have hfix2 : FixFam ((β ^ 2) • F) H ↔ FixFam F H := by
    rw [sq, mul_smul, fixFam_smul_iff β hH, fixFam_smul_iff β hH]
  rcases h1 with h1 | h1 | h1
  · exact absurd h1 hβF
  · rw [h1] at hfix1
    exact hfix1.symm
  · rcases h2 with h2 | h2 | h2
    · exact absurd h2 h2F
    · rw [h2] at hfix2
      exact hfix2.symm
    · exact absurd (h2.trans h1.symm) h21

theorem smul_eq_of_fixFam_point_odd [Finite K]
    (β : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 K)))) (hβ : Odd (orderOf β))
    {H : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 K)))}
    (hH : H.map β.toMonoidHom = H) (hpt : FixFam (statedPointFamily (coe_quadPlus 4 K)) H)
    (hX : ¬ FixFam (conjugacyFamily
      (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (flag 4 K 4))) H) :
    β • statedPointFamily (coe_quadPlus 4 K) = statedPointFamily (coe_quadPlus 4 K) := by
  by_contra hβF
  exact hX ((fixFam_iff_of_smul_ne_odd β hβ hβF hH).mp hpt)

end CFSG.ClassicalInvolution.Q3.Q3T
