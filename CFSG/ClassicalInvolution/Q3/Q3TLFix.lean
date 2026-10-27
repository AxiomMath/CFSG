module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitModel

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def FixFam (𝔉 : Set (Subgroup G)) (H : Subgroup G) : Prop := ∃ M ∈ 𝔉, H ≤ M

theorem fixFam_smul_iff (β : MulAut G) {H : Subgroup G} (hH : H.map β.toMonoidHom = H)
    (𝔉 : Set (Subgroup G)) : FixFam (β • 𝔉) H ↔ FixFam 𝔉 H := by
  constructor
  · rintro ⟨M, hM, hHM⟩
    obtain ⟨N, hN, rfl⟩ := Set.mem_smul_set.mp hM
    refine ⟨N, hN, fun h hh => ?_⟩
    have h1 : β h ∈ H := by
      rw [← hH]
      exact ⟨h, hh, rfl⟩
    obtain ⟨n, hn, hnh⟩ := hHM h1
    have hnh' : n = h := β.injective hnh
    rw [← hnh']
    exact hn
  · rintro ⟨N, hN, hHN⟩
    refine ⟨β • N, Set.smul_mem_smul_set hN, fun h hh => ?_⟩
    rw [← hH] at hh
    obtain ⟨h', hh', rfl⟩ := hh
    exact ⟨h', hHN hh', rfl⟩

theorem smul_eq_of_sq_smul_eq {A X : Type*} [Group A] [MulAction A X] {β : A} {k : ℕ}
    (hβ : β ^ (3 ^ k) = 1) {x : X} (h : (β ^ 2) • x = x) : β • x = x := by
  obtain ⟨m, hm⟩ : ∃ m, 3 ^ k = 2 * m + 1 := ⟨(3 ^ k - 1) / 2, by
    have h1 : Odd (3 ^ k) := Odd.pow (by decide)
    obtain ⟨j, hj⟩ := h1
    omega⟩
  have h1 : β = (β ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = 3 ^ k + 1 by omega, pow_succ, hβ, one_mul]
  have h2 : ∀ j : ℕ, ((β ^ 2) ^ j) • x = x := by
    intro j
    induction j with
    | zero => rw [pow_zero, one_smul]
    | succ j ih => rw [pow_succ, mul_smul, h, ih]
  rw [h1]
  exact h2 _

variable {K : Type} [Field K] [Finite K]

theorem fixFam_iff_of_smul_ne
    (β : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 K)))) {k : ℕ} (hβk : β ^ (3 ^ k) = 1)
    (hβF : β • statedPointFamily (coe_quadPlus 4 K) ≠ statedPointFamily (coe_quadPlus 4 K))
    {H : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 K)))}
    (hH : H.map β.toMonoidHom = H) :
    (FixFam (statedPointFamily (coe_quadPlus 4 K)) H ↔
      FixFam (conjugacyFamily
        (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (flag 4 K 4))) H) ∧
    (FixFam (statedPointFamily (coe_quadPlus 4 K)) H ↔
      FixFam (conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
        (Xstar 4 K (by omega)))) H) := by
  set F := statedPointFamily (coe_quadPlus 4 K) with hF
  set CX := conjugacyFamily
    (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (flag 4 K 4)) with hCX
  set CXs := conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
    (Xstar 4 K (by omega))) with hCXs
  have h1 : β • F ∈ ({F, CX, CXs} : Set _) :=
    stated_pointFamily_orbit_subset (K := K) (n := 4) rfl (MulAction.mem_orbit _ β)
  have h2 : (β ^ 2) • F ∈ ({F, CX, CXs} : Set _) :=
    stated_pointFamily_orbit_subset (K := K) (n := 4) rfl (MulAction.mem_orbit _ (β ^ 2))
  have h2F : (β ^ 2) • F ≠ F := fun h => hβF (smul_eq_of_sq_smul_eq hβk h)
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
  · rcases h2 with h2 | h2 | h2
    · exact absurd h2 h2F
    · exact absurd (h2.trans h1.symm) h21
    · rw [h1] at hfix1
      rw [h2] at hfix2
      exact ⟨hfix1.symm, hfix2.symm⟩
  · rcases h2 with h2 | h2 | h2
    · exact absurd h2 h2F
    · rw [h1] at hfix1
      rw [h2] at hfix2
      exact ⟨hfix2.symm, hfix1.symm⟩
    · exact absurd (h2.trans h1.symm) h21

theorem smul_eq_of_fixFam_point
    (β : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 K)))) {k : ℕ} (hβk : β ^ (3 ^ k) = 1)
    {H : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 K)))}
    (hH : H.map β.toMonoidHom = H) (hpt : FixFam (statedPointFamily (coe_quadPlus 4 K)) H)
    (hX : ¬ FixFam (conjugacyFamily
      (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (flag 4 K 4))) H) :
    β • statedPointFamily (coe_quadPlus 4 K) = statedPointFamily (coe_quadPlus 4 K) := by
  by_contra hβF
  exact hX ((fixFam_iff_of_smul_ne β hβk hβF hH).1.mp hpt)

theorem smul_eq_of_fixFam_solid
    (β : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 K)))) {k : ℕ} (hβk : β ^ (3 ^ k) = 1)
    {H : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 K)))}
    (hH : H.map β.toMonoidHom = H) (hpt : ¬ FixFam (statedPointFamily (coe_quadPlus 4 K)) H)
    (hX : FixFam (conjugacyFamily
      (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (flag 4 K 4))) H ∨
      FixFam (conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
        (Xstar 4 K (by omega)))) H) :
    β • statedPointFamily (coe_quadPlus 4 K) = statedPointFamily (coe_quadPlus 4 K) := by
  by_contra hβF
  obtain ⟨h1, h2⟩ := fixFam_iff_of_smul_ne β hβk hβF hH
  rcases hX with h | h
  · exact hpt (h1.mpr h)
  · exact hpt (h2.mpr h)

end CFSG.ClassicalInvolution.Q3.Q3T
