module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalStabilizerRigidityGeometry
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalStabilizerRigidity

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open scoped Pointwise

universe u v

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_nonzero_intersection {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {M W : Submodule K V}
    (hM : ∀ x ∈ M, Q x = 0) (hdim : Module.finrank K V = 2 * Module.finrank K M)
    (hrank : 2 ≤ Module.finrank K M) (hWdim : 0 < Module.finrank K W)
    (hW : elementaryStabilizer Q M ≤ elementaryStabilizer Q W) :
    ∃ z : V, z ≠ 0 ∧ z ∈ W ∧ z ∈ M := by
  classical
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hWdim
  have hx0 : (x : V) ≠ 0 := by
    intro h
    exact hx (Subtype.ext h)
  by_cases hxM : (x : V) ∈ M
  · exact ⟨x, hx0, x.property, hxM⟩
  · have hperp := totally_singular_eq_orthogonal hQ hM hdim
    have hex : ∃ u ∈ M, polar Q (x : V) u ≠ 0 := by
      by_contra! h
      apply hxM
      rw [hperp]
      apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
      intro u hu
      change polar Q u (x : V) = 0
      rw [polar_comm]
      exact h u hu
    obtain ⟨u, hu, hxu⟩ := hex
    have hu0 : (⟨u, hu⟩ : M) ≠ 0 := by
      intro h
      have huV : u = 0 := congrArg Subtype.val h
      rw [huV, polar_zero_right] at hxu
      exact hxu rfl
    obtain ⟨v, huv⟩ := exists_linearIndependent_pair_of_one_lt_finrank
      (show 1 < Module.finrank K M by omega) hu0
    have huvV : LinearIndependent K ![u, (v : V)] := by
      have heq : M.subtype ∘ ![(⟨u, hu⟩ : M), v] = ![u, (v : V)] := by
        funext i
        fin_cases i <;> rfl
      rw [← heq]
      exact huv.map' M.subtype M.ker_subtype
    let g : elementaryGroup Q :=
      ⟨eichler Q u (v : V), eichler_mem_elementaryGroup Q u (v : V)⟩
    have hg : g ∈ elementaryStabilizer Q M :=
      eichler_mem_elementaryStabilizer hM hu
        (polar_eq_zero_of_totally_singular hM hu v.property)
    have hmove : (g : V ≃ₗ[K] V) (x : V) - (x : V) =
        polar Q (x : V) u • (v : V) - polar Q (x : V) (v : V) • u := by
      change eichler Q u (v : V) (x : V) - (x : V) = _
      rw [eichler_apply (hM u hu) (polar_eq_zero_of_totally_singular hM hu v.property),
        hM (v : V) v.property, zero_mul, add_zero]
      abel
    refine ⟨(g : V ≃ₗ[K] V) (x : V) - (x : V), ?_,
      W.sub_mem (elementaryStabilizer_apply_mem (hW hg) x.property) x.property, ?_⟩
    · rw [hmove]
      intro hz
      have hrel : (-polar Q (x : V) (v : V)) • u +
          polar Q (x : V) u • (v : V) = 0 := by
        rw [neg_smul]
        calc
          -(polar Q (x : V) (v : V) • u) + polar Q (x : V) u • (v : V) =
              polar Q (x : V) u • (v : V) - polar Q (x : V) (v : V) • u := by abel
          _ = 0 := hz
      exact hxu ((LinearIndependent.pair_iff.mp huvV _ _ hrel).2)
    · rw [hmove]
      exact M.sub_mem (M.smul_mem _ v.property) (M.smul_mem _ hu)

theorem singular_le_of_nonzero_intersection {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {M W : Submodule K V}
    (hM : ∀ x ∈ M, Q x = 0)
    (hW : elementaryStabilizer Q M ≤ elementaryStabilizer Q W)
    {z : V} (hz0 : z ≠ 0) (hzW : z ∈ W) (hzM : z ∈ M) : M ≤ W := by
  classical
  intro y hy
  by_cases hdep : ∃ a : K, a • z = y
  · obtain ⟨a, rfl⟩ := hdep
    exact W.smul_mem a hzW
  · have hzy : LinearIndependent K ![z, y] :=
      (LinearIndependent.pair_iff' hz0).mpr (by simpa only [not_exists] using hdep)
    obtain ⟨p, hp⟩ := exists_dual_family hQ hzy
    have hzp : polar Q z (p 0) = 1 := by simpa using hp 0 0
    have hyp : polar Q y (p 0) = 0 := by simpa using hp 1 0
    let g : elementaryGroup Q :=
      ⟨eichler Q y (p 0), eichler_mem_elementaryGroup Q y (p 0)⟩
    have hg : g ∈ elementaryStabilizer Q M := eichler_mem_elementaryStabilizer hM hy hyp
    have hgz : (g : V ≃ₗ[K] V) z = z - y := by
      change eichler Q y (p 0) z = z - y
      rw [eichler_apply (hM y hy) hyp, polar_eq_zero_of_totally_singular hM hzM hy, hzp]
      simp
    have hzmy : z - y ∈ W := by
      rw [← hgz]
      exact elementaryStabilizer_apply_mem (hW hg) hzW
    have hy' := W.sub_mem hzW hzmy
    simpa only [sub_sub_cancel] using hy'

theorem invariant_half_dimensional_eq {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {M W : Submodule K V}
    (hM : ∀ x ∈ M, Q x = 0) (hdim : Module.finrank K V = 2 * Module.finrank K M)
    (hrank : 2 ≤ Module.finrank K M) (hWdim : Module.finrank K W = Module.finrank K M)
    (hW : elementaryStabilizer Q M ≤ elementaryStabilizer Q W) : W = M := by
  obtain ⟨z, hz0, hzW, hzM⟩ := exists_nonzero_intersection hQ hM hdim hrank
    (show 0 < Module.finrank K W by omega) hW
  exact (Submodule.eq_of_le_of_finrank_eq
    (singular_le_of_nonzero_intersection hQ hM hW hz0 hzW hzM) hWdim.symm).symm

theorem elementaryStabilizer_eq_iff {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {M N : Submodule K V}
    (hM : ∀ x ∈ M, Q x = 0) (hdim : Module.finrank K V = 2 * Module.finrank K M)
    (hrank : 2 ≤ Module.finrank K M) (hNdim : Module.finrank K N = Module.finrank K M) :
    elementaryStabilizer Q M = elementaryStabilizer Q N ↔ M = N := by
  constructor
  · intro h
    exact (invariant_half_dimensional_eq hQ hM hdim hrank hNdim h.le).symm
  · rintro rfl
    rfl

end CFSG.ComponentClassification.CatalogueBOrthogonalStabilizerRigidity
