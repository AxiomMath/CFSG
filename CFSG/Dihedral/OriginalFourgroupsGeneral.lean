module

public import CFSG.Dihedral.OriginalInvolutions
import all CFSG.Dihedral.BlueprintDefs

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem t_isInvolution_general :
    BenderSuzuki.PFAppendixIII.IsInvolution d.t := by
  constructor
  · intro ht
    have h := d.t_order
    simp [ht] at h
  · simpa only [d.t_order] using pow_orderOf_eq_one d.t

theorem V_isKleinFour_general (i : Fin 2) : IsKleinFour (d.V i) := by
  let u := d.s * d.r ^ i.val
  have ht := d.t_isInvolution_general
  have hu : BenderSuzuki.PFAppendixIII.IsInvolution u := by
    refine ⟨?_, d.reflection_sq i⟩
    intro h1
    exact d.reflection_not_mem_rotation i (by change u ∈ _; rw [h1]; exact Subgroup.one_mem _)
  have htu : d.t ≠ u := by
    intro h
    exact d.reflection_not_mem_rotation i (by
      change u ∈ _
      rw [← h]
      exact (Subgroup.zpowers d.r).pow_mem (Subgroup.mem_zpowers _) _)
  have huC : u ∈ d.C := by
    rw [d.decomposition]
    exact Subgroup.mem_sup_right (d.reflection_mem_sylow i)
  have hcomm : Commute d.t u := by
    have hcent : u ∈ Subgroup.centralizer ({d.t} : Set G) := by
      simpa only [d.centralizer, t] using huC
    exact (Subgroup.mem_centralizer_singleton_iff.mp hcent).symm
  let W := kleinFourOfCommutingInvolutions d.t u
    (by simpa [pow_two] using ht.2) (by simpa [pow_two] using hu.2) hcomm
  have hW : IsKleinFour W := isKleinFour_kleinFourOfCommutingInvolutions d.t u
    (by simpa [pow_two] using ht.2) (by simpa [pow_two] using hu.2)
    ht.1 hu.1 htu hcomm
  have htV : d.t ∈ d.V i := Subgroup.subset_closure (by simp)
  have huV : u ∈ d.V i := Subgroup.subset_closure (by simp [u])
  have heq : d.V i = W := by
    apply le_antisymm
    · apply (Subgroup.closure_le W).mpr
      intro x hx
      change x ∈ ({d.t, u} : Set G) at hx
      change x ∈ ({d.t * u, d.t, u, 1} : Set G)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto
    · intro x hx
      change x ∈ ({d.t * u, d.t, u, 1} : Set G) at hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact (d.V i).mul_mem htV huV
      · exact htV
      · exact huV
      · exact (d.V i).one_mem
  rwa [heq]

end CFSG.DihedralBlueprint.OriginalData
