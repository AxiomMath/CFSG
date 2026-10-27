module

public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralRotationInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.InvolutionCoverage

public section

namespace CFSG.Semidihedral.Principal

theorem dihedral_derived_involutions_conjugate {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    {n : ℕ} (hn : 2 ≤ n) (hS : Nonempty (DihedralGroup (2 ^ (n - 1)) ≃* (S : Subgroup G))) :
    ∃ z : (S : Subgroup G), z ∈ Subgroup.center (S : Subgroup G) ∧ orderOf z = 2 ∧
      (∀ t : G, t ∈ commutator G → orderOf t = 2 → IsConj t (z : G)) ∧
      (commutator G = ⊤ → ∀ t u : G, orderOf t = 2 → orderOf u = 2 → IsConj t u) := by
  obtain ⟨⟨r, s, hr, hs, hrel, hgen⟩, hall⟩ := dihedral_rotation_involution_structure hn hS
  obtain ⟨-, hAindex, -, ⟨hzA, hzord, hzuniq⟩, -, hzcenter, -, -, -, -⟩ :=
    hall r s hr hs hrel hgen
  have hconj : ∀ t : G, t ∈ commutator G → orderOf t = 2 →
      IsConj t ((r ^ 2 ^ (n - 2) : _) : G) := by
    intro t htD ht
    have hUS : (Subgroup.zpowers r).map (S : Subgroup G).subtype ≤ (S : Subgroup G) :=
      Subgroup.map_subtype_le _
    have hrel2 : ((Subgroup.zpowers r).map (S : Subgroup G).subtype).relIndex
        (S : Subgroup G) = 2 := by
      have hsub : ((Subgroup.zpowers r).map (S : Subgroup G).subtype).subgroupOf
          (S : Subgroup G) = Subgroup.zpowers r := by
        ext x
        rw [Subgroup.mem_subgroupOf]
        exact Subgroup.mem_map_iff_mem (f := (S : Subgroup G).subtype)
          (Subgroup.subtype_injective (S : Subgroup G))
      rw [Subgroup.relIndex, hsub, hAindex]
    obtain ⟨g, hg⟩ := ProperTwoGeneratedCore.derived_involution_sylow_maximal_transfer S _ hUS
      hrel2 t ht htD
    obtain ⟨a, ha, hag⟩ := Subgroup.mem_map.mp hg
    have ha2 : orderOf a = 2 := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.coe_subtype, hag]
      have h := (MulAut.conj g⁻¹).orderOf_eq t
      rw [MulAut.conj_apply, inv_inv] at h
      rw [h, ht]
    have haz := hzuniq a ha ha2
    refine isConj_iff.mpr ⟨g⁻¹, ?_⟩
    rw [inv_inv, ← hag, haz]
    rfl
  refine ⟨r ^ 2 ^ (n - 2), hzcenter, hzord, hconj, fun hperfect t u ht hu => ?_⟩
  have htz := hconj t (hperfect ▸ Subgroup.mem_top t) ht
  have huz := hconj u (hperfect ▸ Subgroup.mem_top u) hu
  exact htz.trans huz.symm

end CFSG.Semidihedral.Principal
