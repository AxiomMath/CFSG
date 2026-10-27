module

public import CFSG.CharacterTheory.Semidihedral.Local.FourSubgroupCentralizers
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.InvolutionCoverage
public import CFSG.CharacterTheory.Semidihedral.FusionTypes

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open

variable {G : Type*} [Group G]

theorem rotation_relIndex (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) :
    ((Subgroup.zpowers (f (r n))).map (S : Subgroup G).subtype).relIndex (S : Subgroup G) =
      2 := by
  have hsub : ((Subgroup.zpowers (f (r n))).map (S : Subgroup G).subtype).subgroupOf
      (S : Subgroup G) = Subgroup.zpowers (f (r n)) := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_map_iff_mem (S : Subgroup G).subtype_injective
  rw [Subgroup.relIndex, hsub]
  exact (supplied_index_two n hn f _).mpr (Or.inl rfl)

theorem rotation_involution_eq (n : ℕ) (hn : 4 ≤ n) {S : Type*} [Group S]
    (f : SemidihedralGroup n ≃* S) (a : S) (ha : a ∈ Subgroup.zpowers (f (r n)))
    (ha2 : orderOf a = 2) : a = f (r n) ^ 2 ^ (n - 2) := by
  have hn3 : 3 ≤ n := Nat.le_of_succ_le hn
  obtain ⟨i, e, rfl⟩ := exists_coordinates hn3 f a
  rw [image_element_mem_zpowers_r_iff] at ha
  subst ha
  rw [image_rotation_orderOf_eq_two_iff] at ha2
  rw [ha2, image_r_pow_eq hn3 f]
  rfl

theorem semidihedral_derived_involutions_conjugate [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S) :
    let r := f (CFSG.Semidihedral.r n)
    let z : G := ((r ^ 2 ^ (n - 2) : S) : G)
    orderOf z = 2 ∧
    (∀ t : G, t ∈ commutator G → orderOf t = 2 → IsConj t z) ∧
    (commutator G = ⊤ → ∀ t : G, orderOf t = 2 ↔ IsConj t z) := by
  intro r z
  have hn3 : 3 ≤ n := Nat.le_of_succ_le hn
  have hz2 : orderOf z = 2 := by
    change orderOf ((f (CFSG.Semidihedral.r n) ^ 2 ^ (n - 2) : S) : G) = 2
    rw [Subgroup.orderOf_coe, image_r_pow_eq hn3 f, image_rotation_orderOf_eq_two_iff]
    rfl
  have hconj : ∀ t : G, t ∈ commutator G → orderOf t = 2 → IsConj t z := by
    intro t htD ht
    obtain ⟨g, hg⟩ := ProperTwoGeneratedCore.derived_involution_sylow_maximal_transfer S _
      (Subgroup.map_subtype_le _) (rotation_relIndex n hn S f) t ht htD
    obtain ⟨a, ha, hag⟩ := Subgroup.mem_map.mp hg
    have ha2 : orderOf a = 2 := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.coe_subtype, hag,
        ← conjugate_orderOf_eq (isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩), ht]
    have haz := rotation_involution_eq n hn f a ha ha2
    refine isConj_iff.mpr ⟨g⁻¹, ?_⟩
    rw [inv_inv]
    change g⁻¹ * t * g = ((f (CFSG.Semidihedral.r n) ^ 2 ^ (n - 2) : S) : G)
    rw [← hag, haz]
    rfl
  refine ⟨hz2, hconj, fun hperfect t => ⟨fun ht => hconj t (hperfect ▸ Subgroup.mem_top t) ht,
    fun h => (conjugate_orderOf_eq h).trans hz2⟩⟩

end CFSG.Semidihedral.Local
