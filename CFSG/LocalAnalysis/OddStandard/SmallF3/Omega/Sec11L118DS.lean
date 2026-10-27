module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.CharacterTheory.Semidihedral.DerivedAndIndexTwo

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem exists_cyclic_relIndex_two_of_mulEquiv {D : Subgroup G} {P₀ : Type*} [Group P₀]
    (e : ↥D ≃* P₀) (Y₀ : Subgroup P₀) (hc : IsCyclic Y₀) (hidx : Y₀.index = 2) :
    ∃ Y : Subgroup G, Y ≤ D ∧ IsCyclic Y ∧ Y.relIndex D = 2 := by
  have hcyc₁ : IsCyclic (Y₀.comap (e : ↥D →* P₀)) :=
    isCyclic_of_injective ((e : ↥D →* P₀).subgroupComap Y₀)
      ((e : ↥D →* P₀).subgroupComap_injective Y₀ e.injective)
  have hidx₁ : (Y₀.comap (e : ↥D →* P₀)).index = 2 := by
    rw [Subgroup.index_comap_of_surjective Y₀ e.surjective, hidx]
  refine ⟨(Y₀.comap (e : ↥D →* P₀)).map D.subtype,
    Subgroup.map_subtype_le (Y₀.comap (e : ↥D →* P₀)), ?_, ?_⟩
  · exact (Subgroup.equivMapOfInjective _ D.subtype D.subtype_injective).isCyclic.mp hcyc₁
  · rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective D.subtype_injective]
    exact hidx₁

private theorem dihedral_rotation_cyclic_index_two (m : ℕ) (hm : 1 ≤ m) :
    IsCyclic (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup (2 ^ m))) ∧
      (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup (2 ^ m))).index = 2 := by
  refine ⟨Subgroup.isCyclic_zpowers _, ?_⟩
  have hcard :=
    (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup (2 ^ m))).card_mul_index
  rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one, DihedralGroup.nat_card] at hcard
  have hpos : 0 < 2 ^ m := Nat.pow_pos (by norm_num)
  rw [show 2 * 2 ^ m = 2 ^ m * 2 from Nat.mul_comm 2 (2 ^ m)] at hcard
  exact Nat.mul_left_cancel hpos hcard

theorem sec11_isDihSd_isPGroup [Finite G] {D : Subgroup G} (hD : IsDihSd D) : IsPGroup 2 D := by
  rcases hD with ⟨m, _, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact IsPGroup.of_card (n := m + 1) (by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, pow_succ]
      ring)
  · exact IsPGroup.of_card (n := n) (by
      rw [Nat.card_congr e.toEquiv, CFSG.Semidihedral.card n (by omega)])

theorem sec11_isDihSd_exists_cyclic {D : Subgroup G} (hD : IsDihSd D) :
    ∃ Y : Subgroup G, Y ≤ D ∧ IsCyclic Y ∧ Y.relIndex D = 2 := by
  rcases hD with ⟨m, hm, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · obtain ⟨hc, hidx⟩ := dihedral_rotation_cyclic_index_two m hm
    exact exists_cyclic_relIndex_two_of_mulEquiv e _ hc hidx
  · exact exists_cyclic_relIndex_two_of_mulEquiv e _
      (CFSG.Semidihedral.rotationSubgroup_cyclic n)
      (CFSG.Semidihedral.rotationSubgroup_index n (by omega))

end CFSG.OddStandard.SmallF3.Omega
