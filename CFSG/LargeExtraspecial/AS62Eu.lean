module

public import CFSG.LargeExtraspecial.AS35DHDefs
public import CFSG.LargeExtraspecial.AS35DSixThreeA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Asc77

namespace AS62

variable {G : Type} [Group G] (S : Setting G)

abbrev Gamma (u : G) : Set G := S.zConj (centralizer ({u} : Set G))

theorem self_mem_Gamma (u : G) : S.z ∈ Gamma S u := self_mem_conjIn _ _

theorem conj_mem_Gamma {u c x : G} (hc : c ∈ centralizer ({u} : Set G)) (hx : x ∈ Gamma S u) :
    c * x * c⁻¹ ∈ Gamma S u :=
  conj_mem_conjIn_of_mem hc hx

theorem mul_self_of_mem_Gamma {u x : G} (hx : x ∈ Gamma S u) : x * x = 1 := by
  obtain ⟨c, -, rfl⟩ := hx
  rw [show c * S.z * c⁻¹ * (c * S.z * c⁻¹) = c * (S.z * S.z) * c⁻¹ by group, S.z_mul_z]
  group

theorem commute_u_of_mem_Gamma {u x : G} (hu : u ∈ S.QG) (hx : x ∈ Gamma S u) :
    x * u = u * x := by
  obtain ⟨c, hc, rfl⟩ := hx
  have h1 : c * u = u * c := mem_centralizer_singleton_iff.mp hc
  have h2 : u * S.z = S.z * u := S.z_comm_QG hu
  have h3 : c⁻¹ * u = u * c⁻¹ := by
    calc c⁻¹ * u = c⁻¹ * (u * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * u) * c⁻¹ := by rw [h1]
      _ = u * c⁻¹ := by group
  calc c * S.z * c⁻¹ * u = c * S.z * (c⁻¹ * u) := by group
    _ = c * S.z * (u * c⁻¹) := by rw [h3]
    _ = c * (S.z * u) * c⁻¹ := by group
    _ = c * (u * S.z) * c⁻¹ := by rw [h2]
    _ = (c * u) * S.z * c⁻¹ := by group
    _ = (u * c) * S.z * c⁻¹ := by rw [h1]
    _ = u * (c * S.z * c⁻¹) := by group

theorem mem_Qa_of_mem_centralizer {u c : G} (hu : u ∈ S.QG)
    (hc : c ∈ centralizer ({u} : Set G)) : u ∈ S.Qa c := by
  rw [S.Qa_eq_map]
  refine ⟨u, hu, ?_⟩
  change c * u * c⁻¹ = u
  rw [mem_centralizer_singleton_iff.mp hc]
  group

theorem Gamma_subset_oTwoCent {u : G} (hzO : S.ZInOTwo u) : Gamma S u ⊆ oTwoCent u := by
  rintro _ ⟨c, hc, rfl⟩
  exact conj_mem_oTwoCent hc hzO

variable [Finite G]

theorem sylow_map_le_M {u : G} (hu : u ∈ S.QG) (hu1 : u ≠ 1) (huz : u ≠ S.z)
    (hnc : ¬ IsConj S.z u) (T : Sylow 2 (centralizer ({u} : Set G)))
    (hT : S.QG ⊓ centralizer ({u} : Set G) ≤
      (T : Subgroup (centralizer ({u} : Set G))).map (centralizer ({u} : Set G)).subtype) :
    (T : Subgroup (centralizer ({u} : Set G))).map (centralizer ({u} : Set G)).subtype ≤ S.M :=
  S.le_M_of_isPGroup_of_cqx_le hu hu1 huz hnc (T.isPGroup'.map _) hT

theorem exists_sylow_le_M {u : G} (hu : u ∈ S.QG) (hu1 : u ≠ 1) (huz : u ≠ S.z)
    (hnc : ¬ IsConj S.z u) : ∃ T : Sylow 2 (centralizer ({u} : Set G)),
      S.QG ⊓ centralizer ({u} : Set G) ≤
          (T : Subgroup (centralizer ({u} : Set G))).map (centralizer ({u} : Set G)).subtype ∧
        (T : Subgroup (centralizer ({u} : Set G))).map (centralizer ({u} : Set G)).subtype ≤
          S.M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({u} : Set G) with hC
  have hP2 : IsPGroup 2 ((S.QG ⊓ C).subgroupOf C) :=
    (S.isPGroup_QG.to_le inf_le_left).comap_of_injective C.subtype C.subtype_injective
  obtain ⟨T, hT⟩ := hP2.exists_le_sylow
  have hle : S.QG ⊓ C ≤ (T : Subgroup C).map C.subtype := fun y hy =>
    ⟨⟨y, (mem_inf.mp hy).2⟩, hT (by rw [mem_subgroupOf]; exact hy), rfl⟩
  exact ⟨T, hle, sylow_map_le_M S hu hu1 huz hnc T hle⟩

theorem oTwoCent_le_M {u : G} (hu : u ∈ S.QG) (hu1 : u ≠ 1) (huz : u ≠ S.z)
    (hnc : ¬ IsConj S.z u) : oTwoCent u ≤ S.M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, -, hTM⟩ := exists_sylow_le_M S hu hu1 huz hnc
  rintro _ ⟨y, hy, rfl⟩
  exact hTM ⟨y, CFSG.pCore_isPGroup.le_sylow_of_normal T hy, rfl⟩

theorem mem_M_of_mem_Gamma {u : G} (hu : u ∈ S.QG) (hu1 : u ≠ 1) (huz : u ≠ S.z)
    (hnc : ¬ IsConj S.z u) (hzO : S.ZInOTwo u) {x : G} (hx : x ∈ Gamma S u) : x ∈ S.M :=
  oTwoCent_le_M S hu hu1 huz hnc (Gamma_subset_oTwoCent S hzO hx)

theorem commute_of_mem_Gamma {u : G} (hu : u ∈ S.QG) (hu1 : u ≠ 1) (huz : u ≠ S.z)
    (hnc : ¬ IsConj S.z u) (hzO : S.ZInOTwo u) {x y : G} (hx : x ∈ Gamma S u)
    (hy : y ∈ Gamma S u) : x * y = y * x := by
  obtain ⟨c, hc, rfl⟩ := hx
  have hy' : c⁻¹ * y * c⁻¹⁻¹ ∈ oTwoCent u :=
    conj_mem_oTwoCent (inv_mem hc) (Gamma_subset_oTwoCent S hzO hy)
  have h := S.mem_M_iff.mp (oTwoCent_le_M S hu hu1 huz hnc hy')
  calc c * S.z * c⁻¹ * y = c * (S.z * (c⁻¹ * y * c⁻¹⁻¹)) * c⁻¹ := by group
    _ = c * (c⁻¹ * y * c⁻¹⁻¹ * S.z) * c⁻¹ := by rw [← h]
    _ = y * (c * S.z * c⁻¹) := by group

end AS62

end CFSG.LargeExtraspecial
