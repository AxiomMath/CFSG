module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OP4Comm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OP4Two

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] [Finite G] {X : Type} [Group X]

theorem sec5op4_rho_commutator
    {z : G} {T : Subgroup G} {π : ↥(centralizer ({z} : Set G)) →* X}
    (hπ : Function.Surjective π)
    (hA : Sec5GCaseI (sec5op_Tb z T π) ∨ Sec5GCaseII (sec5op_Tb z T π))
    {K : Subgroup G} (hKH : K ≤ centralizer ({z} : Set G))
    (hKT : ∀ k ∈ K, ∀ a ∈ T, k * a * k⁻¹ = a) {q : G} (hq : q ∈ ⁅K, K⁆)
    (hqH : q ∈ centralizer ({z} : Set G)) :
    sec5op_rho z T π ⟨q, hqH⟩ = 1 := by
  haveI : Finite X := Finite.of_surjective π hπ
  have hD : ∀ d ∈ (K.subgroupOf (centralizer ({z} : Set G))).map π,
      ∀ a ∈ sec5op_Tb z T π, d * a * d⁻¹ = a := by
    intro d hd a ha
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hd
    have ha' : a ∈ (T.subgroupOf (centralizer ({z} : Set G))).map π := by
      simpa only [sec5op_Tb] using ha
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp ha'
    have hkt : k * t * k⁻¹ = t := by
      apply Subtype.ext
      exact hKT (k : G) (Subgroup.mem_subgroupOf.mp hk)
        (t : G) (Subgroup.mem_subgroupOf.mp ht)
    calc
      π k * π t * (π k)⁻¹ = π (k * t * k⁻¹) := by rw [map_mul, map_inv, map_mul]
      _ = π t := by rw [hkt]
  have hρ : ∀ (g : X)
      (m : ↥(normalClosure ((sec5op_Tb z T π : Subgroup X) : Set X))),
      sec5op_act (sec5op_Tb z T π) g (sec5g_pi (sec5op_Tb z T π) m) =
        sec5g_pi (sec5op_Tb z T π) (MulAut.conjNormal g m) := by
    intro g m
    obtain ⟨h, rfl⟩ := hπ g
    exact sec5op_rho_mk h m
  have hker : ⁅(K.subgroupOf (centralizer ({z} : Set G))).map π,
        (K.subgroupOf (centralizer ({z} : Set G))).map π⁆ ≤
      (sec5op_act (sec5op_Tb z T π)).ker :=
    sec5op4_comm_le_ker hA (sec5op_act (sec5op_Tb z T π)) hρ hD
  have hqKh : (⟨q, hqH⟩ : ↥(centralizer ({z} : Set G))) ∈
      ⁅K.subgroupOf (centralizer ({z} : Set G)),
        K.subgroupOf (centralizer ({z} : Set G))⁆ := by
    have hmap : (⁅K.subgroupOf (centralizer ({z} : Set G)),
          K.subgroupOf (centralizer ({z} : Set G))⁆).map
          (centralizer ({z} : Set G)).subtype = ⁅K, K⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKH]
    rw [← hmap] at hq
    obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.mp hq
    rw [← show x = ⟨q, hqH⟩ from Subtype.ext hxq]
    exact hx
  have hqD : π ⟨q, hqH⟩ ∈ ⁅(K.subgroupOf (centralizer ({z} : Set G))).map π,
      (K.subgroupOf (centralizer ({z} : Set G))).map π⁆ := by
    have hmap2 : (⁅K.subgroupOf (centralizer ({z} : Set G)),
          K.subgroupOf (centralizer ({z} : Set G))⁆).map π =
        ⁅(K.subgroupOf (centralizer ({z} : Set G))).map π,
          (K.subgroupOf (centralizer ({z} : Set G))).map π⁆ :=
      Subgroup.map_commutator (K.subgroupOf (centralizer ({z} : Set G)))
        (K.subgroupOf (centralizer ({z} : Set G))) π
    rw [← hmap2]
    exact Subgroup.mem_map_of_mem π hqKh
  have hmem : π ⟨q, hqH⟩ ∈ (sec5op_act (sec5op_Tb z T π)).ker := hker hqD
  rw [MonoidHom.mem_ker] at hmem
  exact hmem

theorem sec5op4_rho_twoCore
    {z : G} {T : Subgroup G} {π : ↥(centralizer ({z} : Set G)) →* X}
    (hπ : Function.Surjective π)
    (hA : Sec5GCaseI (sec5op_Tb z T π) ∨ Sec5GCaseII (sec5op_Tb z T π))
    {K : Subgroup G} (hKH : K ≤ centralizer ({z} : Set G))
    (hKT : ∀ k ∈ K, ∀ a ∈ T, k * a * k⁻¹ = a) (hK : twoRes K = K) {q : G}
    (hq : q ∈ twoCoreIn K) (hqH : q ∈ centralizer ({z} : Set G)) :
    sec5op_rho z T π ⟨q, hqH⟩ = 1 := by
  exact sec5op4_rho_commutator hπ hA hKH hKT
    (sec5op4_twoCore_le_commutator hK hq) hqH

end CFSG.OddStandard.SmallF3.Omega