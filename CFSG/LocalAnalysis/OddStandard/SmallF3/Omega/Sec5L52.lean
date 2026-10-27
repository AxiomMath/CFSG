module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Center
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma52a_of (h33 : Asc82Lemma33) (h51 : Asc82Lemma51) : Asc82Lemma52a := by
  intro G _ _ t L h
  exact h33 G t L h.toSec3SettingLB L (h51 G t L h) (inFStar_of_inF h.inF)

theorem asc82Lemma52b_of (h52a : Asc82Lemma52a) : Asc82Lemma52b := by
  intro G _ _ t L h
  have hcyc := h52a G t L h
  obtain ⟨u, hu_center, hu2⟩ := sec5_exists_central_involution h.isOm6Z2
  have hu_mem : u ∈ L := (sec5_mem_centerIn_iff.mp hu_center).1
  have hu_comm : ∀ y ∈ L, u * y = y * u := (sec5_mem_centerIn_iff.mp hu_center).2
  have ht_C : t ∈ centralizer (L : Set G) := sec4_t_mem_centralizer h.toSec3Setting
  have hu_C : u ∈ centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hu_comm y hy).symm
  have hu_sq : u * u = 1 := by
    have hpow := pow_orderOf_eq_one u
    rwa [hu2, pow_two] at hpow
  have hut : u * t = t * u := (Subgroup.mem_centralizer_iff.mp ht_C) u hu_mem
  have heq : u = 1 ∨ u = t :=
    sec4_eq_of_commute hcyc hu_C ht_C hu_sq h.involution hut
  have hu_ne : u ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hu2
    norm_num at hu2
  have hu_eq_t : u = t := heq.resolve_left hu_ne
  have ht_center : t ∈ centerIn L := hu_eq_t ▸ hu_center
  have ht_L : t ∈ L := (sec5_mem_centerIn_iff.mp ht_center).1
  refine ⟨ht_L, le_antisymm ?_ ?_⟩
  · intro x hx
    have hx_center : x ∈ centerIn L :=
      sec5_twoCoreIn_le_centerIn h.component.isQuasisimple hx
    have hx2 : ∃ k : ℕ, orderOf x = 2 ^ k := by
      unfold twoCoreIn CFSG.inSubgroup at hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp
        (CFSG.pCore_isPGroup (p := 2) (G := ↥L))) ⟨y, hy⟩
      have hkG : orderOf ((y : ↥L) : G) = 2 ^ k := by
        rw [Subgroup.orderOf_coe, ← Subgroup.orderOf_mk y hy]
        exact hk
      refine ⟨k, ?_⟩
      rw [← hyx]
      exact hkG
    have hmem := sec5_mem_zpowers_of_twoElement h.isOm6Z2 hu_center hu2 hx_center hx2
    rwa [hu_eq_t] at hmem
  · simpa [hu_eq_t] using sec5_zpowers_le_twoCoreIn hu_center hu2

end CFSG.OddStandard.SmallF3.Omega
