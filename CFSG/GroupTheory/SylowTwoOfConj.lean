module

public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type*} [Group G]

theorem exists_eq_conjSub_of_isSylowTwoOf {L P P' : Subgroup G} [Finite ↥L]
    (hP : IsSylowTwoOf P L) (hP' : IsSylowTwoOf P' L) : ∃ g ∈ L, P' = conjSub g P := by
  obtain ⟨SP, hSP⟩ := F7.isSylowTwoOf_exists_sylow hP'
  obtain ⟨SQ, hSQ⟩ := F7.isSylowTwoOf_exists_sylow hP
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥L SP SQ
  refine ⟨(g : G)⁻¹, L.inv_mem g.2, ?_⟩
  have hcoe : (SQ : Subgroup ↥L) = (conjSub (g : G) P').subgroupOf L := by
    rw [← hg, Sylow.coe_subgroup_smul, hSP]
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, mem_conjSub]
    simp [MulAut.conj_inv_apply]
  have hle : conjSub (g : G) P' ≤ L := by
    intro x hx
    rw [mem_conjSub] at hx
    have hxL : (g : G)⁻¹ * x * g ∈ L := hP'.1 hx
    have h : g * ((g : G)⁻¹ * x * g) * (g : G)⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem g.2 hxL) (L.inv_mem g.2)
    rwa [show g * ((g : G)⁻¹ * x * g) * (g : G)⁻¹ = x by group] at h
  have hmap := congrArg (Subgroup.map L.subtype) hcoe
  rw [hSQ] at hmap
  rw [Subgroup.map_subgroupOf_eq_of_le (H := P) (K := L) hP.1,
    Subgroup.map_subgroupOf_eq_of_le (H := conjSub (g : G) P') (K := L) hle] at hmap
  have hconjinv := congrArg (conjSub (g : G)⁻¹) hmap.symm
  simpa [conjSub_conjSub_inv] using hconjinv

theorem eq_of_isSylowTwoOf_of_le {P Q H : Subgroup G} [Finite ↥Q] (hP : IsSylowTwoOf P H)
    (hQ : IsPGroup 2 ↥Q) (hQH : Q ≤ H) (hPQ : P ≤ Q) : Q = P := by
  haveI : Finite ↥P := Finite.of_injective _ (Subgroup.inclusion_injective hPQ)
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hP.2.1
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp hQ
  have hm := Subgroup.relIndex_mul_card (H := P) (K := Q)
  rw [inf_eq_left.mpr hPQ, ha, hb] at hm
  have hdvd : P.relIndex Q ∣ 2 ^ b := ⟨2 ^ a, hm.symm⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hodd : ¬ 2 ∣ P.relIndex H := hP.2.2
  have hk0 : k = 0 := by
    by_contra h
    have h2 : 2 ∣ P.relIndex Q := by rw [hk]; exact dvd_pow_self 2 h
    have h1 : P.relIndex Q * Q.relIndex H = P.relIndex H :=
      Subgroup.relIndex_mul_relIndex (H := P) (K := Q) (L := H) hPQ hQH
    exact hodd (h1 ▸ dvd_mul_of_dvd_left h2 _)
  have hrel1 : P.relIndex Q = 1 := by rw [hk, hk0, pow_zero]
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hrel1) hPQ

end CFSG.GroupTheory
