module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BSwSetup
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

open scoped commutatorElement

private lemma sec5b_mem_cent_coe {G : Type} [Group G] {L : Subgroup G} {z : G} (hz : z ∈ L)
    {c : ↥L} (h : c ∈ centralizer ({(⟨z, hz⟩ : ↥L)} : Set ↥L)) :
    (c : G) ∈ L ⊓ centralizer ({z} : Set G) := by
  refine ⟨c.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  have h1 : c * (⟨z, hz⟩ : ↥L) = (⟨z, hz⟩ : ↥L) * c :=
    Subgroup.mem_centralizer_singleton_iff.mp h
  exact (congrArg Subtype.val h1).symm

theorem swSetup_of_pockets {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}
    {K₁ K₂ : Subgroup G} (h₁ : Sl23PocketIn L z K₁) (h₂ : Sl23PocketIn L z K₂)
    (hcomm : ⁅K₁, K₂⁆ = ⊥) (hprod : K₁ ⊔ K₂ = twoRes (L ⊓ centralizer ({z} : Set G))) :
    SwSetup (K₁.subgroupOf L) (K₂.subgroupOf L) (⟨z, (h₁.2.1 h₁.1).1⟩ : ↥L) := by
  have hK₁L : K₁ ≤ L := h₁.2.1.trans inf_le_left
  have hK₂L : K₂ ≤ L := h₂.2.1.trans inf_le_left
  let z' : ↥L := ⟨z, (h₁.2.1 h₁.1).1⟩
  have hz : z ∈ L := (h₁.2.1 h₁.1).1
  change SwSetup (K₁.subgroupOf L) (K₂.subgroupOf L) z'
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine swPocket_of_isSL23Mod (A := K₁.subgroupOf L) (z := z') ?_ ?_ ?_
    · exact Subgroup.mem_subgroupOf.mpr h₁.1
    · intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hkK : (k : G) ∈ K₁ := Subgroup.mem_subgroupOf.mp hk
      have hkc : (k : G) * z = z * (k : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp (h₁.2.1 hkK).2
      apply Subtype.ext
      show (k : G) * z = z * (k : G)
      exact hkc
    · exact isSL23Mod_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK₁L).symm h₁.2.2.2
  · refine swPocket_of_isSL23Mod (A := K₂.subgroupOf L) (z := z') ?_ ?_ ?_
    · exact Subgroup.mem_subgroupOf.mpr h₂.1
    · intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hkK : (k : G) ∈ K₂ := Subgroup.mem_subgroupOf.mp hk
      have hkc : (k : G) * z = z * (k : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp (h₂.2.1 hkK).2
      apply Subtype.ext
      show (k : G) * z = z * (k : G)
      exact hkc
    · exact isSL23Mod_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK₂L).symm h₂.2.2.2
  · intro u hu v hv
    have huK : (u : G) ∈ K₁ := Subgroup.mem_subgroupOf.mp hu
    have hvK : (v : G) ∈ K₂ := Subgroup.mem_subgroupOf.mp hv
    have hmem : ⁅(u : G), (v : G)⁆ ∈ (⊥ : Subgroup G) := by
      rw [← hcomm]
      exact Subgroup.commutator_mem_commutator huK hvK
    have h1 : ⁅(u : G), (v : G)⁆ = 1 := Subgroup.mem_bot.mp hmem
    have h2 : (u : G) * (v : G) = (v : G) * (u : G) :=
      commutatorElement_eq_one_iff_mul_comm.mp h1
    apply Subtype.ext
    show (u : G) * (v : G) = (v : G) * (u : G)
    exact h2
  · intro o ho hodd
    have hoc : (o : G) ∈ L ⊓ centralizer ({z} : Set G) :=
      sec5b_mem_cent_coe hz ho
    have horder : Odd (orderOf (o : G)) := by rwa [Subgroup.orderOf_coe]
    have htwo : (o : G) ∈ twoRes (L ⊓ centralizer ({z} : Set G)) :=
      Subgroup.subset_closure ⟨hoc, horder⟩
    rw [← hprod] at htwo
    have hmem : o ∈ (K₁ ⊔ K₂).subgroupOf L := Subgroup.mem_subgroupOf.mpr htwo
    rwa [Subgroup.subgroupOf_sup hK₁L hK₂L] at hmem

theorem sw_conj_coe {G : Type} [Group G] {L : Subgroup G} {K₁ K₂ : Subgroup G} (h₁ : K₁ ≤ L)
    (h₂ : K₂ ≤ L) {c : ↥L}
    (h : CFSG.conjugate (K₁.subgroupOf L) c = K₂.subgroupOf L) :
    CFSG.conjugate K₁ (c : G) = K₂ := by
  ext x
  rw [mem_conjugate_iff K₁ (c : G)]
  constructor
  · intro hx
    have hxL : x ∈ L := by
      have hy : (c : G) * x * (c : G)⁻¹ ∈ L := h₁ hx
      have hxeq : x = (c : G)⁻¹ * ((c : G) * x * (c : G)⁻¹) * (c : G) := by group
      rw [hxeq]
      exact L.mul_mem (L.mul_mem (L.inv_mem c.2) hy) c.2
    let x' : ↥L := ⟨x, hxL⟩
    have hx' : c * x' * c⁻¹ ∈ K₁.subgroupOf L := by
      rw [Subgroup.mem_subgroupOf]
      show (c : G) * x * (c : G)⁻¹ ∈ K₁
      exact hx
    have hx'' : x' ∈ CFSG.conjugate (K₁.subgroupOf L) c :=
      (mem_conjugate_iff (K₁.subgroupOf L) c x').mpr hx'
    rw [h] at hx''
    exact Subgroup.mem_subgroupOf.mp hx''
  · intro hx
    let x' : ↥L := ⟨x, h₂ hx⟩
    have hx' : x' ∈ K₂.subgroupOf L := Subgroup.mem_subgroupOf.mpr hx
    rw [← h] at hx'
    have hx'' : c * x' * c⁻¹ ∈ K₁.subgroupOf L := (mem_conjugate_iff (K₁.subgroupOf L) c x').mp hx'
    have hx''' : (c : G) * x * (c : G)⁻¹ ∈ K₁ := Subgroup.mem_subgroupOf.mp hx''
    show (c : G) * x * (c : G)⁻¹ ∈ K₁
    exact hx'''

theorem sw_mem_cent_coe {G : Type} [Group G] {L : Subgroup G} {z : G} (hz : z ∈ L) {c : ↥L}
    (h : c ∈ centralizer ({(⟨z, hz⟩ : ↥L)} : Set ↥L)) :
    (c : G) ∈ L ⊓ centralizer ({z} : Set G) :=
  sec5b_mem_cent_coe hz h

end CFSG.OddStandard.SmallF3.Omega
