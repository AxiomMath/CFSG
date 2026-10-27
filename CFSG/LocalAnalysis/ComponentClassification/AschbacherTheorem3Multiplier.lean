module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitCentralExtension

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open scoped commutatorElement

variable {E : Type*} [Group E] [Finite E]

theorem central_two_kernel_cyclic_of_sylow_two_generated (hE : commutator E = ⊤)
    {K : Subgroup E} (hKc : K ≤ Subgroup.center E) (hK2 : IsPGroup 2 K) (P : Sylow 2 E)
    {x y : E} (hx : x ∈ (P : Subgroup E)) (hy : y ∈ (P : Subgroup E))
    (hgen : (P : Subgroup E) ≤ Subgroup.closure {x, y} ⊔ K)
    (hab : ∀ a ∈ (P : Subgroup E), ∀ b ∈ (P : Subgroup E), ⁅a, b⁆ ∈ K) :
    IsCyclic K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Pg := (P : Subgroup E) with hPgdef
  have hKn : K.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [(Subgroup.mem_center_iff.mp (hKc hn) g), mul_inv_cancel_right]
    exact hn
  have hKP : K ≤ Pg := hK2.le_sylow_of_normal P
  have hKP' : K ≤ (commutator Pg).map Pg.subtype := by
    have h := AschbacherToolkit.central_sylow_commutator P hKc hK2
    rw [hE, inf_top_eq] at h
    rw [h]
    exact inf_le_right
  set x' : Pg := ⟨x, hx⟩
  set y' : Pg := ⟨y, hy⟩
  set c : Pg := ⁅x', y'⁆ with hcdef
  have hcK : (c : E) ∈ K := hab x hx y hy
  have hcz : ∀ g : Pg, g * c = c * g := by
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hKc hcK) g
  set N : Subgroup Pg := Subgroup.zpowers c with hNdef
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hcomm : Commute g (c ^ j) := Commute.zpow_right (hcz g) j
    rw [hcomm.eq, mul_inv_cancel_right]
    exact hn
  have hKcomm : ∀ s : Pg, (s : E) ∈ K → ∀ t : Pg, ⁅s, t⁆ = 1 := by
    intro s hs t
    rw [commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hKc hs) t).symm
  have hKcomm' : ∀ s t : Pg, (t : E) ∈ K → ⁅s, t⁆ = 1 := by
    intro s t ht
    rw [← commutatorElement_inv, hKcomm t ht s, inv_one]
  set S : Set Pg := {x', y'} ∪ ((K.subgroupOf Pg : Subgroup Pg) : Set Pg) with hSdef
  have hS : Subgroup.closure S = ⊤ := by
    rw [eq_top_iff]
    intro p _
    have hle : Subgroup.closure {x, y} ⊔ K ≤ (Subgroup.closure S).map Pg.subtype := by
      refine sup_le ?_ ?_
      · rw [Subgroup.closure_le]
        rintro z (rfl | rfl)
        · exact ⟨x', Subgroup.subset_closure (Or.inl (Or.inl rfl)), rfl⟩
        · exact ⟨y', Subgroup.subset_closure (Or.inl (Or.inr rfl)), rfl⟩
      · intro z hz
        exact ⟨⟨z, hKP hz⟩, Subgroup.subset_closure (Or.inr (Subgroup.mem_subgroupOf.mpr hz)),
          rfl⟩
    obtain ⟨q, hq, hqp⟩ := hle (hgen p.2)
    rw [show p = q from Subtype.ext hqp.symm]
    exact hq
  have hc : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ ∈ N := by
    have hcN : c ∈ N := Subgroup.mem_zpowers c
    rintro s ((rfl | rfl) | hs) t ((rfl | rfl) | ht)
    · rw [commutatorElement_self]; exact N.one_mem
    · exact hcN
    · rw [hKcomm' _ _ (Subgroup.mem_subgroupOf.mp ht)]; exact N.one_mem
    · rw [← commutatorElement_inv]; exact N.inv_mem hcN
    · rw [commutatorElement_self]; exact N.one_mem
    · rw [hKcomm' _ _ (Subgroup.mem_subgroupOf.mp ht)]; exact N.one_mem
    all_goals rw [hKcomm _ (Subgroup.mem_subgroupOf.mp hs)]; exact N.one_mem
  have hP'N := AschbacherToolkit.commutator_le_of_closure_eq_top N hS hc
  have hle : K ≤ Subgroup.zpowers ⁅x, y⁆ := by
    refine hKP'.trans ?_
    rw [Subgroup.map_le_iff_le_comap]
    refine hP'N.trans ?_
    rw [hNdef, Subgroup.zpowers_le, Subgroup.mem_comap]
    exact Subgroup.mem_zpowers _
  exact isCyclic_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

end CFSG.ComponentClassification.AschbacherTheorem3
