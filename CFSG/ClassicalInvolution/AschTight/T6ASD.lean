module

public import CFSG.ClassicalInvolution.AschTight.SDStructure
public import CFSG.ClassicalInvolution.SmallCases.Rank3NormalEight
public import CFSG.ClassicalInvolution.SmallCases.Partition

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.T6A

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

theorem exists_closure_pair_eq {P Q : Subgroup G} {a : G} (hQP : Q ≤ P)
    (hcos : ∀ x ∈ P, ∀ y ∈ P, x ∉ Subgroup.zpowers a → y ∉ Subgroup.zpowers a →
      x⁻¹ * y ∈ Subgroup.zpowers a) :
    ∃ c d : G, Subgroup.closure {c, d} = Q := by
  have hcyc : IsCyclic ↥(Q ⊓ Subgroup.zpowers a) := Subgroup.isCyclic_of_le inf_le_right
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(Q ⊓ Subgroup.zpowers a))
  set c : G := (g : G) with hcdef
  have hcQ : Q ⊓ Subgroup.zpowers a = Subgroup.zpowers c := by
    apply le_antisymm
    · intro x hx
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
      have hx' : x = c ^ m := by simpa [hcdef] using (congrArg Subtype.val hm).symm
      rw [hx']
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) m
    · exact Subgroup.zpowers_le.mpr g.2
  by_cases hQa : Q ≤ Subgroup.zpowers a
  · refine ⟨c, c, ?_⟩
    rw [Set.pair_eq_singleton, ← Subgroup.zpowers_eq_closure, ← hcQ, inf_of_le_left hQa]
  · obtain ⟨d, hdQ, hda⟩ := IsConcreteLE.not_le_iff_exists.mp hQa
    have hc' : c ∈ Subgroup.closure {c, d} := Subgroup.subset_closure (Set.mem_insert c _)
    have hd' : d ∈ Subgroup.closure {c, d} :=
      Subgroup.subset_closure (Set.mem_insert_of_mem c (Set.mem_singleton d))
    have hzc : Subgroup.zpowers c ≤ Subgroup.closure {c, d} := Subgroup.zpowers_le.mpr hc'
    refine ⟨c, d, le_antisymm ?_ fun y hyQ => ?_⟩
    · rw [Subgroup.closure_le]
      intro y hy
      rcases hy with rfl | rfl
      · exact (hcQ.ge (Subgroup.mem_zpowers _)).1
      · exact hdQ
    · by_cases hya : y ∈ Subgroup.zpowers a
      · exact hzc (hcQ ▸ ⟨hyQ, hya⟩)
      · have h1 : d⁻¹ * y ∈ Q ⊓ Subgroup.zpowers a :=
          ⟨Q.mul_mem (Q.inv_mem hdQ) hyQ, hcos d (hQP hdQ) y (hQP hyQ) hda hya⟩
        rw [hcQ] at h1
        have e : y = d * (d⁻¹ * y) := by group
        rw [e]
        exact Subgroup.mul_mem _ hd' (hzc h1)

theorem sdData_inv_mul_mem_zpowers {P : Subgroup G} {a b : G} {M : ℕ} (h : SDData P a b M)
    {x y : G} (hx : x ∈ P) (hy : y ∈ P) (hxa : x ∉ Subgroup.zpowers a)
    (hya : y ∉ Subgroup.zpowers a) : x⁻¹ * y ∈ Subgroup.zpowers a := by
  rcases h.mem_or hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact absurd (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) i) hxa
  rcases h.mem_or hy with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact absurd (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) j) hya
  have e : (a ^ i * b)⁻¹ * (a ^ j * b) = b⁻¹ * a ^ (j - i) * b := by group
  have e2 : b⁻¹ * a ^ (j - i) * b = b * a ^ (j - i) * b⁻¹ := by rw [h.binv]
  rw [e, e2, h.conj_zpow]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _

theorem twoSubgroupsFourGenerated_of_sdData [Finite G] (S : Sylow 2 G) {a b : G} {M : ℕ}
    (h : SDData (S : Subgroup G) a b M) : TwoSubgroupsFourGenerated G := by
  classical
  refine fourGenerated_of_sylow S fun Q hQS => ?_
  obtain ⟨c, d, hcd⟩ := exists_closure_pair_eq hQS fun x hx y hy hxa hya =>
    sdData_inv_mul_mem_zpowers h hx hy hxa hya
  refine ⟨{c, d}, (Finset.card_insert_le _ _).trans (by simp), ?_⟩
  rw [Finset.coe_insert, Finset.coe_singleton, hcd]

end CFSG.ClassicalInvolution.Disconnected.AschTight.T6A
