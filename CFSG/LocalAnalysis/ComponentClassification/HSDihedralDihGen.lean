module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral.DihGen

open Subgroup DihedralGroup

variable {n : ℕ}

@[expose] def rotHom : Multiplicative (ZMod n) →* DihedralGroup n where
  toFun i := r (Multiplicative.toAdd i)
  map_one' := rfl
  map_mul' i j := by simp [r_mul_r]

theorem exists_closure_eq (H : Subgroup (DihedralGroup n)) :
    ∃ s : Finset (DihedralGroup n), s.card ≤ 2 ∧ closure (s : Set (DihedralGroup n)) = H := by
  classical
  have : IsCyclic (Multiplicative (ZMod n)) := inferInstance
  obtain ⟨g₀, hg₀⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := ↥(H.comap rotHom))).mp
    inferInstance
  set h₁ : DihedralGroup n := rotHom (g₀ : Multiplicative (ZMod n))
  have hh₁ : h₁ ∈ H := g₀.2
  have hrot : ∀ i : ZMod n, r i ∈ H → r i ∈ zpowers h₁ := by
    intro i hi
    have hmem : (⟨Multiplicative.ofAdd i, hi⟩ : ↥(H.comap rotHom)) ∈ zpowers g₀ := by
      rw [hg₀]; exact mem_top _
    obtain ⟨k, hk⟩ := hmem
    refine ⟨k, ?_⟩
    have := congrArg (fun x : ↥(H.comap rotHom) => rotHom (x : Multiplicative (ZMod n))) hk
    simp only [SubgroupClass.coe_zpow, map_zpow] at this
    exact this
  by_cases hs : ∃ j : ZMod n, sr j ∈ H
  · obtain ⟨j, hj⟩ := hs
    refine ⟨{h₁, sr j}, Finset.card_le_two, le_antisymm ?_ ?_⟩
    · rw [closure_le]
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hh₁
      · exact hj
    · intro x hx
      have h₁c : h₁ ∈ closure (({h₁, sr j} : Finset (DihedralGroup n)) : Set (DihedralGroup n)) :=
        subset_closure (by simp)
      have hsc : sr j ∈ closure (({h₁, sr j} : Finset (DihedralGroup n)) :
          Set (DihedralGroup n)) := subset_closure (by simp)
      rcases x with i | i
      · exact (zpowers_le.mpr h₁c) (hrot i hx)
      · have hmem : r (i - j) ∈ H := by
          have := mul_mem hj hx
          rwa [sr_mul_sr] at this
        have h' : sr i = sr j * r (i - j) := by rw [sr_mul_r]; congr 1; ring
        rw [h']
        exact mul_mem hsc ((zpowers_le.mpr h₁c) (hrot _ hmem))
  · push Not at hs
    refine ⟨{h₁}, by simp, le_antisymm ?_ ?_⟩
    · rw [closure_le]
      intro x hx
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx
      rw [hx]
      exact hh₁
    · intro x hx
      rcases x with i | i
      · have := hrot i hx
        rw [Finset.coe_singleton, ← zpowers_eq_closure]
        exact this
      · exact absurd hx (hs i)

theorem exists_closure_eq_of_equiv {G : Type*} [Group G] {D : Subgroup G}
    (e : ↥D ≃* DihedralGroup n) (H : Subgroup G) (hH : H ≤ D) :
    ∃ s : Finset G, s.card ≤ 2 ∧ closure (s : Set G) = H := by
  classical
  obtain ⟨s, hs, hcl⟩ := exists_closure_eq ((H.subgroupOf D).map e.toMonoidHom)
  refine ⟨s.image (fun x => ((e.symm x : ↥D) : G)), Finset.card_image_le.trans hs, ?_⟩
  have h1 : (closure (s : Set (DihedralGroup n))).map (D.subtype.comp e.symm.toMonoidHom) = H := by
    rw [hcl, map_map, show (D.subtype.comp e.symm.toMonoidHom).comp e.toMonoidHom = D.subtype by
      ext x; simp, subgroupOf_map_subtype, inf_of_le_left hH]
  rw [MonoidHom.map_closure] at h1
  rw [← h1, Finset.coe_image]
  rfl

end CFSG.ComponentClassification.HSDihedral.DihGen
