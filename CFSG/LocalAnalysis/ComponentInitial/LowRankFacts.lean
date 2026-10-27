module

public import CFSG.LinearAlgebra.LinearGroups.CyclicSylowIndexTwo
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

theorem cyclic_abelian_center_comparison {p : ℕ} (hp : p.Prime) {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) (hnab : ∃ x y : P, x * y ≠ y * x)
    (hcyc : ∀ B : Subgroup P, IsMulCommutative B → IsCyclic B) :
    (∀ g : P, g ∉ center P → center P < zpowers g ∧ Nat.card (center P) < orderOf g) ∧
      ∀ x : P, orderOf x = p → x ∈ center P := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have key : ∀ g : P, g ∉ center P → center P < zpowers g := by
    intro g hg
    set k : Set P := insert g (center P : Set P) with hk
    have hcomm : k.Pairwise Commute := by
      intro x hx y hy _
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · exact Commute.refl _
        · exact (mem_center_iff.1 hy x)
      · exact (mem_center_iff.1 hx y).symm
    set C := closure k with hC
    have hCcyc : IsCyclic C := hcyc C (isMulCommutative_closure hcomm)
    have hgC : zpowers g ≤ C := (zpowers_le).2 (subset_closure (Set.mem_insert g _))
    have hZC : center P ≤ C := fun z hz => subset_closure (Set.mem_insert_of_mem g hz)
    set H := (zpowers g).subgroupOf C
    set Z := (center P).subgroupOf C
    have hHcard : Nat.card H = Nat.card (zpowers g) :=
      Nat.card_congr (subgroupOfEquivOfLe hgC).toEquiv
    have hZcard : Nat.card Z = Nat.card (center P) :=
      Nat.card_congr (subgroupOfEquivOfLe hZC).toEquiv
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 (hP.to_subgroup (zpowers g))
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 (hP.to_subgroup (center P))
    rcases le_or_gt a b with hab | hab
    ·
      exfalso
      have hle : H ≤ Z := by
        rw [IsCyclic.subgroup_le_iff_card_dvd, hHcard, hZcard, ha, hb]
        exact Nat.pow_dvd_pow p hab
      exact hg (hle (show (⟨g, hgC (mem_zpowers g)⟩ : C) ∈ H from mem_zpowers g))
    · have hle : Z ≤ H := by
        rw [IsCyclic.subgroup_le_iff_card_dvd, hHcard, hZcard, ha, hb]
        exact Nat.pow_dvd_pow p hab.le
      refine lt_of_le_of_ne (fun z hz => ?_) fun h => hg (h ▸ mem_zpowers g)
      exact hle (show (⟨z, hZC hz⟩ : C) ∈ Z from hz)
  refine ⟨fun g hg => ⟨key g hg, ?_⟩, fun x hx => ?_⟩
  · rw [← Nat.card_zpowers]
    exact card_lt_of_lt (key g hg)
  · by_contra hxZ
    have hlt := card_lt_of_lt (key x hxZ)
    rw [Nat.card_zpowers, hx] at hlt
    have : Nontrivial P := by
      obtain ⟨u, v, huv⟩ := hnab
      exact ⟨⟨u * v, v * u, huv⟩⟩
    have hZnt : Nontrivial (center P) := hP.center_nontrivial
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 (hP.to_subgroup (center P))
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hb
      exact (Finite.one_lt_card_iff_nontrivial.2 hZnt).ne' hb
    rw [hb] at hlt
    exact absurd hlt (not_lt.2 (Nat.le_self_pow hb0 p))

theorem perfect_even_sylow_noncyclic {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    (hG : Even (Nat.card G)) (S : Sylow 2 G) : ¬ IsCyclic S := by
  classical
  intro hS
  have := Fintype.ofFinite G
  have hG' : Even (Fintype.card G) := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨-, -, -, hidx⟩ := CFSG.LinearGroups.cyclic_sylow_index_two hG' S hS
  set ε : G →* ℤˣ := Equiv.Perm.sign.comp (MulAction.toPermHom G G)
  have hker : ε.ker = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := G)]
    exact Abelianization.commutator_subset_ker ε
  rw [hker, index_top] at hidx
  exact absurd hidx (by norm_num)

end CFSG.LocalAnalysis.ComponentInitial
