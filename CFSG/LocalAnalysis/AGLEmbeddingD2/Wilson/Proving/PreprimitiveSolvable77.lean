module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.AbelianTransitive77
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

open Equiv MulAction

theorem card_mulAut_eq_sixty_of_abelian_transitive_77 (A : Subgroup (Equiv.Perm (Fin 77)))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (htrans : ∀ i j : Fin 77, ∃ a ∈ A, a i = j) : Nat.card (MulAut A) = 60 := by
  have := isCyclic_of_abelian_transitive_77 A hcomm htrans
  have hcard : Nat.card A = 77 := card_eq_of_abelian_transitive A hcomm htrans 0
  rw [IsCyclic.card_mulAut, hcard]
  decide

theorem fixedPoints_ne_univ_of_ne_bot {G : Subgroup (Equiv.Perm (Fin 77))}
    {D : Subgroup G} (hD : D ≠ ⊥) : MulAction.fixedPoints D (Fin 77) ≠ Set.univ := by
  intro hfix
  apply hD
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  apply Subtype.ext
  apply Equiv.ext
  intro i
  have hi : i ∈ MulAction.fixedPoints D (Fin 77) := by
    rw [hfix]
    exact Set.mem_univ i
  have h := MulAction.mem_fixedPoints.mp hi ⟨x, hx⟩
  simp only [Subgroup.coe_one, Equiv.Perm.one_apply]
  exact h

theorem eq_bot_of_normal_solvable_77 (G : Subgroup (Equiv.Perm (Fin 77)))
    [MulAction.IsPreprimitive G (Fin 77)] (S : Subgroup G) [S.Normal] [Group.IsSolvable S]
    (hG : 4620 < Nat.card G) : S = ⊥ := by
  classical
  by_contra hS
  have hex : ∃ n, derivedSeries S n = ⊥ := Group.IsSolvable.solvable
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    apply hS
    have hbot : derivedSeries S 0 = ⊥ := by
      have := Nat.find_spec hex
      rwa [h0] at this
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have h1 : (⟨x, hx⟩ : S) ∈ derivedSeries S 0 := Subgroup.mem_top _
    rw [hbot, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero hm0
  have hkne : derivedSeries S k ≠ ⊥ := fun h =>
    Nat.find_min hex (show k < Nat.find hex by omega) h
  have hkbot : derivedSeries S (k + 1) = ⊥ := by
    rw [← hk]
    exact Nat.find_spec hex
  have hcommS : ∀ x ∈ derivedSeries S k, ∀ y ∈ derivedSeries S k, x * y = y * x := by
    intro x hx y hy
    have hmem := Subgroup.commutator_mem_commutator hx hy
    rw [← derivedSeries_succ, hkbot, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  obtain ⟨D, hDdef⟩ : ∃ D : Subgroup G, D = (derivedSeries S k).map S.subtype := ⟨_, rfl⟩
  have hDnormal : D.Normal := by
    rw [hDdef]
    infer_instance
  have hDne : D ≠ ⊥ := by
    intro h
    apply hkne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxD : S.subtype x ∈ D := by
      rw [hDdef]
      exact Subgroup.mem_map_of_mem _ hx
    rw [h, Subgroup.mem_bot] at hxD
    exact Subtype.ext hxD
  have hfix : MulAction.fixedPoints D (Fin 77) ≠ Set.univ := fixedPoints_ne_univ_of_ne_bot hDne
  have hpt : MulAction.IsPretransitive D (Fin 77) :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal (N := D) hfix
  obtain ⟨φ, hφ⟩ : ∃ φ : S →* Equiv.Perm (Fin 77), φ = G.subtype.comp S.subtype := ⟨_, rfl⟩
  have hφx : ∀ x : S, φ x = ((S.subtype x : G) : Equiv.Perm (Fin 77)) := by
    intro x
    rw [hφ]
    rfl
  obtain ⟨A, hAdef⟩ : ∃ A : Subgroup (Equiv.Perm (Fin 77)),
      A = (derivedSeries S k).map φ := ⟨_, rfl⟩
  have hAle : A ≤ G := by
    intro a ha
    rw [hAdef] at ha
    obtain ⟨x, _, rfl⟩ := Subgroup.mem_map.mp ha
    rw [hφx]
    exact (S.subtype x).2
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    rw [hAdef] at ha hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul, hcommS x hx y hy]
  have hAtrans : ∀ i j : Fin 77, ∃ a ∈ A, a i = j := by
    intro i j
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D i j
    have hgD : (g : G) ∈ (derivedSeries S k).map S.subtype := by
      rw [← hDdef]
      exact g.2
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hgD
    refine ⟨φ x, ?_, ?_⟩
    · rw [hAdef]
      exact Subgroup.mem_map_of_mem φ hx
    · rw [hφx, hxg, ← hg]
      rfl
  have hAn : (A.subgroupOf G).Normal := by
    have hAD : A.subgroupOf G = D := by
      ext g
      rw [Subgroup.mem_subgroupOf, hAdef]
      constructor
      · intro hg
        obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hg
        rw [hDdef]
        refine Subgroup.mem_map.mpr ⟨x, hx, Subtype.ext ?_⟩
        rw [hφx] at hxeq
        exact hxeq
      · intro hg
        rw [hDdef] at hg
        obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hg
        refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
        rw [hφx, hxg]
    rw [hAD]
    exact hDnormal
  have hbound := card_le_of_abelian_transitive_normal G A hAle hAn hAcomm hAtrans
  rw [card_mulAut_eq_sixty_of_abelian_transitive_77 A hAcomm hAtrans,
    card_eq_of_abelian_transitive A hAcomm hAtrans 0] at hbound
  omega

end CFSG.AGLEmbeddingD2.Wilson.Proving

end
