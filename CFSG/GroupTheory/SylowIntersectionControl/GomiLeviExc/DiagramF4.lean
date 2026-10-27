module

public import CFSG.Blueprint.Chevalley
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram

public section

namespace CFSG.GroupTheory.GomiLeviExc

open CFSG.Blueprint.Chevalley

local instance diagramF4NeZeroRank : NeZero (Tag.rank .F4) := ⟨by decide⟩

private lemma adj_f4_iff (a b : Fin (Tag.rank .F4)) :
    (TauCeti.diagramGraph (Tag.cartan .F4)).Adj a b ↔
      a.val + 1 = b.val ∨ b.val + 1 = a.val := by
  decide +revert

private lemma mem_of_lt_of_lt {C : Set (Fin (Tag.rank .F4))}
    (hC : ∀ i ∈ C, ∀ j ∈ C, Relation.ReflTransGen
      (fun a b => a ∈ C ∧ b ∈ C ∧ (TauCeti.diagramGraph (Tag.cartan .F4)).Adj a b) i j)
    {i j k : Fin (Tag.rank .F4)} (hi : i ∈ C) (hj : j ∈ C)
    (hik : i < k) (hkj : k < j) : k ∈ C := by
  have hpath := hC i hi j hj
  revert hi hik
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro hj hjk
      omega
  | head h' h ih =>
      rename_i a c
      intro ha hak
      have hcC : c ∈ C := h'.2.1
      have hac : (TauCeti.diagramGraph (Tag.cartan .F4)).Adj a c := h'.2.2
      rw [adj_f4_iff] at hac
      rcases hac with hac | hac
      · by_cases hck : c = k
        · rw [hck] at hcC
          exact hcC
        · have hck' : c < k := by omega
          exact ih hcC hck'
      · have hck' : c < k := by omega
        exact ih hcC hck'

private lemma interval_enum : ∀ s : Finset (Fin (Tag.rank .F4)),
    (∀ i ∈ s, ∀ j ∈ s, ∀ k : Fin (Tag.rank .F4), i < k → k < j → k ∈ s) ∧ 2 ≤ s.card ∧
      s ≠ Finset.univ →
    s = {0, 1} ∨ s = {1, 2} ∨ s = {2, 3} ∨ s = {0, 1, 2} ∨ s = {1, 2, 3} := by
  decide +kernel

theorem f4_connected_cases {C : Set (Fin (Tag.rank .F4))}
    (hC : ∀ i ∈ C, ∀ j ∈ C, Relation.ReflTransGen
      (fun a b => a ∈ C ∧ b ∈ C ∧ (TauCeti.diagramGraph (Tag.cartan .F4)).Adj a b) i j)
    (h2 : 2 ≤ C.ncard) (hne : C ≠ Set.univ) :
    C = {0, 1} ∨ C = {1, 2} ∨ C = {2, 3} ∨ C = {0, 1, 2} ∨ C = {1, 2, 3} := by
  obtain ⟨s, rfl⟩ : ∃ s : Finset (Fin (Tag.rank .F4)), (s : Set _) = C :=
    ⟨C.toFinite.toFinset, by simp⟩
  rw [Set.ncard_coe_finset] at h2
  have hs : ∀ i ∈ s, ∀ j ∈ s, ∀ k : Fin (Tag.rank .F4), i < k → k < j → k ∈ s :=
    fun i hi j hj k hik hkj => mem_of_lt_of_lt hC hi hj hik hkj
  have hne' : s ≠ Finset.univ := fun h => hne (by simp [h])
  rcases interval_enum s ⟨hs, h2, hne'⟩ with rfl | rfl | rfl | rfl | rfl <;> simp

end CFSG.GroupTheory.GomiLeviExc
