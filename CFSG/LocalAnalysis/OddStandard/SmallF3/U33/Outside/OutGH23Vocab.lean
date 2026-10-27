module

public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open CFSG.GH74.GLS.Bg.TwoGroups

@[expose] def NoNormalTwo {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∀ N : Subgroup G, N ≤ H → H ≤ Subgroup.normalizer (N : Set G) → IsPGroup 2 N → N = ⊥

@[expose] def GH23Concl (P : Type) [Group P] : Prop :=
  Nonempty (P ≃* alternatingGroup (Fin 8)) ∨ Nonempty (P ≃* alternatingGroup (Fin 7)) ∨
  Nonempty (P ≃* Equiv.Perm (Fin 6)) ∨ Nonempty (P ≃* alternatingGroup (Fin 6)) ∨
  Nonempty (P ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) ∨
  Nonempty (P ≃* Equiv.Perm (Fin 5)) ∨ Nonempty (P ≃* alternatingGroup (Fin 5)) ∨
  Nonempty (P ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 5)) ∨
  ∃ L : Subgroup P, L.index = 2 ∧
    Nonempty (L ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 5))

theorem GH23Concl.of_mulEquiv {P Q : Type} [Group P] [Group Q] (e : P ≃* Q) (h : GH23Concl Q) :
    GH23Concl P := by
  have key : ∀ {M : Type} [Group M], Nonempty (Q ≃* M) → Nonempty (P ≃* M) :=
    fun ⟨f⟩ => ⟨e.trans f⟩
  unfold GH23Concl at h ⊢
  rcases h with h | h | h | h | h | h | h | h | h
  · exact Or.inl (key h)
  · exact Or.inr (Or.inl (key h))
  · exact Or.inr (Or.inr (Or.inl (key h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (key h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key h))))))))
  · obtain ⟨L, hL, ⟨f⟩⟩ := h
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨L.comap (e : P →* Q), ?_, ?_⟩)))))))
    · rw [Subgroup.index_comap_of_surjective L e.surjective]
      exact hL
    · exact ⟨((MulEquiv.subgroupCongr (Subgroup.comap_equiv_eq_map_symm e L)).trans
        (e.symm.subgroupMap L).symm).trans f⟩

@[expose] def gh23g5 : Equiv.Perm (Fin 8) := Fin.cycleRange 4

@[expose] def gh23g7 : Equiv.Perm (Fin 8) := Fin.cycleRange 6

theorem gh23g5_cycleType : gh23g5.cycleType = {5} := by
  show (Fin.cycleRange (4 : Fin 8)).cycleType = {5}
  rw [Fin.cycleType_cycleRange (by decide)]
  rfl

theorem gh23g7_cycleType : gh23g7.cycleType = {7} := by
  show (Fin.cycleRange (6 : Fin 8)).cycleType = {7}
  rw [Fin.cycleType_cycleRange (by decide)]
  rfl

@[expose] def Alt8Classification : Prop :=
  ∀ H : Subgroup (Equiv.Perm (Fin 8)), H ≤ alternatingGroup (Fin 8) → ¬ IsSolvable ↥H →
    NoNormalTwo H → GH23Concl ↥H

@[expose] def Alt8Rooted : Prop :=
  ∀ H : Subgroup (Equiv.Perm (Fin 8)), H ≤ alternatingGroup (Fin 8) →
    (gh23g5 ∈ H ∨ gh23g7 ∈ H) → ¬ IsSolvable ↥H → NoNormalTwo H → GH23Concl ↥H

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
