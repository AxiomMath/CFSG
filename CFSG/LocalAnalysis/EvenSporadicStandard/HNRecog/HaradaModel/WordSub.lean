module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.EnumCount

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] noncomputable def wordSubgroup (ws : List (List ℕ)) :
    Subgroup (Equiv.Perm (Fin 1408)) :=
  closure (elemW '' {w | w ∈ ws})

@[expose] noncomputable def wordSubgroupP (ws : List (List ℕ)) : Subgroup ↥P1408 :=
  (wordSubgroup ws).subgroupOf P1408

theorem wordSubgroup_le (ws : List (List ℕ)) : wordSubgroup ws ≤ P1408 :=
  closure_elemW_le ws

theorem mem_wordSubgroupP {ws : List (List ℕ)} {x : ↥P1408} :
    x ∈ wordSubgroupP ws ↔ (x : Equiv.Perm (Fin 1408)) ∈ wordSubgroup ws :=
  Iff.rfl

theorem elemW_mem_wordSubgroup {ws : List (List ℕ)} {w : List ℕ} (hw : w ∈ ws) :
    elemW w ∈ wordSubgroup ws :=
  subset_closure ⟨w, hw, rfl⟩

theorem subgroupList_size {cap m : ℕ} {ws : List (List ℕ)} (h : enumW cap m ws = true) :
    (subgroupList cap ws).size = m :=
  size_subgroupList_of_enumW h

theorem enumW_spec' {cap m : ℕ} {ws : List (List ℕ)} (h : enumW cap m ws = true) :
    Nat.card ↥(wordSubgroup ws) = m ∧
      IsEnumSet 1408 (subgroupList cap ws) (wordSubgroup ws : Set (Equiv.Perm (Fin 1408))) ∧
        (subgroupList cap ws).size = (wordSubgroup ws : Set (Equiv.Perm (Fin 1408))).ncard := by
  obtain ⟨hcard, henum⟩ := enumW_spec h
  refine ⟨hcard, henum, ?_⟩
  rw [subgroupList_size h, ← hcard]
  exact (Nat.card_coe_set_eq (wordSubgroup ws : Set (Equiv.Perm (Fin 1408)))).symm

theorem card_wordSubgroupP (ws : List (List ℕ)) :
    Nat.card ↥(wordSubgroupP ws) = Nat.card ↥(wordSubgroup ws) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe (wordSubgroup_le ws)).toEquiv

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
