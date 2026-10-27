module

public import CFSG.Blueprint.ChevalleyRootsInputs

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley

abbrev T8 := ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ

set_option synthInstance.maxSize 1024 in
instance instDecidableEqT8 : DecidableEq T8 := inferInstance

@[expose] def coords (v : Fin Tag.E8.rank → ℤ) : T8 :=
  let w : Fin 8 → ℤ := v
  (w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7)

@[expose] def ofCoords (t : T8) : Fin Tag.E8.rank → ℤ :=
  (![t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2.1,
    t.2.2.2.2.2.2.2] : Fin 8 → ℤ)

@[expose] def e8Pos1 : List T8 := [
  (0, 0, 0, 0, 0, 0, 0, 1),
  (0, 0, 0, 0, 0, 0, 1, 0),
  (0, 0, 0, 0, 0, 0, 1, 1),
  (0, 0, 0, 0, 0, 1, 0, 0),
  (0, 0, 0, 0, 0, 1, 1, 0),
  (0, 0, 0, 0, 0, 1, 1, 1),
  (0, 0, 0, 0, 1, 0, 0, 0),
  (0, 0, 0, 0, 1, 1, 0, 0),
  (0, 0, 0, 0, 1, 1, 1, 0),
  (0, 0, 0, 0, 1, 1, 1, 1),
  (0, 0, 0, 1, 0, 0, 0, 0),
  (0, 0, 0, 1, 1, 0, 0, 0),
  (0, 0, 0, 1, 1, 1, 0, 0),
  (0, 0, 0, 1, 1, 1, 1, 0),
  (0, 0, 0, 1, 1, 1, 1, 1),
  (0, 0, 1, 0, 0, 0, 0, 0),
  (0, 0, 1, 1, 0, 0, 0, 0),
  (0, 0, 1, 1, 1, 0, 0, 0),
  (0, 0, 1, 1, 1, 1, 0, 0),
  (0, 0, 1, 1, 1, 1, 1, 0)]

@[expose] def e8Pos2 : List T8 := [
  (0, 0, 1, 1, 1, 1, 1, 1),
  (0, 1, 0, 0, 0, 0, 0, 0),
  (0, 1, 0, 1, 0, 0, 0, 0),
  (0, 1, 0, 1, 1, 0, 0, 0),
  (0, 1, 0, 1, 1, 1, 0, 0),
  (0, 1, 0, 1, 1, 1, 1, 0),
  (0, 1, 0, 1, 1, 1, 1, 1),
  (0, 1, 1, 1, 0, 0, 0, 0),
  (0, 1, 1, 1, 1, 0, 0, 0),
  (0, 1, 1, 1, 1, 1, 0, 0),
  (0, 1, 1, 1, 1, 1, 1, 0),
  (0, 1, 1, 1, 1, 1, 1, 1),
  (0, 1, 1, 2, 1, 0, 0, 0),
  (0, 1, 1, 2, 1, 1, 0, 0),
  (0, 1, 1, 2, 1, 1, 1, 0),
  (0, 1, 1, 2, 1, 1, 1, 1),
  (0, 1, 1, 2, 2, 1, 0, 0),
  (0, 1, 1, 2, 2, 1, 1, 0),
  (0, 1, 1, 2, 2, 1, 1, 1),
  (0, 1, 1, 2, 2, 2, 1, 0)]

@[expose] def e8Pos3 : List T8 := [
  (0, 1, 1, 2, 2, 2, 1, 1),
  (0, 1, 1, 2, 2, 2, 2, 1),
  (1, 0, 0, 0, 0, 0, 0, 0),
  (1, 0, 1, 0, 0, 0, 0, 0),
  (1, 0, 1, 1, 0, 0, 0, 0),
  (1, 0, 1, 1, 1, 0, 0, 0),
  (1, 0, 1, 1, 1, 1, 0, 0),
  (1, 0, 1, 1, 1, 1, 1, 0),
  (1, 0, 1, 1, 1, 1, 1, 1),
  (1, 1, 1, 1, 0, 0, 0, 0),
  (1, 1, 1, 1, 1, 0, 0, 0),
  (1, 1, 1, 1, 1, 1, 0, 0),
  (1, 1, 1, 1, 1, 1, 1, 0),
  (1, 1, 1, 1, 1, 1, 1, 1),
  (1, 1, 1, 2, 1, 0, 0, 0),
  (1, 1, 1, 2, 1, 1, 0, 0),
  (1, 1, 1, 2, 1, 1, 1, 0),
  (1, 1, 1, 2, 1, 1, 1, 1),
  (1, 1, 1, 2, 2, 1, 0, 0),
  (1, 1, 1, 2, 2, 1, 1, 0)]

@[expose] def e8Pos4 : List T8 := [
  (1, 1, 1, 2, 2, 1, 1, 1),
  (1, 1, 1, 2, 2, 2, 1, 0),
  (1, 1, 1, 2, 2, 2, 1, 1),
  (1, 1, 1, 2, 2, 2, 2, 1),
  (1, 1, 2, 2, 1, 0, 0, 0),
  (1, 1, 2, 2, 1, 1, 0, 0),
  (1, 1, 2, 2, 1, 1, 1, 0),
  (1, 1, 2, 2, 1, 1, 1, 1),
  (1, 1, 2, 2, 2, 1, 0, 0),
  (1, 1, 2, 2, 2, 1, 1, 0),
  (1, 1, 2, 2, 2, 1, 1, 1),
  (1, 1, 2, 2, 2, 2, 1, 0),
  (1, 1, 2, 2, 2, 2, 1, 1),
  (1, 1, 2, 2, 2, 2, 2, 1),
  (1, 1, 2, 3, 2, 1, 0, 0),
  (1, 1, 2, 3, 2, 1, 1, 0),
  (1, 1, 2, 3, 2, 1, 1, 1),
  (1, 1, 2, 3, 2, 2, 1, 0),
  (1, 1, 2, 3, 2, 2, 1, 1),
  (1, 1, 2, 3, 2, 2, 2, 1)]

@[expose] def e8Pos5 : List T8 := [
  (1, 1, 2, 3, 3, 2, 1, 0),
  (1, 1, 2, 3, 3, 2, 1, 1),
  (1, 1, 2, 3, 3, 2, 2, 1),
  (1, 1, 2, 3, 3, 3, 2, 1),
  (1, 2, 2, 3, 2, 1, 0, 0),
  (1, 2, 2, 3, 2, 1, 1, 0),
  (1, 2, 2, 3, 2, 1, 1, 1),
  (1, 2, 2, 3, 2, 2, 1, 0),
  (1, 2, 2, 3, 2, 2, 1, 1),
  (1, 2, 2, 3, 2, 2, 2, 1),
  (1, 2, 2, 3, 3, 2, 1, 0),
  (1, 2, 2, 3, 3, 2, 1, 1),
  (1, 2, 2, 3, 3, 2, 2, 1),
  (1, 2, 2, 3, 3, 3, 2, 1),
  (1, 2, 2, 4, 3, 2, 1, 0),
  (1, 2, 2, 4, 3, 2, 1, 1),
  (1, 2, 2, 4, 3, 2, 2, 1),
  (1, 2, 2, 4, 3, 3, 2, 1),
  (1, 2, 2, 4, 4, 3, 2, 1),
  (1, 2, 3, 4, 3, 2, 1, 0)]

@[expose] def e8Pos6 : List T8 := [
  (1, 2, 3, 4, 3, 2, 1, 1),
  (1, 2, 3, 4, 3, 2, 2, 1),
  (1, 2, 3, 4, 3, 3, 2, 1),
  (1, 2, 3, 4, 4, 3, 2, 1),
  (1, 2, 3, 5, 4, 3, 2, 1),
  (1, 3, 3, 5, 4, 3, 2, 1),
  (2, 2, 3, 4, 3, 2, 1, 0),
  (2, 2, 3, 4, 3, 2, 1, 1),
  (2, 2, 3, 4, 3, 2, 2, 1),
  (2, 2, 3, 4, 3, 3, 2, 1),
  (2, 2, 3, 4, 4, 3, 2, 1),
  (2, 2, 3, 5, 4, 3, 2, 1),
  (2, 2, 4, 5, 4, 3, 2, 1),
  (2, 3, 3, 5, 4, 3, 2, 1),
  (2, 3, 4, 5, 4, 3, 2, 1),
  (2, 3, 4, 6, 4, 3, 2, 1),
  (2, 3, 4, 6, 5, 3, 2, 1),
  (2, 3, 4, 6, 5, 4, 2, 1),
  (2, 3, 4, 6, 5, 4, 3, 1),
  (2, 3, 4, 6, 5, 4, 3, 2)]

@[expose] def e8PosTuples : List T8 := e8Pos1 ++ e8Pos2 ++ e8Pos3 ++ e8Pos4 ++ e8Pos5 ++ e8Pos6

@[expose] def negT (t : T8) : T8 :=
  (-t.1, -t.2.1, -t.2.2.1, -t.2.2.2.1, -t.2.2.2.2.1, -t.2.2.2.2.2.1, -t.2.2.2.2.2.2.1,
    -t.2.2.2.2.2.2.2)

@[expose] def e8Tuples : List T8 := e8PosTuples ++ e8PosTuples.map negT

theorem coords_mem : ∀ v ∈ rootFinset .E8, coords v ∈ e8Tuples := by decide +kernel

theorem ofCoords_mem : ∀ t ∈ e8Tuples, ofCoords t ∈ rootFinset .E8 := by decide +kernel

theorem e8Tuples_nodup : e8Tuples.Nodup := by decide +kernel

theorem coords_ofCoords (t : T8) : coords (ofCoords t) = t := rfl

theorem ofCoords_coords (v : Fin Tag.E8.rank → ℤ) : ofCoords (coords v) = v := by
  funext i
  fin_cases i <;> rfl

theorem ofCoords_injective : Function.Injective ofCoords :=
  Function.LeftInverse.injective coords_ofCoords

@[expose] def e8Finset : Finset (Fin Tag.E8.rank → ℤ) :=
  ⟨↑(e8Tuples.map ofCoords), e8Tuples_nodup.map ofCoords_injective⟩

theorem mem_e8Finset (v : Fin Tag.E8.rank → ℤ) : v ∈ e8Finset ↔ coords v ∈ e8Tuples := by
  show v ∈ (e8Tuples.map ofCoords) ↔ _
  rw [List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rwa [coords_ofCoords]
  · intro h
    exact ⟨coords v, h, ofCoords_coords v⟩

theorem rootFinset_E8_eq : rootFinset .E8 = e8Finset := by
  ext v
  rw [mem_e8Finset]
  constructor
  · exact coords_mem v
  · intro h
    have := ofCoords_mem _ h
    rwa [ofCoords_coords] at this

theorem mem_rootFinset_E8 (v : Fin Tag.E8.rank → ℤ) :
    v ∈ rootFinset .E8 ↔ coords v ∈ e8Tuples := by
  rw [rootFinset_E8_eq, mem_e8Finset]

instance (priority := high) fastMemE8 (v : Fin Tag.E8.rank → ℤ) : Decidable (v ∈ e8Finset) :=
  decidable_of_iff (coords v ∈ e8Tuples) (mem_e8Finset v).symm

instance (priority := high) fastMemFilterE8 (p : (Fin Tag.E8.rank → ℤ) → Prop) [DecidablePred p]
    (v : Fin Tag.E8.rank → ℤ) : Decidable (v ∈ Finset.filter p e8Finset) :=
  decidable_of_iff (v ∈ e8Finset ∧ p v) Finset.mem_filter.symm

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
