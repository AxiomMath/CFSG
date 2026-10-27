module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.RootChecks
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice

def f4OrbitTable : List (List ℕ × List (Fin 4)) := [
  ([0, 0, 1, 0], [1, 0, 2, 1, 0, 2, 1, 3, 2]),
  ([0, 0, 2, 0], [1, 0, 2, 1, 2, 3, 2, 1, 2]),
  ([0, 1, 0, 0], []),
  ([0, 1, 0, 1], [1, 0, 2, 1, 3, 2, 1]),
  ([0, 1, 1, 2], [1, 0, 2, 1, 2, 3, 2, 1]),
  ([0, 2, 0, 0], [1, 2, 1, 3, 2, 1]),
  ([0, 2, 0, 2], [1, 0, 2, 1, 0, 2, 1]),
  ([0, 2, 2, 1], [1, 0, 2, 1, 0, 2, 1, 3]),
  ([1, 0, 1, 1], [1, 0, 2, 1, 2, 3]),
  ([1, 0, 2, 0], [1, 2, 1, 0, 3, 2]),
  ([1, 0, 2, 2], [1, 0, 2, 1, 2]),
  ([1, 1, 0, 1], [1, 2, 1, 0]),
  ([1, 1, 0, 2], [1, 2, 3]),
  ([1, 1, 1, 1], [1, 0, 2, 1]),
  ([1, 1, 1, 2], [1, 2, 1, 0, 3]),
  ([1, 1, 2, 1], [1, 2]),
  ([1, 1, 2, 2], [1, 0, 2, 1, 3]),
  ([1, 2, 1, 0], [1]),
  ([1, 2, 1, 1], [1, 0, 2, 1, 3, 2]),
  ([1, 2, 2, 2], [1, 0, 2, 1, 2, 3, 2]),
  ([2, 0, 1, 0], [1, 0]),
  ([2, 0, 1, 1], [1, 0, 2, 1, 0, 3, 2]),
  ([2, 0, 2, 2], [1, 0, 2, 1, 0, 2, 3, 2]),
  ([2, 1, 1, 1], [1, 0, 2, 1, 0, 2, 3]),
  ([2, 1, 2, 0], [1, 2, 1, 3, 2]),
  ([2, 1, 2, 2], [1, 0, 2, 1, 0, 2]),
  ([2, 2, 0, 1], [1, 2, 1]),
  ([2, 2, 0, 2], [1, 0, 2, 3]),
  ([2, 2, 1, 1], [1, 0, 2, 1, 0]),
  ([2, 2, 1, 2], [1, 2, 1, 3]),
  ([2, 2, 2, 1], [1, 0, 2]),
  ([2, 2, 2, 2], [1, 0, 2, 1, 0, 3])]


theorem f4OrbitTable_sound : ∀ p ∈ f4OrbitTable, ∀ i : Fin 4,
    wordMat Tag.F4 p.2 ⟨1, by decide⟩ i % 3 = ((p.1.getD i.val 0 : ℕ) : ℤ) % 3 := by
  decide +kernel

theorem f4OrbitTable_complete : ∀ a b c d : Fin 3,
    (f4ArtifactRoots.filter fun r => rootDot r [a.val, b.val, c.val, d.val] % 3 = 0).length = 12 →
      ∃ p ∈ f4OrbitTable, p.1 = [a.val, b.val, c.val, d.val] := by
  decide +kernel

theorem f4_row_orbit (k : Fin 4 → ℕ) (hk : ∀ i, k i < 3)
    (hcount : (f4ArtifactRoots.filter fun r => rootDot r (List.ofFn k) % 3 = 0).length = 12) :
    ∃ m : List (Fin 4), ∀ i : Fin 4,
      wordMat Tag.F4 m ⟨1, by decide⟩ i % 3 = ((k i : ℕ) : ℤ) % 3 := by
  have hk4 : List.ofFn k = [k 0, k 1, k 2, k 3] := rfl
  rw [hk4] at hcount
  obtain ⟨p, hp, hpk⟩ := f4OrbitTable_complete ⟨k 0, hk 0⟩ ⟨k 1, hk 1⟩ ⟨k 2, hk 2⟩ ⟨k 3, hk 3⟩
    hcount
  refine ⟨p.2, fun i => ?_⟩
  rw [f4OrbitTable_sound p hp i, hpk]
  fin_cases i <;> rfl

end CFSG.LieType.SeitzGeneration.ExcHighThree
