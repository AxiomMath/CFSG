module

public import CFSG.RankThree.PartOne.KE.E8TwelveClasses

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE

@[expose] def e8T12BasisList : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0],
   [0, 0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 0, 0, 1, 1]]

@[expose] def e8T12Basis (j : Fin Tag.E8.rank) : Fin Tag.E8.rank → ℤ :=
  toVec Tag.E8.rank (e8T12BasisList.getD j [])

theorem e8T12BasisList_mem : ∀ j : Fin Tag.E8.rank,
    e8T12BasisList.getD j [] ∈ Tag.E8.artifactRoots := by
  decide +kernel

theorem e8T12Basis_root (j : Fin Tag.E8.rank) :
    IsRoot Tag.E8 (e8T12Basis j) :=
  isRoot_toVec (e8T12BasisList_mem j)

theorem e8T12Basis_not_twoA2 : ∀ c ∈ e8T12TwoA2Certs,
    ∀ l ∈ lineClassRoots e8T12Rows c.cls, ∀ j : Fin Tag.E8.rank,
      toVec Tag.E8.rank l ≠ e8T12Basis j := by
  decide +kernel

theorem e8T12Basis_span : Submodule.span ℤ (Set.range e8T12Basis) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun ℤ (Fin Tag.E8.rank)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  have hb : ∀ j, e8T12Basis j ∈ Submodule.span ℤ (Set.range e8T12Basis) := fun j =>
    Submodule.subset_span ⟨j, rfl⟩
  have e5 : (Pi.single 5 1 : Fin Tag.E8.rank → ℤ) = e8T12Basis 5 - e8T12Basis 4 := by
    decide +kernel
  have e6 : (Pi.single 6 1 : Fin Tag.E8.rank → ℤ) =
      e8T12Basis 6 - e8T12Basis 5 + e8T12Basis 4 := by
    decide +kernel
  have e7 : (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) =
      e8T12Basis 7 - e8T12Basis 6 + e8T12Basis 5 - e8T12Basis 4 := by
    decide +kernel
  have e0 : (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) = e8T12Basis 0 := by decide +kernel
  have e1 : (Pi.single 1 1 : Fin Tag.E8.rank → ℤ) = e8T12Basis 1 := by decide +kernel
  have e2 : (Pi.single 2 1 : Fin Tag.E8.rank → ℤ) = e8T12Basis 2 := by decide +kernel
  have e3 : (Pi.single 3 1 : Fin Tag.E8.rank → ℤ) = e8T12Basis 3 := by decide +kernel
  have e4 : (Pi.single 4 1 : Fin Tag.E8.rank → ℤ) = e8T12Basis 4 := by decide +kernel
  fin_cases i
  · exact e0 ▸ hb 0
  · exact e1 ▸ hb 1
  · exact e2 ▸ hb 2
  · exact e3 ▸ hb 3
  · exact e4 ▸ hb 4
  · exact e5 ▸ sub_mem (hb 5) (hb 4)
  · exact e6 ▸ add_mem (sub_mem (hb 6) (hb 5)) (hb 4)
  · exact e7 ▸ sub_mem (add_mem (sub_mem (hb 7) (hb 6)) (hb 5)) (hb 4)

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
