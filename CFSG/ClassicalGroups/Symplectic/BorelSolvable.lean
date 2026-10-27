module

public import CFSG.ClassicalGroups.Symplectic.BorelQuotientAbelian

public section

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem isSolvable_borel_sp {m : ℕ} (hm : 3 ≤ m) {F : Type} [Field F] [Finite F] [CharP F 2] :
    Group.IsSolvable ↥(borelSubgroup m F) := by
  rw [← normalizer_unipotent (r := m) (K := F)]
  let B : Subgroup (StatedSp m F) :=
    Subgroup.normalizer (unipotent m F : Set (StatedSp m F))
  change Group.IsSolvable ↥B
  have hcomm : IsMulCommutative (↥B ⧸ CFSG.pCore 2 ↥B) :=
    isMulCommutative_borel_quotient_sp (m := m) (F := F) hm B rfl
  haveI : IsMulCommutative (↥B ⧸ CFSG.pCore 2 ↥B) := hcomm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsSolvable ↥(CFSG.pCore 2 ↥B) := by
    haveI : Group.IsNilpotent ↥(CFSG.pCore 2 ↥B) :=
      IsPGroup.isNilpotent (pCore_isPGroup (p := 2) (G := ↥B))
    infer_instance
  exact Group.isSolvable_of_subgroup_quotient (CFSG.pCore 2 ↥B)

end CFSG.ClassicalGroups.Symplectic
