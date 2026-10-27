module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.LowDimSection.Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.LowDimSection.Sections
public import CFSG.RankThree.SubgroupLists.SchurCommutant

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Matrix CFSG.RankThree.SubgroupLists MatrixGroups

@[expose] def DicksonPSLTwo : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ L : Subgroup PSL(2, ZMod p),
    Group.IsSolvable L ∨ L = ⊤ ∨ Nonempty (↥L ≃* alternatingGroup (Fin 5))

@[expose] def MitchellSpFourList : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p)),
    G ≤ CFSG.Open.StatedSp 2 (ZMod p) → CFSG.IsQuasisimple G →
    Nonempty (↥G ≃* ↥(CFSG.Open.StatedSp 2 (ZMod p))) ∨
      Nonempty (↥G ≃* SL(2, GaloisField p 2)) ∨ Nonempty (↥G ≃* SL(2, ZMod p)) ∨
      Nonempty (↥G ≃* SL(2, ZMod 5)) ∨ Nonempty (↥G ≃* SL(2, GaloisField 3 2)) ∨
      (p = 7 ∧ Nat.card (Subgroup.center G) = 2 ∧
        Nonempty ((↥G ⧸ Subgroup.center G) ≃* alternatingGroup (Fin 7)))

@[expose] def GLTwoLowDimSections : Prop :=
  ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 →
    SimpleSectionsIn (IsLowDimSimpleSection q) (GL (Fin 2) (ZMod q))

@[expose] def GLThreeQuasisimpleLowDim : Prop :=
  ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → ∀ Y : Subgroup (GL (Fin 3) (ZMod q)),
    CFSG.IsQuasisimple Y → IsIrreducibleOn Y →
      IsLowDimSimpleSection q (↥Y ⧸ Subgroup.center ↥Y)

@[expose] def SpFourQuasisimpleLowDim : Prop :=
  ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → ∀ Y : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q)),
    Y ≤ CFSG.Open.StatedSp 2 (ZMod q) → CFSG.IsQuasisimple Y →
      IsLowDimSimpleSection q (↥Y ⧸ Subgroup.center ↥Y)

@[expose] def LowDimOutSolvable : Prop :=
  ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T],
    ¬ IsMulCommutative T → IsLowDimSimpleSection q T →
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer T)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
