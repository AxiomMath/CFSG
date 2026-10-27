module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5Inputs

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ABGLocalTools

@[expose] def Foote5TwoSubgroupOverInner : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], FooteSimpleType Y →
    ∀ (R : Sylow 2 Y) (P : Subgroup (MulAut Y)), IsPGroup 2 P →
      (R : Subgroup Y).map (MulAut.conj : Y →* MulAut Y) ≤ P →
      (Nat.card P ≤ 2 * Nat.card R ∧
        (AschbacherTheorem3.IsDihedralTwoGroup P ∨ AschbacherTheorem3.IsSemidihedralTwoGroup P)) ∨
      ∃ β ∈ P, β * β = 1 ∧ β ∉ innAut5 Y ∧ ∃ R' : Sylow 2 Y, ∀ r ∈ (R' : Subgroup Y), β r = r

end CFSG.ComponentClassification.Foote5
