module

public import CFSG.CharacterTheory.BrauerLinearThree.CentralizerSylowSemidihedral
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.OddLie.DiagBlockOrder

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie

open CFSG.Open CFSG.BrauerLinearThree

theorem exists_orderOf_sixteen_PSL_four {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0)
    (hq : Nat.card K % 4 = 3) (h16 : 16 ∣ Nat.card K ^ 2 - 1) :
    ∃ x : StatedProj (StatedSL 4 K), orderOf x = 16 := by
  obtain ⟨A, hA, -, -⟩ := exists_nonsplit_element hq (m := 3) (by simpa using h16)
  have hmem : diag22 (A, diagOneHom (Matrix.GeneralLinearGroup.det A)⁻¹) ∈ StatedSL 4 K :=
    Subgroup.subset_closure (det_diag22_det_inv A)
  obtain ⟨x, hx⟩ := exists_orderOf_statedProj_diag (H := StatedSL 4 K) A hmem
  exact ⟨x, hx.trans (by simpa using hA)⟩

end CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie
