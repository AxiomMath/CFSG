module

public import CFSG.RankThree.PartOne.KC.UnitaryRigidityScalar
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryBasic

public section

namespace CFSG.AGLEmbedding.UnitaryLevi

open CFSG.AGLEmbedding CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LinearGroups CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryScalar
  Matrix Polynomial

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

omit [Finite K] [CharP K 2] in
theorem toStatedSU_mem (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    {g : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (hg : g ∈ sesqSpecialUnitaryGroup
      (stdHermForm (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) n)) :
    (GeneralLinearGroup.toLin (n := Fin n) (R := K)).symm g ∈ StatedSU n (2 ^ f) K := by
  have h := ToralCensus.unitaryFieldData_of_card_eq_sq hK hf
  set A := GeneralLinearGroup.toLin.symm g with hAdef
  have hgA : g = GeneralLinearGroup.toLin A := (MulEquiv.apply_symm_apply _ _).symm
  rw [hgA, stdHermForm_eq_gramForm, toLin_mem_sesqSpecialUnitaryGroup_iff] at hg
  rwa [← unitarySU_eq_gramSU h] at hg

end CFSG.AGLEmbedding.UnitaryLevi
