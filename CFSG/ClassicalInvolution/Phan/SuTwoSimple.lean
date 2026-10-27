module

public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
public import CFSG.RankThree.PartTwo.Sec21.Item228Census4ProofCore

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.Open CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary

theorem isSimpleGroup_Su_two {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) : IsSimpleGroup (Su K 2 f 2) := by
  obtain ⟨e⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two
    (K := K) (r := 2) (f := f) hK
  have hF : Nat.card (fixedSubfield K 2 f) = 2 ^ f := card_fixedSubfield hK
  have hs : IsSimpleGroup
      (Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield K 2 f)) :=
    CFSG.RankThree.PartTwo.Sec21.Item228Census4Proof.isSimpleGroup_SL_two_of_charTwo
      (by rw [hF]; exact hq)
  have hsSU : IsSimpleGroup (StatedSU 2 (2 ^ f) K) := e.symm.isSimpleGroup
  exact (MulEquiv.subgroupCongr (SUid_eq_statedSU (F := K) (p := 2) (f := f) hK 2)).isSimpleGroup

end CFSG.ClassicalInvolution.Phan
