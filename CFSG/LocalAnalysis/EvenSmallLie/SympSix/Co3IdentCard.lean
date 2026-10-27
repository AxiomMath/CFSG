module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentDefs
public meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentDefs
public meta import CFSG.Certificates.CosetTablePresented
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentCardInputs
public import Certificates.Certificate3090
public import CFSG.Certificates.CosetTableColumns
public import CFSG.Certificates.CosetTableShort

public section

namespace CFSG.EvenSmallLie.SympSix.Co3Ident

open CFSG.CosetTable

theorem vcheck0 :
    (genSub {r | r ∈ relsV.map FreeGroup.mk} (subsetOf 7 [0, 1, 2, 4, 5, 6])).FiniteIndex ∧
      (genSub {r | r ∈ relsV.map FreeGroup.mk} (subsetOf 7 [0, 1, 2, 4, 5, 6])).index ≤ 170775 :=
  Certificates.certificate3090.1
theorem vcheck1 :
    (genSub {r | r ∈ relsV1.map FreeGroup.mk} (subsetOf _ [0, 2, 3, 4, 5])).FiniteIndex ∧
      (genSub {r | r ∈ relsV1.map FreeGroup.mk} (subsetOf _ [0, 2, 3, 4, 5])).index ≤ 7560 :=
  Certificates.certificate3090.2.1
theorem vcheck2 :
    Finite (PG _ relsV2) ∧ Nat.card (PG _ relsV2) ≤ 384 :=
  Certificates.certificate3090.2.2.1

theorem vCardLe : VCardLe := by
  obtain ⟨f2, c2⟩ := vcheck2
  have : Finite (PG _ (restrictWords (subsetOf _ [0, 2, 3, 4, 5]) relsV1)) := f2
  obtain ⟨f1, c1⟩ := card_le_of_genSub_index relsV1 _ vcheck1.1 vcheck1.2
  have : Finite (PG _ (restrictWords (subsetOf 7 [0, 1, 2, 4, 5, 6]) relsV)) := f1
  obtain ⟨f0, c0⟩ := card_le_of_genSub_index relsV _ vcheck0.1 vcheck0.2
  refine ⟨f0, ?_⟩
  have := c0.trans <| Nat.mul_le_mul_left _ <| c1.trans <| Nat.mul_le_mul_left _ c2
  exact this.trans (by norm_num)

theorem vwcheck :
    (genSub {r | r ∈ relsVw.map FreeGroup.mk} (subsetOf 7 [0, 1, 2, 4, 5, 6])).FiniteIndex ∧
      (genSub {r | r ∈ relsVw.map FreeGroup.mk} (subsetOf 7 [0, 1, 2, 4, 5, 6])).index ≤ 1 :=
  Certificates.certificate3090.2.2.2

theorem mem_subsetOf_iff (i : Fin 7) : i ∈ subsetOf 7 [0, 1, 2, 4, 5, 6] ↔ i ≠ 3 := by
  revert i
  decide

theorem vwGenerated : VwGenerated := by
  obtain ⟨hfi, hidx⟩ := vwcheck
  set S := subsetOf 7 [0, 1, 2, 4, 5, 6]
  have h1 : (genSub {r : FreeGroup (Fin 7) | r ∈ relsVw.map FreeGroup.mk} S).index = 1 :=
    Nat.le_antisymm hidx (Nat.pos_of_ne_zero hfi.index_ne_zero)
  rw [Subgroup.index_eq_one] at h1
  rw [VwGenerated, ← h1, genSub]
  congr 2
  ext i
  exact (mem_subsetOf_iff i).symm

end CFSG.EvenSmallLie.SympSix.Co3Ident
