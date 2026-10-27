module

public import Certificates.Data.Kernel.HeisWordsK
public import CFSG.LieType.SeitzGeneration.HeisSmallCheck
public import CFSG.Certificates.Kernel.Common.StrSplit

public section

namespace CFSG.KC.HeisWords

open CFSG.LieType.SeitzGeneration.HeisSmall

@[expose] def dig (c : Char) : Nat := c.toNat - 48

theorem beq_comma (x : Char) : Nat.beq x.toNat 44 = (x == ',') := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]
  constructor
  · intro h
    exact Char.toNat_inj.mp (by rw [h]; rfl)
  · rintro rfl
    rfl

theorem wordsGo_eq : ∀ (l acc : List Char),
    wordsGo l (acc.map dig) = (List.splitOnPPrepend (· == ',') l acc).map (List.map dig)
  | [], acc => by simp [wordsGo]
  | x :: xs, acc => by
    rw [wordsGo, List.splitOnPPrepend_cons_eq_ite, beq_comma]
    split
    · have h := wordsGo_eq xs []
      rw [List.map_nil, List.splitOnPPrepend_nil_right] at h
      rw [List.map_cons, List.map_reverse, h]
    · exact wordsGo_eq xs (x :: acc)

theorem decodeWords_ofList (cs : List Char) : decodeWords (String.ofList cs) = decodeL cs := by
  have hc : ("," : String) = String.singleton ',' := by decide
  unfold decodeWords decodeL
  rw [hc, CFSG.KC.Str.splitOn_ofList, List.map_map]
  have h := wordsGo_eq cs []
  rw [List.map_nil, List.splitOnPPrepend_nil_right, ← List.splitOn_eq_splitOnP] at h
  rw [h]
  exact List.map_congr_left fun w _ => by simp [dig]

end CFSG.KC.HeisWords
