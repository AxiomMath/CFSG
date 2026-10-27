
module

public import CFSG.Certificates.Kernel.J4FixCSoundBase

public import CFSG.Sporadic.Schreier.J4SSylowBase1

@[expose] public section

namespace CFSG.KC.J4FixC

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ CFSG.KS.SporSch.C11 CFSG.KC.Enum
open CFSG.Sporadic.SmallF2.Native

theorem pairRep_one : PairRep 1 pidP := by
  refine ⟨1, K.one_mem, ?_, ?_⟩
  · rw [pidP, paK_mkP (by norm_num), η_zero, one_mul]
  · rw [pidP, pcK_mkP (by norm_num), ← KS.SporSch.C11.id_eq]
    exact actsBy_one

theorem pairRep_mul_η {g : J} {p a : ℕ} (hg : PairRep g p) :
    PairRep (g * η a) (mkP (paK p ^^^ appK (pcK p) a) (pcK p)) := by
  obtain ⟨k, hk, rfl, hkC⟩ := hg
  have hlt : paK p ^^^ appK (pcK p) a < 2 ^ 11 := Nat.xor_lt_two_pow (paK_lt p) (appK_lt' _ _)
  refine ⟨k, hk, ?_, by rw [pcK_mkP hlt]; exact hkC⟩
  rw [paK_mkP hlt, η_xor, ← app_eq, ← hkC a]
  group

section Gen

variable {X XI Y YI : Nat} (hX : bindWK 11 11 xColumns.toList X = true)
  (hXI : bindWK 11 11 xInvColumns.toList XI = true) (hY : bindWK 11 11 yColumns.toList Y = true)
  (hYI : bindWK 11 11 yInvColumns.toList YI = true)
include hX hXI hY hYI

theorem actsBy_word (w : List ℤ) :
    ActsBy (signedWord x y w) (unpack11 (wordColsK X XI Y YI w)) := fun a => by
  rw [← wordCols_eq hX hXI hY hYI]
  exact word_conj_η_cols w a

theorem pairRep_gen (g : List ℕ × ℕ) :
    PairRep (signedWord x y (toI g.1) * η g.2) (genP X XI Y YI g) := by
  have hact := actsBy_word hX hXI hY hYI (toI g.1)
  have hlt : appK (wordColsK X XI Y YI (toI g.1)) g.2 < 2 ^ 11 := appK_lt' _ _
  refine ⟨signedWord x y (toI g.1), signedWord_mem_K _, ?_, ?_⟩
  · simp only [genP, sN]
    rw [paK_mkP hlt, ← app_eq, ← hact g.2]
    group
  · simp only [genP, sN]
    rw [pcK_mkP hlt]
    exact hact

end Gen

end CFSG.KC.J4FixC

end
