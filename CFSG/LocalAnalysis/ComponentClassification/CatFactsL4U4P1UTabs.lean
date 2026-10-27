module

public import Certificates.Data.CatFactsL4U4P1U43Defs

public section

namespace CFSG.ComponentClassification.HarrisLit.P1.U43

open CFSG.LieType.Multipliers.U43 Matrix CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem ptIndex_lt_two_pow (v : V) : ptIndex v < 2 ^ 32 := (ptIndex_lt v).trans (by norm_num)

theorem rep_tu_false {A : GL (Fin 4) F9} {k : ℕ}
    (hA : (A : Matrix (Fin 4) (Fin 4) F9) = matN9 k) :
    CFSG.Sporadic.Th.Rep 820 (tu k false) (perm820 A) := by
  intro i hi
  rw [idx_of_lt _ hi, tu, ap_ofFn _ hi, UInt32.toNat_ofNat', Nat.mod_eq_of_lt
    (ptIndex_lt_two_pow _)]
  show _ = (perm820 A ⟨i, hi⟩ : ℕ)
  rw [perm820_apply, hA, mulVec_eq_mv4]
  rfl

theorem rep_toTable {t : Array ℕ} {g : Equiv.Perm (Fin 820)}
    (h : CFSG.Monster.B.Co2.Rep 820 t g) : CFSG.Sporadic.Th.Rep 820 (toTable t) g := by
  intro i hi
  rw [idx_of_lt _ hi, toTable, ap_ofFn _ hi, UInt32.toNat_ofNat', h ⟨i, hi⟩]
  exact Nat.mod_eq_of_lt ((g ⟨i, hi⟩).isLt.trans (by norm_num))

end CFSG.ComponentClassification.HarrisLit.P1.U43
