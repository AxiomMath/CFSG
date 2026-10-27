module

public import CFSG.Certificates.NativeSchreierArrays
public import Certificates.Data.PhilipHallSp6Cover

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6Cover

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6CoverData

theorem yS_size : yS.size = 12 := rfl

theorem yBase_nodup : yBase.Nodup := by decide

theorem three_le_yS : 3 ≤ yS.size := by rw [yS_size]; norm_num

noncomputable abbrev ySub : Subgroup (Equiv.Perm (Fin 240)) :=
  (RawSchreierDatum.ofArrays 240 (by norm_num) yS 3 three_le_yS yBase yBase_nodup
    yW).originalSubgroup

noncomputable abbrev tP : Equiv.Perm (Fin 240) := permOfArr 240 tA

noncomputable abbrev iP : Equiv.Perm (Fin 240) := permOfArr 240 iA

noncomputable abbrev jP : Equiv.Perm (Fin 240) := permOfArr 240 jA

noncomputable abbrev dP (k : ℕ) : Equiv.Perm (Fin 240) := permOfArr 240 yS[k]!

noncomputable abbrev gP (k : ℕ) : Equiv.Perm (Fin 240) := permOfArr 240 gA[k]!

noncomputable abbrev RSub : Subgroup (Equiv.Perm (Fin 240)) := Subgroup.closure {iP, jP}

noncomputable abbrev CSub : Subgroup (Equiv.Perm (Fin 240)) :=
  ySub ⊓ Subgroup.centralizer {tP}

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6Cover
