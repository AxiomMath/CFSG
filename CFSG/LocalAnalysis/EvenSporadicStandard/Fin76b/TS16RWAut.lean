module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWChain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWAutCard

public section

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative

theorem pg_le_autC : Pg ≤ AutC := by
  show Subgroup.closure {g | g ∈ QPg.original.toList} ≤ AutC
  rw [Subgroup.closure_le]
  intro g hg
  obtain ⟨i, hi, rfl⟩ := RawSchreierDatum.mem_ofArrays_original.1 hg
  exact permOfArr_mem_autC (by rw [sgsArr_size]; exact hi)

end CFSG.EvenSporadicStandard.Fin76b.W16
