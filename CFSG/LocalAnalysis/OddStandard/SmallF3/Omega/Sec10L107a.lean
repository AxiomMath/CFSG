module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10BData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Statements2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma107a_of (hb : Asc82Basic10) (hB5 : Asc82FactB5) : Asc82Lemma107a := by
  intro G _ _ t L S z K1 K2 hctx
  obtain ⟨-, -, -, -, hM, φ, hperm, -⟩ := sec10BData_of hb hB5 hctx.toSec10Z
  refine ⟨φ, ?_⟩
  rw [hM]
  exact hperm

end CFSG.OddStandard.SmallF3.Omega
