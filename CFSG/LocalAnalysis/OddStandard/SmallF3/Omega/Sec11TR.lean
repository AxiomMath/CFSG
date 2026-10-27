module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Step111TR_of (h109 : Asc82Lemma109) (hT : Asc82Step111T) : Asc82Step111TR := by
  intro G _ _ t L S z K1 K2 hctx hyp
  obtain ⟨T, hTsyl, hST⟩ := exists_isSylow2Of_ge hctx.sylow.2.1
    (le_normalizer.trans (h109 G t L S z K1 K2 hctx))
  obtain ⟨-, -, -, hTQ⟩ := hT G t L S z K1 K2 T hctx hyp hTsyl hST
  obtain ⟨R, hRsyl, hTR⟩ := exists_isSylow2Of_ge hTsyl.2.1 hTQ
  refine ⟨T, R, ?_⟩
  exact
    { toSec10Ctx := hctx
      hyp := hyp
      sylowT := hTsyl
      S_le := hST
      sylowR := hRsyl
      T_le := hTR }

end CFSG.OddStandard.SmallF3.Omega
