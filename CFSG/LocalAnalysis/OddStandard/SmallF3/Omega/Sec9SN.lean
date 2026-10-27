module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SNOdd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SNP

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82Lemma9N_of (h36 : Asc82Lemma36) (h68 : Asc82Lemma68) (hB : Asc82Sec8B)
    (hT : Asc82Tab9M) : Asc82Lemma9N := by
  intro G _ _ t L S z g B t₀ hctx
  exact ⟨sec9n_N0_le h36 hB hT hctx, sec9n_sylow_centA h36 h68 hB hT hctx,
    sec9n_sylow_cent8 h36 h68 hB hT hctx, sec9n_cent_eq h36 hT hctx.toSec9Ctx,
    sec9n_oddCore_eq h36 h68 hB hT hctx, sec9n_twoTrans h36 h68 hB hT hctx⟩

end CFSG.OddStandard.SmallF3.Omega
