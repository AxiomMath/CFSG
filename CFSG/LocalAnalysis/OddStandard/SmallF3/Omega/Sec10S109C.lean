module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Ch
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Cg

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Step109C_of (hW : Asc82Step109W) (hKL : Asc82StepKL) (h3 : Asc82Sec3Res10)
    (h : Asc82Res10a) (hf : Asc82Facts10) (hb : Asc82Basic10) : Asc82Step109C := by
  intro G _ _ t L S z K1 K2 g hctx
  obtain ⟨-, hz2, -⟩ := sec10D_basic hb hctx.toSec10Ctx
  have hCS := sec10C_cs hW hKL h3 h hf hb hctx
  intro k hk hs
  have e : (S ⊔ zpowers g) ⊔ zpowers z = S ⊔ zpowers g :=
    sup_eq_left.mpr (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hctx.mem_S))
  rw [e] at hs
  rcases sec10C_mem_T hz2 hctx hs with hsS | ⟨y, hy, hsy⟩
  · exact hCS k hk (Subgroup.mem_sup_left hsS)
  · exact (sec10C_part2 h hf hb hctx hCS hk hy hsy).elim

end CFSG.OddStandard.SmallF3.Omega
