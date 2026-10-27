module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109KLInv

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
  {g : G}

theorem sec10B_no_conj_tq (hKL : Asc82StepKL) (h3 : Asc82Sec3Res10) (h : Asc82Res10a)
    (hf : Asc82Facts10) (hq : Asc82FactQ2m) (hb : Asc82Basic10)
    (hctx : Sec109Ctx G t L S z K1 K2 g) {q : G} (hqQ : q ∈ secQ K1 K2) (hq2 : q * q = 1)
    (hqz : q ∉ zpowers z) {k : G} (hk : k⁻¹ * t * k = t * q) : False := by
  obtain ⟨hpsp, -⟩ := hb G t L S z hctx.toSec10Z
  have hqL : q ∈ L := (sec10J_Q_le hf.pockets5 hb hctx.toSec10Ctx hqQ).2
  have hqty : InducesTypeSome L q 5 1 2 (-1) :=
    hq G L hpsp z K1 K2 hctx.toSec10Z.pocket hctx.pocket1 hctx.pocket2 hctx.ne q hqQ hq2 hqz
  exact sec10C_kl_L hKL h3 h hf hb hctx hqL hqty ⟨k, hk⟩

end CFSG.OddStandard.SmallF3.Omega
