module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Col
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Tr1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Tr2

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup _root_.Certificates

namespace Fz410Mod

variable {G : Type} [Group G] [Finite G] {t tau lam rho s : G} {Z E W Q R T P : Subgroup G}
  {emb : FzL410.A → G} (M : Fz410Mod t tau lam rho s Z E W Q R T P emb)

include M

theorem facts (hM : FzL410.ModelFacts) : Fz410Facts t s Z E P Q R T := by
  obtain ⟨hCR, hCP, hSq, hRQ, hQC, hEF, hCent, hInv, hFus, hCS, hSL⟩ := hM
  obtain ⟨ht, hets⟩ := M.fus_transfer hFus
  exact
    { charR := M.charR_transfer hCR
      charP := M.charP_transfer hCP
      rq := M.rq_transfer hRQ
      qc := M.qc_transfer hQC
      sqZ := M.sqZ_transfer hSq
      P_comm := M.emb.P_comm
      ef := M.ef_transfer hEF
      centP := M.centP_transfer hCent
      invF := M.invF_transfer hInv
      fus_t := ht
      fus_ets := hets
      card_S := M.cardS_transfer hCS
      slem := M.slem_transfer hSL }

end Fz410Mod

end CFSG.OddStandard.SmallF3.FritzII
