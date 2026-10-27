module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalZC
public import CFSG.Sporadic.Bridge.HSSurj
public import Certificates.Certificate42303

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Blueprint

theorem zcw_HS_7_native : ZCW NativeSporadic.HS 7 :=
  Certificates.certificate42303

set_option maxHeartbeats 4000000 in
theorem row_HS_7 :
    KFactSporLocalRow .HS 7 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  exact @row_of_zcw .HS 7 NativeSporadic.HS inferInstance inferInstance ⟨e⟩
    (by rw [CFSG.Sporadic.HS.card_HS]; norm_num) zcw_HS_7_native (by decide)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
