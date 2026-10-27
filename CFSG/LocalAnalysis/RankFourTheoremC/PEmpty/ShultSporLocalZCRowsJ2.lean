module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalZC
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalZCJ2
public import Certificates.Certificate42302

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Blueprint

noncomputable def closureJ2abEquivNative :
    ↥(Subgroup.closure ({j2a, j2b} : Set (GL (Fin 14) (ZMod 5)))) ≃* NativeSporadic.J2 :=
  (MulEquiv.subgroupCongr closure_j2ab).trans CFSG.Sporadic.Bridge.J2.nativeEquiv.symm

theorem zcw_J2_7_native : ZCW NativeSporadic.J2 7 :=
  Certificates.certificate42302

theorem card_nativeJ2_zc : Nat.card NativeSporadic.J2 = 604800 := by
  rw [← Nat.card_congr closureJ2abEquivNative.toEquiv]
  exact card_closure_j2ab

set_option maxHeartbeats 4000000 in
theorem row_J2_7 : KFactSporLocalRow .J2 7 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  exact @row_of_zcw .J2 7 NativeSporadic.J2 inferInstance inferInstance ⟨b⟩
    (by rw [card_nativeJ2_zc]; norm_num) zcw_J2_7_native (by decide)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
