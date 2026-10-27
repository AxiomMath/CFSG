module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Cz
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporModel
public import CFSG.Sporadic.J4.QT2LocZMain

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Blueprint

theorem exists_centralizer_zJ_not_mem_Hj
    : ∃ g : J, g * zJ = zJ * g ∧ g ∉ Hj :=
  CFSG.Sporadic.J4.QT2.centralizer_z0_not_le_Hj

theorem pairsFor_J4
    : PairsFor (TypeSporadic .J4) := by
  have hloc := localPair_J4_of exists_centralizer_zJ_not_mem_Hj goodLocal_centralizer_zJ
  have hequiv : Nonempty (NativeSporadic.Carrier .J4 ≃* J) := ⟨seedEquiv j4Facts.mat⟩
  obtain ⟨e⟩ := hequiv
  have : Finite J := inferInstance
  have key := @pairsFor_of_localPair_equiv .J4 J _ this
  exact key e hloc

end CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs
