module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.SimpleType
public import CFSG.HardMathSupport.Dickson.BMRows.KFormM11Holds

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.GLTheoremA

section


theorem upD42SporLeaf_holds : UpD42SporLeaf := by
  intro S _ _ hS hnab hK name ⟨e⟩ α hpump
  obtain ⟨hα3, hα1, I, hI, hI42⟩ := hpump
  have h42 : IsCatalogLieIso (PSimple 3 I) IsD42Index := isD42_pSimple hI42
  have h2 : IsChevSimple 2 (PSimple 3 I) := isChevSimple_two_of_isD42 h42
  have hB : name = .B → CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier .B) := by
    rintro rfl
    exact CFSG.KCore.KGroupNonab.of_mulEquiv CFSG.Open.isCatalogGroup_isoInvariant hK
      ((CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .B).some.trans e.symm)
  have hM : name = .M → CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier .M) := by
    rintro rfl
    exact CFSG.KCore.KGroupNonab.of_mulEquiv CFSG.Open.isCatalogGroup_isoInvariant hK
      ((CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .M).some.trans e.symm)
  exact not_catalogIs_chev2Spor_of_isD42 lieOrderBridge_holds h42
    (CFSG.HardMathSupport.Dickson.BMRows.i1416Chev2SporListK_holds S name ⟨e⟩ hB hM 3
      Nat.prime_three (by decide) α hα3 hα1 I hI h2)

end

end CFSG.HardMathSupport.Dickson.Sec6

end
