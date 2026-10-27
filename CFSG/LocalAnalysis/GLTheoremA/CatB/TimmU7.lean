module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.TimmU6
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TimmAt
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TimmU5

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Timm.UnitaryPoint

open Subgroup CFSG.Open CFSG.LocalAnalysis.GLTheoremA.S8

@[expose] def UnitaryPointIdentification : Prop :=
  ∀ (w : ℕ), 12 ≤ w → ∀ M : Subgroup ↥(timmesfeldPSU (w + 2)),
    IsMaxTwoLocalSubgroup M → IsExtraSpec2 (pCoreOf 2 M) →
      Nat.card ↥(pCoreOf 2 M) = 2 ^ (1 + 2 * w) → Nonempty (↥M ≃* ↥(Cbar w))

theorem timmesfeldUnitaryAt_of_identification (hI : UnitaryPointIdentification) :
    Timm.TimmesfeldUnitaryAt := by
  intro G _ _ hsimple _ _ w hw ⟨φ⟩ M hM hext hcard _
  have hM' : IsMaxTwoLocalSubgroup (M.map φ.toMonoidHom) :=
    (isMaxTwoLocal_map_iff φ M).2 hM
  have hext' : IsExtraSpec2 (pCoreOf 2 (M.map φ.toMonoidHom)) := by
    rw [pCoreOf_map_equiv]
    exact timmesfeldIsExtraspecial_of_equiv (MulEquiv.subgroupMap φ (pCoreOf 2 M)) hext
  have hcard' : Nat.card ↥(pCoreOf 2 (M.map φ.toMonoidHom)) = 2 ^ (1 + 2 * w) := by
    rw [pCoreOf_map_equiv, Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]
    exact hcard
  obtain ⟨e2⟩ := hI w hw (M.map φ.toMonoidHom) hM' hext' hcard'
  let e : ↥M ≃* ↥(Cbar w) := (MulEquiv.subgroupMap φ M).trans e2
  have hcore : Subgroup.map e.toMonoidHom (CFSG.pPrimeCore 5 ↥M) = CFSG.pPrimeCore 5 ↥(Cbar w) :=
    CFSG.pPrimeCore_map_iso 5 e
  let eq := QuotientGroup.congr (CFSG.pPrimeCore 5 ↥M) (CFSG.pPrimeCore 5 ↥(Cbar w)) e hcore
  have hC := isSimpleGroup_oPrimeRes_Cbar hw
  exact Timm.isSimpleGroup_oPrimeRes_of_mulEquiv eq hC

end CFSG.LocalAnalysis.GLTheoremA.Timm.UnitaryPoint

end
