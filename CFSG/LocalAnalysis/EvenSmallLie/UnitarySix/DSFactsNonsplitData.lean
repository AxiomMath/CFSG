module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.CoverActionData
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeData
public meta import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.CoverActionData
public meta import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeData
public meta import CFSG.LieType.Multipliers.U62Bridge
public meta import CFSG.LieType.Multipliers.U62Kernel
public meta import Certificates.Data.CFSGNative.F4.T46Simple
public meta import Certificates.Data.CFSGNative.Fi22.Local
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.DSFactsNonsplitDataInputs
public import Certificates.Certificate3180
public import Certificates.Certificate3144

public section

namespace CFSG.EvenSmallLie.UnitarySix

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U62 CFSG.CosetTable CFSG.F4.Native
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Fischer CFSG.Sporadic.Fi22.Native

theorem ns_t46_check :
    u62W (expand nsE) ∈ Subgroup.closure {g | g ∈ aGens} ∧
      (∀ k ∈ [u62W (expand nsN₁), u62W (expand nsN₂)], ∀ a ∈ aGens,
        k * a * k⁻¹ ∈ Subgroup.closure {g | g ∈ aGens}) ∧
      t46FixAll (wordT 693 t46Gen (expand nsC₁)) = true ∧
      t46FixAll (wordT 693 t46Gen (expand nsC₂)) = true :=
  Certificates.certificate3144.1

theorem ns_cover_check :
    ∃ (E : Type) (_ : Group E) (ψ : PG 5 coverWs →* E),
      ∀ u ∈ exclWords nsC₁ (0, 1, 0) ++ exclWords nsC₂ (0, 0, 1),
        ψ (PresentedGroup.mk _ (FreeGroup.mk u)) ≠ 1 :=
  Certificates.certificate3144.2

end CFSG.EvenSmallLie.UnitarySix
