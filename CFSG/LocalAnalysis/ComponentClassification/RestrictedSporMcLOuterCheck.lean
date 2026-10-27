module

public import CFSG.Sporadic.SmallOddCore.McLLocalCheck
public meta import CFSG.Sporadic.SmallOddCore.McLLocalCheck
public meta import CFSG.Sporadic.SmallOddCore.McLData
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcLOuterCheckInputs
public import Certificates.Certificate2025

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG.PSL3Four.Native CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native

theorem mclY_basic :
    mclFix1.length = 11 ∧ mclYGens.size = 4 ∧ invsOK 11 mclYGens mclYInvs = true ∧
      mclYOrbits.size = 10 ∧ permOK 275 (mclCentTbl 17) = true ∧
      ∀ k < 4, permOK 275 (mclCentTbl (k + 18)) = true :=
  Certificates.certificate2025.1

theorem mclY_enum : enumOK 11 mclYGens mclYEnum = true ∧ mclYEnum.tabs.size = 7920 :=
  Certificates.certificate2025.2.1

theorem mclY_orbits :
    (∀ l < 10, orbitOK 11 mclYGens mclYInvs (wordTabS 11 mclYGens (mclYWords.getD l []))
        mclYOrbits[l]! = true ∧ mclYOrbits[l]!.tabs.size = mclYSizes.getD l 0) ∧
      (∀ l < 10, ∀ l' < 10, l ≠ l' →
        notInOK mclYOrbits[l]!.tabs (wordTabS 11 mclYGens (mclYWords.getD l' [])) = true) ∧
      (∀ l < 10, ∀ j ∈ mclYWords.getD l [], j < mclYGens.size) ∧
      wordTabS 11 mclYGens (mclYWords.getD 0 []) = idTab 11 :=
  Certificates.certificate2025.2.2.1

theorem mclY_cover : coverAllOK mclYEnum.tabs mclYOrbits = true :=
  Certificates.certificate2025.2.2.2.1

theorem mclY_sums : ∀ U : Finset (Fin 10), 0 ∈ U → (∑ l ∈ U, mclYSizes.getD l 0) ∣ 7920 →
    U = {0} ∨ U = Finset.univ :=
  Certificates.certificate2025.2.2.2.2

end CFSG.ComponentClassification.RestrictedStd.Spor
