module

public import CFSG.LieType.Multipliers.U43
public import Certificates.Certificate22243
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Transport
public import CFSG.Sporadic.SmallOddCore.Assembly

public section

namespace CFSG.ComponentClassification.HarrisLit.P1.U43

open CFSG.LieType.Multipliers.U43 Matrix Subgroup CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Th.Native

theorem p1ModelFacts_u43 : P1ModelFacts X₀ :=
  Certificates.certificate22243

theorem p1ModelFacts_of_lieModel_psu {S : Type} [Group S]
    (h : Blueprint.LieModel S .PSU 4 3 1) : P1ModelFacts S := by
  obtain ⟨e⟩ := CFSG.LieType.Multipliers.U43.nonempty_mulEquiv_X₀ h
  exact P1ModelFacts.of_mulEquiv e p1ModelFacts_u43

end CFSG.ComponentClassification.HarrisLit.P1.U43
