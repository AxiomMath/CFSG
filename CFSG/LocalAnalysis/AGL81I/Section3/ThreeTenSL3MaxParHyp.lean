module

public import CFSG.LocalAnalysis.AGL81I.Section3.SL3BorelOvergroups
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenBasics

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open Matrix
open CFSG.GH74.GLS.Stage2.Signalizer (IsMaxParabolicP)

variable {H : Type} [Group H] [Finite H]

theorem isMaxParabolicP_of_threeTenHyp_of_isSLType {I D P Y : Subgroup H} {p d : ℕ}
    (hhyp : ThreeTenHyp I D P Y p d)
    (e : ↥I ≃* SpecialLinearGroup (Fin 3) (ZMod p))
    (hYI : Y ≤ I) (hne : Y ≠ I)
    (hNne : Y ≠ Subgroup.normalizer (P : Set H) ⊓ I) :
    IsMaxParabolicP p I Y := by
  obtain ⟨hp, -, -, -, -, hI, -, -, hP, -, -, hN⟩ := hhyp
  haveI : Fact p.Prime := ⟨hp⟩
  have hPI : P ≤ I := by
    rw [hI]
    exact p_sylow_le_oPPrimeHull hp hP
  exact isMaxParabolicP_of_isSLType_sylowNormalizer_le e hYI hne
    (hP.of_le hPI le_top) hN hNne

end CFSG.LocalAnalysis.AGL81I.Section3
