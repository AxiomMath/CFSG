module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenSL3MaxParHyp
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenSL3DLeI
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenSL3BorelCase

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open Matrix
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (ThreeTenTorusExclusion)

variable {H : Type} [Group H] [Finite H]

theorem isMaxParabolicP_of_threeTenHyp_of_isSLType_of_torusExclusion
    {I D P Y : Subgroup H} {p d : ℕ} (hhyp : ThreeTenHyp I D P Y p d)
    (e : ↥I ≃* SpecialLinearGroup (Fin 3) (ZMod p))
    (htor : ThreeTenTorusExclusion p d) :
    CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p I Y := by
  have hDI : D ≤ I := d_le_I_of_threeTenHyp_of_isSLType hhyp e htor
  have hbase : ThreeTenHyp I D P Y p d := hhyp
  obtain ⟨-, -, -, -, -, -, -, -, -, hYlt, -, -⟩ := hbase
  have hYI : Y ≤ I := Y_le_left_of_le hDI hYlt
  have hne : Y ≠ I := Y_ne_left_of_le hDI hYlt
  have hNne : Y ≠ Subgroup.normalizer (P : Set H) ⊓ I := by
    intro hYB
    have hB : Subgroup.normalizer (P : Set H) ⊓ I = Y ⊓ I := by
      rw [hYB]
      exact (inf_eq_left.mpr (inf_le_right : Subgroup.normalizer (P : Set H) ⊓ I ≤ I)).symm
    exact borel_case_impossible hhyp e htor hB rfl
  exact isMaxParabolicP_of_threeTenHyp_of_isSLType hhyp e hYI hne hNne

end CFSG.LocalAnalysis.AGL81I.Section3
