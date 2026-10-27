module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5G8Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5G8B3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5G8BarSyl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5G8BarGen

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open CFSG.ClassicalInvolution.Disconnected.AschTight

theorem sec5g8_outcome (hB3 : GoldschmidtB3Tmp) (hSH8 : Sec5SH8Statement) {X : Type} [Group X]
    [Finite X] (P : Sylow 2 X) {Tb : Subgroup X} (hle : Tb ≤ (P : Subgroup X))
    (hD : Nonempty (↥Tb ≃* DihedralGroup 4))
    (hSC : fusionStronglyClosed (Tb : Set X) (P : Subgroup X)) : Sec5G8Outcome Tb := by
  obtain ⟨Pm, hPm⟩ := sec5g8_exists_sylow hB3 P hle hD hSC
  obtain ⟨Pb, hPb⟩ := sec5g8_exists_sylow_bar ⟨Pm, hPm⟩
  have hDb : Nonempty (↥Pb ≃* DihedralGroup 4) := by
    obtain ⟨e⟩ := sec5g8_dihedral_bar hD
    exact ⟨(MulEquiv.subgroupCongr hPb).trans e⟩
  have hO : CFSG.oddCore (Sec5GBar Tb) = ⊥ := sec5g8_oddCore_bar Tb
  have hgen : normalClosure ((Pb : Subgroup (Sec5GBar Tb)) : Set (Sec5GBar Tb)) = ⊤ := by
    rw [hPb]
    exact sec5g8_normalClosure_bar P hle hSC
  exact ⟨Pb, hPb, hDb, hO, hgen, hSH8 (Sec5GBar Tb) hO Pb hDb hgen⟩

end CFSG.OddStandard.SmallF3.Omega
