module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeZ2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeHigh
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLow
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6ZCover
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6ZFix
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6ZOdd
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82ZExists_of (h36 : Asc82Lemma36) (hS : Asc82SchurU43) : Asc82ZExists := by
  intro G _ _ t L hset S hSyl
  have hqs : IsQuasisimple ↥L := hset.component.isQuasisimple
  have hodd : Odd {z : G | z ∈ L ∧ IsI4PlusIn L z}.ncard := by
    rw [m6z_ncard_pocketed_eq hqs]
    rcases hset.inF.2 with h | h
    · rcases h with h | h | h | h | h | h
      · exact m6z_odd_pocketed_omegaStar (isOmegaStar_of_lieModel_psp h)
          (Or.inl ⟨rfl, rfl⟩)
      · exact m6z_odd_pocketed_omegaStar (isOmegaStar_of_lieModel_psl h)
          (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · exact m6z_odd_pocketed_omegaStar (isOmegaStar_of_lieModel_psu h)
          (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      · exact m6z_odd_pocketed_omegaStar (isOmegaStar_of_lieModel_odd h)
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
      · exact m6z_odd_pocketed_omegaStar (isOmegaStar_of_lieModel_plus h)
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
      · exact m6z_odd_pocketed_omegaStar (isOmegaStar_of_lieModel_minus h)
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
    · exact m6z_odd_pocketed_omegaCover (isOmegaCover_oddCore_quotient hS hqs h)
  exact m6z_notation_of_odd hset.component.le hSyl
    (fun s hs => sec4_mem_normalizer h36 hset s (hSyl.1 hs)) hodd

end CFSG.OddStandard.SmallF3.Omega
