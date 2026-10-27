module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PkBasic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PkOmega
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeZ2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Lift

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem exists_isI4PlusIn_of_quotient {A : Type} [Group A] [Finite A]
    (h : ∃ q : A ⧸ oddCore A, IsI4PlusIn (⊤ : Subgroup (A ⧸ oddCore A)) q) :
    ∃ a : A, IsI4PlusIn (⊤ : Subgroup A) a := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨a, ha, rfl⟩ := exists_involution_lift_oddCore hq.1
  exact ⟨a, isI4PlusIn_top_of_quotient ha hq⟩

theorem exists_quotient_isI4PlusIn_of_isFGroup (hS : Asc82SchurU43) {L : Type} [Group L]
    [Finite L] (hL : IsFGroup L) :
    ∃ q : L ⧸ oddCore L, IsI4PlusIn (⊤ : Subgroup (L ⧸ oddCore L)) q := by
  obtain ⟨hq, h | h⟩ := hL
  · rcases h with h | h | h | h | h | h
    · exact exists_isI4PlusIn_of_isOmegaStar (isOmegaStar_of_lieModel_psp h) (by norm_num)
    · exact exists_isI4PlusIn_of_isOmegaStar (isOmegaStar_of_lieModel_psl h) (by norm_num)
    · exact exists_isI4PlusIn_of_isOmegaStar (isOmegaStar_of_lieModel_psu h) (by norm_num)
    · exact exists_isI4PlusIn_of_isOmegaStar (isOmegaStar_of_lieModel_odd h) (by norm_num)
    · exact exists_isI4PlusIn_of_isOmegaStar (isOmegaStar_of_lieModel_plus h) (by norm_num)
    · exact exists_isI4PlusIn_of_isOmegaStar (isOmegaStar_of_lieModel_minus h) (by norm_num)
  · exact exists_isI4PlusIn_of_isOmegaCover (isOmegaCover_oddCore_quotient hS hq h) (by norm_num)

theorem exists_isI4PlusIn_of_isFGroup (hS : Asc82SchurU43) {L : Type} [Group L] [Finite L]
    (hL : IsFGroup L) : ∃ a : L, IsI4PlusIn (⊤ : Subgroup L) a :=
  exists_isI4PlusIn_of_quotient (exists_quotient_isI4PlusIn_of_isFGroup hS hL)

end CFSG.OddStandard.SmallF3.Omega
