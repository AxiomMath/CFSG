module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2G2Def
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2G1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OddCoreQ8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OddCoreL3U3
public import CFSG.Sporadic.FischerOddCore.CentralExt

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint

theorem oddCore_centralizer_quaternion_of_isTwoU43 {Y : Type} [Group Y] [Finite Y]
    (hY : IsTwoU43 Y) (f : QuaternionGroup 2 →* Y) :
    oddCore ↥(Subgroup.centralizer ({f (QuaternionGroup.a 2)} : Set Y)) = ⊥ := by
  obtain ⟨hcard, hU⟩ := hY
  refine CFSG.Sporadic.FischerOddCore.oddCore_centralizer_eq_bot_of_central
    (QuotientGroup.mk' (Subgroup.center Y)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _).le ?_ (f (QuaternionGroup.a 2)) ?_
  · rw [QuotientGroup.ker_mk']
    exact dvd_of_eq hcard
  · exact oddCore_centralizer_quaternion_of_isOmegaStar (isOmegaStar_of_lieModel_psu hU)
      ((QuotientGroup.mk' (Subgroup.center Y)).comp f)

theorem asc82OddCoreCentralizerQ8_holds : Asc82OddCoreCentralizerQ8 := by
  intro Y _ _ hY f hf
  have hord : orderOf (f (QuaternionGroup.a 2)) = 2 :=
    (orderOf_injective f hf _).trans orderOf_quaternion_a_two_eq_two
  rcases hY with h | h | h | h | h
  · exact oddCore_centralizer_quaternion_of_smallF3OmegaQuotient h f
  · exact oddCore_centralizer_quaternion_of_isTwoU43 h f
  · exact (asc82NoQ8InL2_holds Y (Or.inl h) f hf).elim
  · exact oddCore_centralizer_of_lieModel_psl33 h hord
  · exact oddCore_centralizer_of_lieModel_psu33 h hord

end CFSG.OddStandard.SmallF3.Omega
