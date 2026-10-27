
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.NotZ2A6Base

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Final4Base
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WFactsJ2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WJ3

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Schreier (j2P j2PermEquiv j3P j3PermEquiv)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {z t : G} {T₀ : Subgroup G}

namespace J2

theorem betaData_of_isSporadic {L : Subgroup G}
    (h : InnerConfig G L z t T₀) (hL : IsSporadic L .J2) {β : G} (hβL : β ∈ L)
    (hβt : β * t = t * β) (hβ3 : orderOf β = 3) :
    Nonempty (↥(L ⊓ centralizer ({β} : Set G)) ⧸
      fusionOddCore ↥(L ⊓ centralizer ({β} : Set G)) ≃* alternatingGroup (Fin 6)) ∧
      fusionOddCoreOf (L ⊓ centralizer ({β} : Set G)) ≤ zpowers β := by
  obtain ⟨e⟩ := hL
  have hB : BetaDataSqB ↥ComponentClassification.J2Cover.Models.P :=
    BetaDataSqB.of_mulEquiv
      ((j2PermEquiv.symm.trans ComponentClassification.J2Cover.nativeEquivP).trans
        (MulEquiv.subgroupCongr ComponentClassification.J2Cover.Models.P_eq_autP.symm))
      betaDataSqB_j2P
  exact betaData_of_model h
    (((MulEquiv.subgroupCongr ComponentClassification.J2Cover.Models.P_eq_autP).trans
      ComponentClassification.J2Cover.nativeEquivP.symm).trans e.symm) hB.betaDataSq
    rootFactsClass_P hβL hβt hβ3

end J2

namespace J3

theorem betaData_of_isSporadic {L : Subgroup G}
    (h : InnerConfig G L z t T₀) (hL : IsSporadic L .J3) {β : G} (hβL : β ∈ L)
    (hβt : β * t = t * β) (hβ3 : orderOf β = 3) :
    Nonempty (↥(L ⊓ centralizer ({β} : Set G)) ⧸
      fusionOddCore ↥(L ⊓ centralizer ({β} : Set G)) ≃* alternatingGroup (Fin 6)) ∧
      fusionOddCoreOf (L ⊓ centralizer ({β} : Set G)) ≤ zpowers β := by
  obtain ⟨e⟩ := hL
  exact betaData_of_model h (j3PermEquiv.symm.trans e.symm) betaDataSqB_j3P.betaDataSq
    rootFactsClass_j3P hβL hβt hβ3

end J3

theorem fin76bNotZ2A6 :
    Fin76bNotZ2A6 := by
  intro G _ _ L z t T₀ E Q x β B hconf hW y hyN hyβ hyz hyt
  have hβL : β ∈ L := hconf.B_le hconf.beta_mem
  have hβt : β * t = t * β := mem_centralizer_singleton_iff.1 (hconf.B_cent hconf.beta_mem)
  obtain ⟨hD, hO⟩ : Nonempty (↥(L ⊓ centralizer ({β} : Set G)) ⧸
      fusionOddCore ↥(L ⊓ centralizer ({β} : Set G)) ≃* alternatingGroup (Fin 6)) ∧
      fusionOddCoreOf (L ⊓ centralizer ({β} : Set G)) ≤ zpowers β := by
    rcases hconf.sporadic with hL | hL
    · exact J2.betaData_of_isSporadic hconf.cfg hL hβL hβt hconf.beta_order
    · exact J3.betaData_of_isSporadic hconf.cfg hL hβL hβt hconf.beta_order
  exact not_z2a6_of_betaData hconf.cfg hD hO hβL hβt hyβ hyz

end CFSG.EvenSporadicStandard.Fin76b
