module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.BT2Basic
public import CFSG.Sporadic.Schreier.TitsComponent
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup CFSG CFSG.Blueprint CFSG.Sporadic.Schreier.Tits

theorem isCharacteristicP_two_of_hasTwoCore {G : Type*} [Group G] (h : HasTwoCore G) :
    IsCharacteristicP 2 G := by
  obtain ⟨J, hJ, hJ2, hJC⟩ := h
  haveI := hJ
  exact isCharacteristicP_two_of_two_radical J hJ2 fun x hx => by
    obtain ⟨k, hk⟩ := hJ2 ⟨x, hJC hx⟩
    exact ⟨k, congrArg Subtype.val hk⟩


theorem involutionCentralizersCharTwo_titsD : InvolutionCentralizersCharTwo titsD := by
  intro x hx
  have hz : HasTwoCore (Subgroup.centralizer {titsZD}) :=
    hasTwoCore_centralizer_of_map_eq titsD_centralizer_z hasTwoCore_titsH
  have ht : HasTwoCore (Subgroup.centralizer {titsTD}) :=
    hasTwoCore_centralizer_of_map_eq titsD_centralizer_t.1.symm hasTwoCore_titsCt
  rcases titsD_involution_conj x hx with h | h
  · exact isCharacteristicP_two_of_hasTwoCore (hasTwoCore_centralizer_of_conj h hz)
  · exact isCharacteristicP_two_of_hasTwoCore (hasTwoCore_centralizer_of_conj h ht)

theorem involutionCentralizersCharTwo_tits {S : Type} [Group S] {f : ℕ}
    (h : ReeTitsModel S .Tits 2 f) : InvolutionCentralizersCharTwo S := by
  obtain ⟨e⟩ := titsModelEquiv _ 2 f h
  exact InvolutionCentralizersCharTwo.of_mulEquiv e involutionCentralizersCharTwo_titsD

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
