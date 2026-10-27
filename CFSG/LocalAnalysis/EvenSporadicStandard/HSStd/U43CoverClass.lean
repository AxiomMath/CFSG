module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Cover
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43CoverData
public import CFSG.Sporadic.SmallOddCore.CentData
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check
public import CFSG.Sporadic.SmallOddCore.CentSpec
public import Certificates.Certificate27271
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Contra
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.OutU43Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Stages
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.EvenSporadicStandard.HSStd.U43

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.M24Std.CU43

@[expose] noncomputable def yA : Equiv.Perm (Fin 820) := tp 820 yATab

@[expose] noncomputable def yB : Equiv.Perm (Fin 820) := tp 820 yBTab

@[expose] noncomputable def yC : Equiv.Perm (Fin 820) := tp 820 yCTab

@[expose] noncomputable def yD : Equiv.Perm (Fin 820) := tp 820 yDTab

theorem cube_of_orderOf {β : Equiv.Perm (Fin 820)} (ho : orderOf β = 3) :
    β * β * β = 1 ∧ β ≠ 1 := by
  refine ⟨?_, ?_⟩
  · have := pow_orderOf_eq_one β
    rwa [ho, pow_three'] at this
  · intro h
    rw [h, orderOf_one] at ho
    exact absurd ho (by norm_num)

section Cover

theorem mem_conjClasses {β : Equiv.Perm (Fin 820)} (hβ : β ∈ P) (h3 : β * β * β = 1)
    (h1 : β ≠ 1) : β ∈ conjClass P yA ∨ β ∈ conjClass P yB ∨ β ∈ conjClass P yC ∨
      β ∈ conjClass P yD := by
  obtain ⟨g, hg, h | h | h | h⟩ := Certificates.certificate27271.2.2.2 β hβ h3 h1
  · exact Or.inl ⟨g, hg, h⟩
  · exact Or.inr (Or.inl ⟨g, hg, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨g, hg, h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨g, hg, h⟩))

theorem card_inf_centralizer_order_three {β : Equiv.Perm (Fin 820)} (hβ : β ∈ P)
    (ho : orderOf β = 3) :
    Nat.card ↥(P ⊓ centralizer ({β} : Set (Equiv.Perm (Fin 820)))) = 5832 ∨
      Nat.card ↥(P ⊓ centralizer ({β} : Set (Equiv.Perm (Fin 820)))) = 972 ∨
      Nat.card ↥(P ⊓ centralizer ({β} : Set (Equiv.Perm (Fin 820)))) = 81 := by
  obtain ⟨h3, h1⟩ := cube_of_orderOf ho
  obtain ⟨hAc, hBc, hCc, hDc⟩ := Certificates.certificate27271.2.2.1
  rcases mem_conjClasses hβ h3 h1 with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩ |
      ⟨g, hg, rfl⟩
  · exact Or.inl ((card_inf_centralizer_conj hg yA).trans hAc)
  · exact Or.inr (Or.inl ((card_inf_centralizer_conj hg yB).trans hBc))
  · exact Or.inr (Or.inl ((card_inf_centralizer_conj hg yC).trans hCc))
  · exact Or.inr (Or.inr ((card_inf_centralizer_conj hg yD).trans hDc))

theorem exists_conj_of_card_972 {β : Equiv.Perm (Fin 820)} (hβ : β ∈ P) (ho : orderOf β = 3)
    (hc : Nat.card ↥(P ⊓ centralizer ({β} : Set (Equiv.Perm (Fin 820)))) = 972) :
    ∃ g ∈ P, β = g * yB * g⁻¹ ∨ β = g * yC * g⁻¹ := by
  obtain ⟨h3, h1⟩ := cube_of_orderOf ho
  obtain ⟨hAc, -, -, hDc⟩ := Certificates.certificate27271.2.2.1
  rcases mem_conjClasses hβ h3 h1 with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩ |
      ⟨g, hg, rfl⟩
  · rw [card_inf_centralizer_conj hg yA] at hc
    exact absurd (hc.symm.trans hAc) (by norm_num)
  · exact ⟨g, hg, Or.inl rfl⟩
  · exact ⟨g, hg, Or.inr rfl⟩
  · rw [card_inf_centralizer_conj hg yD] at hc
    exact absurd (hc.symm.trans hDc) (by norm_num)

end Cover

end CFSG.EvenSporadicStandard.HSStd.U43
