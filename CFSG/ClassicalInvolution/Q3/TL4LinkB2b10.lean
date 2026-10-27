module

public import CFSG.ClassicalInvolution.Q3.TL4LinkB2b0
public import CFSG.ClassicalInvolution.Q3.TL4LinkB2b9
public import CFSG.LocalAnalysis.ComponentClassification.QuaternionComponentWired27
public import CFSG.Goldschmidt.Final
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFD4OG
public import CFSG.ClassicalInvolution.Q3.TL4LinkDiscC
public import CFSG.Holt.Centralizer
public import CFSG.Holt.MaximalFixer

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj)

theorem tightLinkEdgeRigidR_plus
    (n : ℕ) : TL4.PlusLeaf TL4.LinkDisc.TightLinkEdgeRigidR n := by
  intro hA hPlus Y _ _ R S t hL hc _ hα hall _ J hJ M hM hMJ u hu _ hB2
  by_cases hrig : RigidEdge (tightCore R) J t u
  · exact false_of_B2b' CFSG.Goldschmidt.topStatement quatAutFacts_three hL hall hJ
      hM hMJ hu hB2 hrig
  · unfold RigidEdge at hrig
    push Not at hrig
    obtain ⟨P, T, hP, hT, hPT, e, he, he2, heE⟩ := hrig
    exact false_of_edge_of_frame_of_sylow
      (CFSG.ComponentClassification.QuaternionComponent.thm4RBelow₂₇ n hA hPlus) hPlus.thm5
      (hPlus.twin rfl) TL4.e4AutOddFreeR_proved TL4.omegaAutOddFreeR_proved hL hc hα hall hJ hM
      hMJ hB2 hu hP hT hPT (Subgroup.mem_inf.mp he).1 (Subgroup.mem_inf.mp he).2 he2 heE

end CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b
