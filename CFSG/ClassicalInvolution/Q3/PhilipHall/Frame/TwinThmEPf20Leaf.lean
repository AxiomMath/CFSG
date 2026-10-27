module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf18NoExit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf20E4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf20W
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf18E8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf18OddCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.Ih8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf17Ae8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf16Leaf
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUConnE

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.TC.Thin

section LeafF

theorem e189LeafQ8_of' (hE4 : E189E4ModelT) : TwinThmEW.E189LeafQ8 := by
  intro n hih Y _ _ hlt Λ hS _ K hK htrans hconn hedge z hz hodd J hJ t ht hzt hne
  obtain ⟨K', hK'tw, hK'ne⟩ := hedge
  have htransAll := trans_of_trans_at htrans
  have hzK' : ∃ w, IsUniqueInvolution K w ∧ IsUniqueInvolution K' w := hK'tw.2
  obtain ⟨w, hwK, hwK'⟩ := hzK'
  have hedge' : ∃ M ∈ Λ, ∃ N : Subgroup Y, N ∈ omegaNbr Λ M :=
    ⟨K, hK, K', Q3CL.T3.twin_mem_omegaNbr hS.hyp hK hK'tw.1 hK'ne hwK hwK'⟩
  have hoddAll : ∀ M ∈ Λ, ∀ u : Y, IsUniqueInvolution M u →
      oddCoreImg (Subgroup.centralizer ({u} : Set Y)) = ⊥ := fun M hM u hu =>
    TwinDisc.oddCentEdge_proved n hih.1 hih.2 Y hlt Λ hS htransAll hedge' M hM u hu
  by_cases hO2 : ∃ M ∈ Λ, ∃ u : Y, IsUniqueInvolution M u ∧ TightInO2 u
  ·
    obtain ⟨M, hM, u, hu, hOu⟩ := hO2
    have F := TwinDisc.ExitU.q8Fam_of_q8Section hS htransAll hM hu (hoddAll M hM u hu) hOu
    rcases F.thmDConcl hih.2.thmD.d2 hlt with h1 | ⟨W', hW'⟩ | ⟨E, hE⟩ | I64 | ⟨m, hm5, ⟨I⟩⟩ | I29
    · exact absurd (h1 K' hK'tw.1 K hK) hK'ne
    · exact absurd (wOutcome_normalizes F hW' hK hJ ht) hne
    · exact Or.inr (e189_e8_alt2 F hE hK hJ hz ht hzt hne)
    · obtain ⟨I⟩ := I64
      exact e189ConclF_of_e64 F I hK hJ hz ht hzt hne
    · rcases Nat.lt_or_ge m 6 with h6 | h6
      · obtain rfl : m = 5 := by omega
        exact (ae5_not_dstarConnected F I hK hconn ⟨K', hK'tw, hK'ne⟩).elim
      · exact Or.inr (e189_aeM_alt2_all F h6 I hK hJ hz ht hzt hne)
    · obtain ⟨I⟩ := I29
      exact e189ConclF_of_e29 F I hK hJ hz ht hzt hne
  · push Not at hO2
    rcases TwinDisc.ExitU.noExit_or_o2_or_e4 hS htransAll hedge' hoddAll with hNo | ⟨M, hM, u, hu, hOu⟩ | hE4'
    · exact e189ConclF_noExit
        (Q3T8.Asc77.e189Sect_of_model Q3T8.Asc77.e189Model3_proved) hih.1
        (InductionBridge.ih8T_of_cit3Below hih.1) hih.2 hlt hS hNo hK hJ hz ht hzt hne
    · exact absurd hOu (hO2 M hM u hu)
    · have hmem := TwinDisc.ExitU.members hS htransAll hK hz (hoddAll K hK z hz)
      exact Or.inr (e189_twinE4_alt2' hE4 hS.hyp (fun J₀ hJ₀ => (hmem J₀ hJ₀).1)
        (fun J₀ hJ₀ => (hmem J₀ hJ₀).2) hS.gen htransAll hO2 hE4' hK hz hJ ht hzt hne)

end LeafF

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
