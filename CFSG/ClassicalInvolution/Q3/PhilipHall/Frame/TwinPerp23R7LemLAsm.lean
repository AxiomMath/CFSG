module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLTri

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.TC.Thin

section Asm

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)}

theorem Q8Pre.toFam_of_tightInO2 (F : Q8Pre G Φ) {K : Subgroup G} (hK : K ∈ Φ) {t : G}
    (ht : IsUniqueInvolution K t) (hO2 : TightInO2 t) : TwinDisc.ExitO2.Q8Fam G Φ := by
  refine F.toFam fun L hL u hu => ?_
  obtain ⟨g, rfl⟩ := F.trans K hK L hL
  obtain ⟨P, hPn, hP2, hzP⟩ := hO2
  refine ⟨P, hPn, hP2, ?_⟩
  have hgu : g * t * g⁻¹ = u := (ht.conj g).eq hu
  rw [← hgu]
  exact hPn.conj_mem t hzP g

end Asm

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
