module

public import CFSG.ClassicalInvolution.Q3.Q3T7S23A04
public import CFSG.ClassicalInvolution.Q3.Q3T7P25Bridge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7S23

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77


@[expose] def Phan23Residual3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Q3T8.Asc77.Hyp23b Ω K K' W z u e g →
      (alphaOf (Subgroup.closure {u, z}) = ⊥ ∧
        Q3T8.Asc77.ExactLayer.exactLayer Ω e ⊔ Q3T8.Asc77.ExactLayer.exactLayer Ω u = ⊤) →
      Q3T8.Asc77.LayerOrthType Ω e 6 (piSign 3 1) →
      (Q3T8.Asc77.LayerOrthType Ω u 5 true ∨ Q3T8.Asc77.LayerOrthType Ω u 6 (!piSign 3 1)) →
        ConcOrTF4 G

theorem c23_10_of_phan (h9 : Q3T8.Asc77.C23_9X) (hres : Phan23Residual3) :
    Q3T8.Asc77.C23_10 := by
  intro G _ _ _ Ω K K' W z u e g h
  obtain ⟨hgen, hE, hY⟩ := h9 G Ω K K' W z u e g h
  exact hres G Ω K K' W z u e g h hgen hE hY

theorem c23_3_of_inputs3 (hE : Q3T7E.ThmEWithSylow3) (h7 : Q3T8.Asc77.C23_7)
    (hres : Phan23Residual3) : Q3T8.Asc77.C23_3 := by
  have : Fact Q3T7E.ThmEWithSylow3 := ⟨hE⟩
  exact Q3T8.Asc77.c23_3_of_steps (Q3T8.Asc77.c23_setup_of Q3T8.Asc77.c23_setupSetting_proved)
    (c23_10_of_phan (Q3T8.Asc77.c23_9_ofK
      (Q3T8.Asc77.c23_2_of_trans hE Q3T8.Asc77.c23_2_trans_proved) Q3T8.Asc77.c23_4X_proved
      Q3T8.Asc77.c23_5X_type_proved h7 Q3T8.Asc77.c23_GammaU_proved
      Q3T8.Asc77.c23_9_noZX_proved Q3T8.Asc77.c23_9_genX_proved) hres)

theorem c23_3Three_of_inputs (hE : Q3T7E.ThmEWithSylow3) (h7 : Q3T8.Asc77.C23_7)
    (hres : Phan23Residual3) : Q3T7.C23_3Three := by
  intro G _ _ _ Ω K K' z hs W hW hzW hS4
  have key := c23_3_of_inputs3 hE h7 hres G Ω K K' z (Q3T7P25.hyp23_of_three hs) W hW hzW hS4
  rw [CFSG.centerIn_eq_map_center]
  exact key

end CFSG.ClassicalInvolution.Q3.Q3T7S23
