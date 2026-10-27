module

public import CFSG.ClassicalInvolution.Q3.Q3T7S23Fin
public import CFSG.ClassicalInvolution.Q3.Q3T7ExitB3Phan

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7S23

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77


@[expose] def B3Chain23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Q3T8.Asc77.Hyp23b Ω K K' W z u e g →
      (alphaOf (Subgroup.closure {u, z}) = ⊥ ∧
        Q3T8.Asc77.ExactLayer.exactLayer Ω e ⊔ Q3T8.Asc77.ExactLayer.exactLayer Ω u = ⊤) →
      Q3T8.Asc77.LayerOrthType Ω e 6 (piSign 3 1) →
      Q3T8.Asc77.LayerOrthType Ω u 5 true → Q3T7.B3PhanChain3 Ω

@[expose] def D4Chain23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Q3T8.Asc77.Hyp23b Ω K K' W z u e g →
      (alphaOf (Subgroup.closure {u, z}) = ⊥ ∧
        Q3T8.Asc77.ExactLayer.exactLayer Ω e ⊔ Q3T8.Asc77.ExactLayer.exactLayer Ω u = ⊤) →
      Q3T8.Asc77.LayerOrthType Ω e 6 (piSign 3 1) →
      Q3T8.Asc77.LayerOrthType Ω u 6 (!piSign 3 1) → Q3T7.TD4Chain3 Ω

@[expose] def OddCoreLayer23Neg3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Q3T8.Asc77.Hyp23b Ω K K' W z u e g →
      (alphaOf (Subgroup.closure {u, z}) = ⊥ ∧
        Q3T8.Asc77.ExactLayer.exactLayer Ω e ⊔ Q3T8.Asc77.ExactLayer.exactLayer Ω u = ⊤) →
      Q3T8.Asc77.LayerOrthType Ω e 6 (piSign 3 1) →
        classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω e) = ⊥

theorem phan23Residual3_of_chains
    (hB : B3Chain23) (hD : D4Chain23) : Phan23Residual3 := by
  intro G _ _ _ Ω K K' W z u e g h hgen hE hY
  have hnab : ∃ a b : G, a * b ≠ b * a := Q3T8.Asc77.T7Y.exists_noncomm h.std.1.stand
  rcases hY with hY | hY
  · exact Or.inl (Q3T7.conclusionD_of_b3PhanChain3 hnab (hB G Ω K K' W z u e g h hgen hE hY))
  · exact Or.inl (Q3T7.conclusionD_of_td4Chain3 hnab (hD G Ω K K' W z u e g h hgen hE hY))

end CFSG.ClassicalInvolution.Q3.Q3T7S23
