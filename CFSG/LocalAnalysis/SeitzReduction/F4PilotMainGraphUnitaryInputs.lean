module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryModel
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphPiecesLift

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)

local instance f4PilotMainGraphUnitaryInputsNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Model

variable {G : Type} [Group G] {M : Type} [Group M]

theorem pieceCards_eq_of_model {E T₁₂ T₁ T₂ : Subgroup G} {Φ : M →* G} (hE : Φ.range = E)
    {S₁₂ S₁ S₂ : Subgroup M}
    (h₁₂ : T₁₂ ⊔ centralizer (E : Set G) = S₁₂.map Φ ⊔ centralizer (E : Set G))
    (h₁ : T₁ ⊔ centralizer (E : Set G) = S₁.map Φ ⊔ centralizer (E : Set G))
    (h₂ : T₂ ⊔ centralizer (E : Set G) = S₂.map Φ ⊔ centralizer (E : Set G)) :
    pieceCards E T₁₂ T₁ T₂ = pieceCards Φ.range (S₁₂.map Φ) (S₁.map Φ) (S₂.map Φ) := by
  subst hE
  simp only [pieceCards, inf_centralizer_eq_of_sup_eq h₁₂, inf_centralizer_eq_of_sup_eq h₁,
    inf_centralizer_eq_of_sup_eq h₂]

end Model

section Inputs


@[expose] def UnitaryGraphTorusExactInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f →
    ∀ N : AmalgamNeighbour, N ≠ .X' →
      (HR8Kind e t f N .unitary6 → ∃ (F : Type) (_ : Field F) (h : UnitaryFieldData 2 f F)
        (Φ : uGroup6 h →* G), Φ.range = neighbourCore e N ∧ Φ.ker ≤ center (uGroup6 h) ∧
          ((sp6TorusA (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed6 h)).map Φ =
            leviTorusG e {1, 2} ⊓ neighbourLeviG e N ∧
          ((sp6TorusM2 (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed6 h)).map Φ =
            leviTorusG e (rankOneTori N).1 ⊓ neighbourLeviG e N ∧
          ((sp6TorusM3 (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed6 h)).map Φ =
            leviTorusG e (rankOneTori N).2 ⊓ neighbourLeviG e N) ∧
      (HR8Kind e t f N .unitary7 → ∃ (F : Type) (_ : Field F) (h : UnitaryFieldData 2 f F)
        (Φ : uGroup7 h →* G), Φ.range = neighbourCore e N ∧ Φ.ker ≤ center (uGroup7 h) ∧
          ((sp6TorusA (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed7 h)).map Φ =
            leviTorusG e {1, 2} ⊓ neighbourLeviG e N ∧
          ((sp6TorusM2 (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed7 h)).map Φ =
            leviTorusG e (rankOneTori N).1 ⊓ neighbourLeviG e N ∧
          ((sp6TorusM3 (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed7 h)).map Φ =
            leviTorusG e (rankOneTori N).2 ⊓ neighbourLeviG e N)

end Inputs

@[expose] def UnitaryModelPiecesInput : Prop :=
  ∀ (f : ℕ) (F : Type) [Field F] (h : UnitaryFieldData 2 f F), 2 ≤ f →
    ∀ (G : Type) [Group G] [Finite G],
      (∀ Φ : uGroup6 h →* G, Φ.ker ≤ center (uGroup6 h) →
        pieceCards Φ.range (((sp6TorusA (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed6 h)).map Φ)
          (((sp6TorusM2 (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed6 h)).map Φ)
          (((sp6TorusM3 (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed6 h)).map Φ) =
            pieceOrders .unitary6 (2 ^ f)) ∧
      (∀ Φ : uGroup7 h →* G, Φ.ker ≤ center (uGroup7 h) →
        pieceCards Φ.range (((sp6TorusA (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed7 h)).map Φ)
          (((sp6TorusM2 (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed7 h)).map Φ)
          (((sp6TorusM3 (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed7 h)).map Φ) =
            pieceOrders .unitary7 (2 ^ f))

section Omega


@[expose] def OmegaPieceTablesInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f →
    ∀ N : AmalgamNeighbour, N ≠ .X' → ∀ κ : Sp6Kind, (κ = .omegaPlus8 ∨ κ = .omegaMinus8) →
      HR8Kind e t f N κ → neighbourPieceCards e N = pieceOrders κ (2 ^ f)

end Omega

section Reduction


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem neighbourPieceCards_eq_of_exact (e : L ≃* adjointGroup .F4 K) {N : AmalgamNeighbour}
    (hN : N ≠ .X') {M : Type} [Group M] {Φ : M →* G} (hE : Φ.range = neighbourCore e N)
    {S₁₂ S₁ S₂ : Subgroup M}
    (hA : S₁₂.map Φ = leviTorusG e {1, 2} ⊓ neighbourLeviG e N)
    (h₂ : S₁.map Φ = leviTorusG e (rankOneTori N).1 ⊓ neighbourLeviG e N)
    (h₃ : S₂.map Φ = leviTorusG e (rankOneTori N).2 ⊓ neighbourLeviG e N) :
    neighbourPieceCards e N = pieceCards Φ.range (S₁₂.map Φ) (S₁.map Φ) (S₂.map Φ) := by
  have h12 : ({1, 2} : Finset (Fin (Tag.rank .F4))) ⊆ N.nodes := by
    cases N
    · decide
    · decide
    · exact absurd rfl hN
  rw [neighbourPieceCards_eq_pieceCards]
  refine pieceCards_eq_of_model hE ?_ ?_ ?_
  · rw [leviTorusG_sup_centralizer_eq e h12, hA]
  · rw [leviTorusG_sup_centralizer_eq e (rankOneTori_subset_nodes hN).1, h₂]
  · rw [leviTorusG_sup_centralizer_eq e (rankOneTori_subset_nodes hN).2, h₃]

omit [Finite K] [CharP K 2] in
theorem unitaryOmegaPieceTablesInput_of_inputs (hT : UnitaryGraphTorusExactInput)
    (hP : UnitaryModelPiecesInput) (hO : OmegaPieceTablesInput) :
    UnitaryOmegaPieceTablesInput := by
  intro G _ _ L K _ _ _ e t f hw hf N hN κ hκ h
  rcases hκ with rfl | rfl | hκ
  · obtain ⟨F, _, hF, Φ, hE, hker, hA, h₂, h₃⟩ := (hT G L K e t f hw hf N hN).1 h
    rw [neighbourPieceCards_eq_of_exact e hN hE hA h₂ h₃]
    exact (hP f F hF hf G).1 Φ hker
  · obtain ⟨F, _, hF, Φ, hE, hker, hA, h₂, h₃⟩ := (hT G L K e t f hw hf N hN).2 h
    rw [neighbourPieceCards_eq_of_exact e hN hE hA h₂ h₃]
    exact (hP f F hF hf G).2 Φ hker
  · exact hO G L K e t f hw hf N hN κ hκ h

end Reduction

end CFSG.SeitzReduction.F4Pilot
