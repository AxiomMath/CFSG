module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aSelfDual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.TopDefs

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped MatrixGroups Matrix

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.X7
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def ActualLinearThreeSelfDualSections : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H T M E : Subgroup (MulAut V)), FFHyp V H T M E →
    ¬ Group.IsSolvable H → ∀ L : Subgroup (MulAut V), IsComp L H → ∀ f : ℕ, 2 ≤ f →
      StatedClassicalModel (CQ L) .PSL 3 2 f →
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (φ : SL(3, F) →* ↥L)
        (U : Type) (_ : AddCommGroup U) (_ : Module (ZMod 2) U) (_ : Finite U)
        (ρL : Representation (ZMod 2) ↥L U) (A : Subgroup (U ≃ₗ[ZMod 2] U)),
        Nat.card F = 2 ^ f ∧ Odd (Nat.card (Subgroup.center ↥L)) ∧ Function.Surjective φ ∧
        (∀ x : SL(3, F), φ x = 1 → x ∈ scalars 3 F) ∧
        (scalars 3 F).map φ = Subgroup.center ↥L ∧
        (∀ x : SL(3, F), ρL (φ x) = 1 → x ∈ scalars 3 F) ∧
        Representation.IsIrreducible (ρL.comp φ) ∧
        Nonempty (Representation.Equiv (ρL.comp φ) (Representation.dual (ρL.comp φ))) ∧
        CFSG.IsElementaryAbelian 2 A ∧ A ≠ ⊥ ∧
        (∀ a ∈ A, ∀ x : SL(3, F), ∃ y : SL(3, F), Intertwines (ρL.comp φ) a x y) ∧
        Nat.card U ≤ Nat.card A * Nat.card {u : U // ∀ a ∈ A, a u = u}

theorem original_minimal_parabolic_FF_actor_excludes_PSL3_components
    (h6 : SelfDualInvolutionRank) (h9 : ActualLinearThreeSelfDualSections) {V : Type}
    [CommGroup V] [Finite V] {H T M E : Subgroup (MulAut V)} (hF : FFHyp V H T M E)
    (hns : ¬ Group.IsSolvable H) {L : Subgroup (MulAut V)} (hL : IsComp L H) {f : ℕ}
    (hf : 2 ≤ f) : ¬ StatedClassicalModel (CQ L) .PSL 3 2 f := by
  intro hmodel
  obtain ⟨F, _, hFfin, φ, U, _, _, hUfin, ρL, A, hcard, -, -, -, -, hker, hirr, hsd, hAe, hA1, hA,
    hoff⟩ := h9 V H T M E hF hns L hL f hf hmodel
  have : Fintype F := Fintype.ofFinite F
  have hF2 : Fintype.card F = 2 ^ f := by rw [Fintype.card_eq_nat_card]; exact hcard
  have := hAe
  have := self_dual_full_normalizer_no_offender h6 hf hF2 (ρL.comp φ) hker hirr hsd A hA1 hA
  omega

theorem noPSL3Component (h6 : SelfDualInvolutionRank) (h9 : ActualLinearThreeSelfDualSections) :
    CFSG.QuasithinUnique.Setup.Top.NoPSL3Component :=
  fun _ _ _ _ _ _ _ hF hns _ _ hL _ hf =>
    original_minimal_parabolic_FF_actor_excludes_PSL3_components h6 h9 hF hns hL hf

end CFSG.QuasithinUnique.Setup.X7a
