module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaOuterMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmega

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup QuadraticMap Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ClassicalGroups.Orthogonal (elementaryGroup)
open CFSG.RankThree.OrthogonalInvolutions (commSpace)
open CFSG.RankThree.PartOne.AUTSL (mem_matrixDerived_iff_even)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

section Model

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_coordModel_two_of_three_le {n : ℕ} (hn : 3 ≤ n) (e : L ≃* StatedSp (n + 1) K) {t : G}
    {κ : Sp2mKind} (hκ : κ = .omegaPlus ∨ κ = .omegaMinus)
    (hglob : NsRowGlobal e t (q2GlobalKind κ)) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K')
      (Q : QuadraticForm K' (Fin (2 * (n + 1 + 1)) → K')), Nat.card K' = 2 ^ 1 ∧
      Q.polarBilin.Nondegenerate ∧
      (∃ T : Submodule K' (Fin (2 * (n + 1 + 1)) → K'), Module.finrank K' T = 3 ∧
        ∀ x ∈ T, Q x = 0) ∧
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
        elementaryGroup Q ∧
      matrixProjectiveImage Q = ⊤ ∧ Nonempty (nsGlobal e ≃* matrixProjectiveDerived Q) := by
  rcases hκ with rfl | rfl
  · have hty : LieModel (nsGlobal e) .POmegaMinus (n + 1 + 1) 2 1 := hglob.1
    obtain ⟨K', _, _, b, c, hirr, ε, hK', -⟩ :=
      exists_isometry_eq_of_lieModel_minus (n := n + 1) (by omega) hty
    have : CharP K' 2 := LinearPilot.charP_two_of_card_eq_two_pow hK'
    have hreg := regular_coordinateQuadMinus (n + 1 + 1) K' b c (by omega) hirr
    have hE := commutator_coordinateQuadMinus (n + 1 + 1) K' b c (by omega) hirr
    have hImg := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K'
      (n + 1 + 1) (by omega) b c hirr
    exact ⟨K', inferInstance, inferInstance, _, hK', hreg.1, hreg.2, hE, hImg, ⟨ε⟩⟩
  · have hty : LieModel (nsGlobal e) .POmegaPlus (n + 1 + 1) 2 1 := hglob.1
    have hC := CFSG.ComponentClassification.EvenOrthSelector.statedModel_of_lieModel
      (by decide) hty
    obtain ⟨-, K', _, _, hK', ⟨e'⟩⟩ := hC
    have : CharP K' 2 := LinearPilot.charP_two_of_card_eq_two_pow hK'
    have hreg := regular_coordinateQuadPlus (n + 1 + 1) K' (by omega)
    have hE := commutator_coordinateQuadPlus (n + 1 + 1) K' (by omega)
    have hImg := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K'
      (n + 1 + 1) (by omega)
    exact ⟨K', inferInstance, inferInstance, _, hK', hreg.1, hreg.2, hE, hImg,
      ⟨coordinatePlusWitnessEquiv K' e'⟩⟩

end Model

end CFSG.SeitzReduction.SymplecticPilot
