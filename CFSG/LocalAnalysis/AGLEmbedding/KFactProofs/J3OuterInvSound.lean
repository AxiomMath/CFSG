module

public import CFSG.Sporadic.Bridge.TwoGen
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public meta import Certificates.Data.CFSGNative.Bridge.SurjA
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3OuterInvGroup
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3SylowPrim
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3SylowGroup
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.AGLEmbedding.KFactProofs.J3OuterInv

open CFSG.AGLEmbedding.KFactProofs.J3Sylow CFSG.Quasithin CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native

section Helpers

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

theorem eq_one_of_comm {ω₀ : Fin n} (htr : ∀ q, ∃ x : G, x • ω₀ = q) {τ : Equiv.Perm (Fin n)}
    (h0 : τ ω₀ = ω₀)
    (hc : ∀ x : G, τ * MulAction.toPermHom G (Fin n) x = MulAction.toPermHom G (Fin n) x * τ) :
    τ = 1 := by
  refine Equiv.ext fun q => ?_
  obtain ⟨x, rfl⟩ := htr q
  have := congrArg (fun π : Equiv.Perm (Fin n) => π ω₀) (hc x)
  simp only [Equiv.Perm.mul_apply] at this
  change τ (x • ω₀) = x • τ ω₀ at this
  rw [h0] at this
  simpa using this

end Helpers

end CFSG.AGLEmbedding.KFactProofs.J3OuterInv
