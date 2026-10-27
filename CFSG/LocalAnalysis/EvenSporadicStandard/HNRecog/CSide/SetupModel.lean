module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.Setup

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Subgroup CFSG.RankThree.Literature.FSmith CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {C : Type} [Group C] {Q : Subgroup C} [hQn : Q.Normal]
  [Module (ZMod 2) (Additive (Abelianization Q))]

theorem CSideSetup.q_invariant [Finite C] (hC : WeakHyp C Q) (S : CSideSetup C Q) (g : A5 × A5)
    (u : Additive (Abelianization Q)) :
    extraspecialQuadForm hC.isExtraspecialPGroup (S.σ g u) =
      extraspecialQuadForm hC.isExtraspecialPGroup u := by
  haveI : Finite Q := hC.finite_Q
  obtain ⟨l, rfl⟩ := S.surj g
  rw [S.sigma_eq l]
  exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1
    (conjLinEquiv_mem hC.isExtraspecialPGroup hQn (l : C)) u

theorem CSideSetup.model [Finite C] (hC : WeakHyp C Q)
    (S : CSideSetup C Q) : CSideModel (extraspecialQuadForm hC.isExtraspecialPGroup) S.σ := by
  haveI : Finite Q := hC.finite_Q
  haveI : Finite (Additive (Abelianization Q)) := by
    change Finite (Q ⧸ _root_.commutator Q)
    infer_instance
  exact cSideModel_of_stdHyp _ (extraspecialQuadForm_nondegenerate hC.isExtraspecialPGroup)
    S.σ S.std (S.q_invariant hC)

end CFSG.EvenSporadicStandard.HNRecog.CSide
