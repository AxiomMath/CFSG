module

public import CFSG.ClassicalInvolution.MilestoneAssemblyCore

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly
open CFSG.ClassicalInvolution.MilestoneAssembly (PieceSL3Big)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

@[expose] def ChainPieceSLsTwo (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeA p f 2 (conjClass K) z →
      ∃ U : Fin 4 → Subgroup G, (∀ i, U i ∈ conjClass K) ∧
        (∀ i j : Fin 4, (i : ℕ) + 1 < j → Commutes (U i) (U j)) ∧
        ∀ i j : Fin 4, (j : ℕ) = i + 1 →
          ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)

theorem pieceSL3Big_of_chainTwo (h : ChainPieceSLsTwo p f) : PieceSL3Big p f := by
  intro G _ _ _ hnab K z S _ hS
  have hshape : LocalShapeA p f 2 (conjClass K) z := localShapeA_of_T hS
  obtain ⟨U, hUΩ, hcomm, hpair⟩ := h G hnab K z S hshape
  obtain ⟨D, -, -⟩ := routeD_typeA_of_chain S.odd S.five (m := 2) (by omega) S.inClass
    (mem_conjClass_self K) (single_class K) S.conn S.cls hshape S.p1 U hUΩ hcomm hpair
  exact ⟨D⟩

end CFSG.ClassicalInvolution.RouteD
