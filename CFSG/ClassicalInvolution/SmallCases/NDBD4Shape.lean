module

public import CFSG.ClassicalInvolution.Asc77.WP3LayerPair

public section

namespace CFSG.ClassicalInvolution.NDB.D4

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem localShapeT_of_exact (hex : ExactMembers Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) {z : G} {a : ℕ} {tY : StatedLieTag}
    {nY : ℕ} (D : LocalLieSystemAt p f (exactFamily Ω z) z) (hcard : D.card = a + 1)
    {i₁ : Fin D.card} (ht : D.tag i₁ = tY) (hn : D.rank i₁ = nY)
    (hrest : ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2) :
    RouteD.LocalShapeT p f a tY nY Ω z := by
  have h : centralizingMembers (exactFamily Ω z) {z} = centralizingMembers Ω {z} :=
    (centMembers_exactFamily Ω z).trans (exactFamily_eq_centMembers_of_exact hex hcls)
  have key : ∀ S₁ S₂ : Set (Subgroup G), S₁ = S₂ →
      (∃ D : LieSystemData p f (↥(⨆ L ∈ S₁, L) ⧸ classicalInvolutionOddCore ↥(⨆ L ∈ S₁, L))
        (oddQuotientFamily (restrictFamily S₁ (⨆ L ∈ S₁, L))), D.card = a + 1 ∧
          ∃ i₁ : Fin D.card, D.tag i₁ = tY ∧ D.rank i₁ = nY ∧
            ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2) →
      ∃ D : LieSystemData p f (↥(⨆ L ∈ S₂, L) ⧸ classicalInvolutionOddCore ↥(⨆ L ∈ S₂, L))
        (oddQuotientFamily (restrictFamily S₂ (⨆ L ∈ S₂, L))), D.card = a + 1 ∧
          ∃ i₁ : Fin D.card, D.tag i₁ = tY ∧ D.rank i₁ = nY ∧
            ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2 := by
    intro S₁ S₂ hS
    subst hS
    exact id
  exact key _ _ h ⟨D, hcard, i₁, ht, hn, hrest⟩

end CFSG.ClassicalInvolution.NDB.D4
