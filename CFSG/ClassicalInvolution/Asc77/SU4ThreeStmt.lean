module

public import CFSG.ClassicalInvolution.Asc77.SU4Stmt
public import CFSG.ClassicalInvolution.Asc77.SU4ThreeNode

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.SU4Pattern
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

@[expose] def SU4LinearLiftStmt (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G) (S : RouteDSetup p f K z),
      LocalShapeT p f 2 .PSU 4 (conjClass K) z →
      ∀ (Λ : SuLayer p f 2 (conjClass K) z) (K₁ K₂ : Subgroup G) (z₁ : G),
        K₁ ∈ conjClass K → K₂ ∈ conjClass K → IsClassicalMember p f K₁ z₁ →
        Commutes K K₂ →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K K₁) →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K₁ K₂) →
        locImg (conjClass K) z K₂ ≤ (Λ.D.hom Λ.i₁).range →
        ∀ hz₁z : z₁ * z * z₁⁻¹ = z,
          LinearLift (Λ.ψ S.odd) (Gaps.locAut S.inClass.conjInvariant hz₁z)

theorem su4PatternStmt_of_three_mod_four (hq3 : p ^ f % 4 = 3) (hlin : SU4LinearLiftStmt p f) :
    SU4PatternStmt p f := by
  intro G _ _ _ hnab K z S hshape Λ K₁ K₂ z₁ hK₁ hK₂ hz₁ c02 p01 p12 hK₂i
  have hz₁z : z₁ * z * z₁⁻¹ = z := partner_involution_commutes S.odd S.cls hz₁ p01
  have hz₁2 : z₁ * z₁ = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one z₁
    rwa [hz₁.orderOf_eq_two] at this
  have hK₂' : K₂ ∈ centralizingMembers (conjClass K) {z} :=
    mem_centralizingMembers_of_commutes hK₂ S.cls.mem c02.symm
  obtain ⟨θ, hθr, hθτ⟩ := exists_chart_of_standardPair S.odd S.inClass.conjInvariant hz₁
    (le_centralizingLayer hK₂') hz₁z p12
  exact Λ.exists_shortNode_centralizer_of_linear S.odd S.five hq3 S.inClass S.p1 hz₁z hz₁2 hK₂'
    hK₂i θ hθr hθτ
    (hlin G hnab K z S hshape Λ K₁ K₂ z₁ hK₁ hK₂ hz₁ c02 p01 p12 hK₂i hz₁z)

theorem su4PatternStmt_of_linearLift (hlin : SU4LinearLiftStmt p f) : SU4PatternStmt p f := by
  by_cases h1 : p ^ f % 4 = 1
  · exact su4PatternStmt_of_one_mod_four h1
  by_cases h3 : p ^ f % 4 = 3
  · exact su4PatternStmt_of_three_mod_four h3 hlin
  intro G _ _ _ hnab K z S
  exfalso
  have hodd : p % 2 = 1 := by
    rcases Nat.Prime.eq_two_or_odd (Fact.out : p.Prime) with h | h
    · exact absurd h S.odd
    · exact h
  have : p ^ f % 2 = 1 := by rw [Nat.pow_mod, hodd]; simp
  omega

end CFSG.ClassicalInvolution.Generic.CoreAssembly
