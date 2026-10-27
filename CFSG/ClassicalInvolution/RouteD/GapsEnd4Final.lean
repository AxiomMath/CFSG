module

public import CFSG.ClassicalInvolution.RouteD.GapsEnd4
public import CFSG.ClassicalInvolution.RouteD.GapsS3
public import CFSG.ClassicalInvolution.ModelFacts.LinearAutMain

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.ModelFacts.LinearAut

variable {p f : ℕ} [Fact p.Prime]

theorem standardPairAutAbelian_galoisField [NeZero f] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    StandardPairAutAbelian (GaloisField p f) := by
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (NeZero.ne f)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hcard]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have h5 : 5 ≤ Nat.card (GaloisField p f) := by rw [hcard]; exact hq
  have hcl : LinearAutClassification (GaloisField p f) 3 :=
    linearAutClassification hp2 hq (by norm_num)
  exact @standardPairAutAbelian_of_classification _ _ _ hodd h5 hcl

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem ACtx.end_relation_four (c : ACtx p f 4 Ω K z) (nd : Nodes c) (hMFZ : FundNoncentral p)
    (hshape : LocalShapeA p f 4 Ω z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (hwβ : IsClassicalMember p f β t)
    (hnK : ¬ Commutes K β) (hpair : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfirst : ¬ Commutes β (nd.j 0)) (hmid : Commutes β (nd.j 1)) (hlast : Commutes β (nd.j 3)) :
    Commutes β (nd.j 2) :=
  ACtx.commutes_beta_second_last_four c nd hMFZ
    (linearAutClassification c.hp2 c.hq (by norm_num)) hshape hsingle hβ hwβ hnK hpair hfirst hmid
    hlast

end CFSG.ClassicalInvolution.RouteD.Gaps
