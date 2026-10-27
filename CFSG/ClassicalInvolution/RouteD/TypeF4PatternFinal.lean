module

public import CFSG.ClassicalInvolution.RouteD.TypeF4PatternAdapt

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem routeD_typeF4_of_twin_inputs (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hconn : DeltaConnected Ω) (hz : IsClassicalMember p f K z)
    (hshape : LocalShapeC p f 3 Ω z) (hP1 : LocalOddCentral Ω {z}) (hIH : LocalLieSystems p f Ω)
    (hP1x : TwinProductP1 p f Ω K z) (hexc : TwinProductNoExotic p f Ω K z)
    (hlink : F4Linked p f Ω K z) (hTable : F4PerpTableR p f)
    (hTwin : TwinPartnerFactTwin p f .POmegaOdd 4 f) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .F4 :=
  routeD_typeF4_of_twin_data hp2 hq hΩ hex hK hsingle hconn hz hshape hP1 hIH hP1x hexc hlink
    hTable hTwin fun d _ hj0 himg0 himg1 himg2 _ _ ht _ hNj htz =>
    adaptedF4_of_partner hp2 hq hΩ hP1 d hj0 himg0 himg1 himg2 ht hNj htz

end CFSG.ClassicalInvolution.RouteD.NonClassical
