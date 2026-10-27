module

public import CFSG.ClassicalInvolution.RouteD.GapsPatternDMain
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpin

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic (Commutes conjSub IsClassicalMember)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime]
  {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G} {m : ℕ}

theorem PartnerPatternD.of_toral_normal_plus (hm : 7 ≤ m) (hMFZ : FundNoncentral p)
    (c : TCtx p f .POmegaPlus m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaPlus m Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfixM : HasFixedMember Ω K β z)
    (hT : ToralNormalD c (partner_involution_commutes c.hp2 c.hz ht hKβ)) :
    PartnerPatternD p f m Ω K β t :=
  PartnerPatternD.of_toral_normal hm hMFZ (orthFacts_plus c.hp2 (by omega) c.hq) c hsingle hshape
    hβ ht hKβ hfixM hT

end CFSG.ClassicalInvolution.RouteD.Gaps
