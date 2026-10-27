module

public import CFSG.ClassicalInvolution.RouteD.GapsToralD
public import CFSG.ClassicalInvolution.RouteD.GapsPatternDAdapted

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem PartnerPatternD.of_torusFixed_of_adapted {m : ℕ} (hm : 5 ≤ m) (hMFZ : FundNoncentral p)
    (c : TCtx p f .POmegaPlus m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaPlus m Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfixM : HasFixedMember Ω K β z)
    (hT : TorusFixedD (by omega : 3 ≤ m) c (partner_involution_commutes c.hp2 c.hz ht hKβ))
    (hadapt : ∀ (nd : DNodes p f m Ω K) {β : Subgroup G} {t : G}, β ∈ Ω →
      IsClassicalMember p f β t → (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) →
      ∀ {pp : Fin m}, (∀ a, a ≠ pp → Commutes β (nd.J a)) → ¬ Commutes β (nd.J pp) →
        conjSub t (nd.J pp) = nd.J pp →
        pp.val = 0 ∧ ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (nd.J pp)) :
    PartnerPatternD p f m Ω K β t := by
  obtain ⟨W, hW⟩ := hKβ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two, pow_two] at this
  have hKt : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  exact PartnerPatternD.of_toral_normal_of_adapted hm hMFZ (orthFacts_plus c.hp2 hm c.hq) c hsingle
    hshape hβ ht ⟨W, hW⟩ hfixM (toralNormalD_of_torusFixed hm (by omega) c _ h2t hKt hT) hadapt

theorem PartnerPatternD.of_torusFixed_five (hMFZ : FundNoncentral p)
    (c : TCtx p f .POmegaPlus 5 Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaPlus 5 Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfixM : HasFixedMember Ω K β z)
    (hT : TorusFixedD (by norm_num : 3 ≤ 5) c
      (partner_involution_commutes c.hp2 c.hz ht hKβ)) :
    PartnerPatternD p f 5 Ω K β t :=
  PartnerPatternD.of_torusFixed_of_adapted (le_refl 5) hMFZ c hsingle hshape hβ ht hKβ hfixM hT
    fun nd {_ _} hβ' ht' hKβ' {_} hfix hmov hnorm =>
      adapted_pattern_D5 (orthFacts_plus c.hp2 (le_refl 5) c.hq) c hsingle hshape nd hβ' ht' hKβ'
        hfix hmov hnorm

end CFSG.ClassicalInvolution.RouteD.Gaps
