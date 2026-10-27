module

public import CFSG.ClassicalInvolution.RouteD.TypeUPatternPartner
public import CFSG.ClassicalInvolution.RouteD.TypeUE6
public import CFSG.ClassicalInvolution.RouteD.GapsFive

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut

variable {p f m : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem UCtx.partner_normalizes_nodes (c : UCtx p f m Ω K z) (hm : 4 ≤ m) (nd : UNodes c)
    (hMFZ : FundNoncentral p) (hshape : LocalShapeU p f m Ω z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {β : Subgroup G} (hβ : β ∈ Ω) {t : G}
    (hwβ : IsClassicalMember p f β t) (hnK : ¬ Commutes K β)
    (hpair : ∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W K β)
    (hfixed : ∀ (a : ℕ) (ha : a < m), partnerFixed m ⟨a, ha⟩ → Commutes β (nd.j a))
    (hfirst : ¬ Commutes β (nd.j 0)) : ∀ a, a < m → conjSub t (nd.j a) = nd.j a := by
  obtain ⟨_, _, _, _, hnorm⟩ := c.partner_pattern hm nd hMFZ hshape hsingle hβ hwβ hnK hpair
    hfixed hfirst
  exact hnorm

theorem UCtx.partner_commute_w3 (c : UCtx p f 5 Ω K z) (nd : UNodes c) (hMFZ : FundNoncentral p)
    (hshape : LocalShapeU p f 5 Ω z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β : Subgroup G} (hβ : IsPartnerU c nd β) {wβ : G} (hwβ : IsClassicalMember p f β wβ) :
    Commute wβ (nd.w 3) := by
  have hfixed : ∀ (a : ℕ) (ha : a < 5), partnerFixed 5 ⟨a, ha⟩ → Commutes β (nd.j a) := by
    intro a ha hfx
    rcases hfx with hfx | ⟨h1, h2⟩
    · have : a = 4 := by
        simp only at hfx
        omega
      subst this
      exact hβ.last
    · exact hβ.mid a (by simpa using h1) (by simp only at h2; omega)
  have hnorm := c.partner_normalizes_nodes (by norm_num) nd hMFZ hshape hsingle hβ.mem hwβ hβ.nK
    hβ.pK hfixed hβ.n0
  exact commute_of_conjSub_eq (two_ne_zero_of_charP_ne_two c.hp2)
    (c.hex _ (nd.mem 3 (by norm_num)).1) (nd.isCl 3 (by norm_num)) (hnorm 3 (by norm_num))

theorem UCtx.exists_adapted_partner (c : UCtx p f 5 Ω K z) (nd : UNodes c)
    (hMFZ : FundNoncentral p) (hshape : LocalShapeU p f 5 Ω z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) :
    ∃ β, IsPartnerU c nd β ∧ ∀ wβ : G, IsClassicalMember p f β wβ → Commute wβ (nd.w 3) := by
  obtain ⟨β, hβ⟩ := c.exists_partnerU nd hsingle
  exact ⟨β, hβ, fun wβ hwβ => c.partner_commute_w3 nd hMFZ hshape hsingle hβ hwβ⟩

theorem UEndObstruction.stdpair_five (hMFZ : FundNoncentral p) (hshape : LocalShapeU p f 5 Ω z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (h : UEndObstruction p f 5 Ω K z) :
    ∃ (c : UCtx p f 5 Ω K z) (nd : UNodes c) (β : Subgroup G), IsPartnerU c nd β ∧
      ¬ Commutes β (nd.j 3) ∧ ∃ W : Subgroup G,
        UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W β (nd.j 3) := by
  obtain ⟨c, nd, β, hβΩ, ⟨wβ, hwβ⟩, hnK, hpK, hn0, hp0, hlast, hmid, hnot⟩ := h
  have hβ : IsPartnerU c nd β := ⟨hβΩ, ⟨wβ, hwβ⟩, hnK, hpK, hn0, hp0, hlast, hmid⟩
  rcases c.commutes_or_stdpair_end nd hsingle hβ hwβ
    (c.partner_commute_w3 nd hMFZ hshape hsingle hβ hwβ) with h3 | h3
  · exact absurd h3 hnot
  · exact ⟨c, nd, β, hβ, hnot, h3⟩

theorem UEndObstruction.pattern_five (hMFZ : FundNoncentral p) (hshape : LocalShapeU p f 5 Ω z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (h : UEndObstruction p f 5 Ω K z) :
    ∃ (c : UCtx p f 5 Ω K z) (nd : UNodes c) (β : Subgroup G) (t : G),
      IsPartnerU c nd β ∧ IsClassicalMember p f β t ∧ ¬ Commutes β (nd.j 3) ∧
      ∃ htz : t * z * t⁻¹ = z, ∀ x, locAut c.hΩ.conjInvariant htz (c.d.ψ x) =
        c.d.ψ (conjSign c.card_eq (partnerSigns 5 1) x) := by
  obtain ⟨c, nd, β, hβΩ, ⟨t, hwβ⟩, hnK, hpK, hn0, hp0, hlast, hmid, hnot⟩ := h
  have hβ : IsPartnerU c nd β := ⟨hβΩ, ⟨t, hwβ⟩, hnK, hpK, hn0, hp0, hlast, hmid⟩
  have hfixed : ∀ (a : ℕ) (ha : a < 5), partnerFixed 5 ⟨a, ha⟩ → Commutes β (nd.j a) := by
    intro a ha hfx
    rcases hfx with hfx | ⟨h1, h2⟩
    · have : a = 4 := by
        simp only at hfx
        omega
      subst this
      exact hlast
    · exact hmid a (by simpa using h1) (by simp only at h2; omega)
  obtain ⟨htz, w, hpat, hw0, -⟩ := c.partner_pattern (by norm_num) nd hMFZ hshape hsingle hβΩ hwβ
    hnK hpK hfixed hn0
  have hw1 : w = 1 := by
    have : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    exact (this w).resolve_left fun hw => hnot (hw0 hw)
  subst hw1
  exact ⟨c, nd, β, t, hβ, hwβ, hnot, htz, hpat⟩

theorem routeD_typeU_five_chain (hMFZ : FundNoncentral p) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {K : Subgroup G}
    (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω)
    {z : G} (hz : IsClassicalMember p f K z) (hshape : LocalShapeU p f 5 Ω z)
    (hP1 : LocalOddCentral Ω {z}) :
    (∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSU ∧ D.rank i = 8) ∨
      ∃ U : Fin 6 → Subgroup G, IsPhanChainE6 p f U ∧ ∀ i, U i ∈ Ω :=
  (routeD_typeU_dichotomy hp2 hq (by norm_num) hΩ hex hK hsingle hconn hz hshape hP1).imp id
    fun hobs => by
      obtain ⟨c, nd, β, hβ, -, hW⟩ := hobs.stdpair_five hMFZ hshape hsingle
      obtain ⟨U, hUΩ, hc, hp⟩ := c.chain_E6 nd hβ hW
      exact ⟨U, isPhanChainE6_of_members c.hq c.hΩ c.hex hUΩ hc hp, hUΩ⟩

theorem routeD_typeU_five_final (hMFZ : FundNoncentral p) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hPhan : PhanE6 p f) {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    {K : Subgroup G} (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hconn : DeltaConnected Ω) {z : G} (hz : IsClassicalMember p f K z)
    (hshape : LocalShapeU p f 5 Ω z) (hP1 : LocalOddCentral Ω {z}) :
    (∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSU ∧ D.rank i = 8) ∨
      ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .twistedE6 ∧ D.rank i = 0 :=
  routeD_typeU_five_of_phanE6 hp2 hq hPhan hΩ hex hK hsingle hconn hz hshape hP1
    fun c nd {_} hβ {_} hwβ => c.partner_commute_w3 nd hMFZ hshape hsingle hβ hwβ

end CFSG.ClassicalInvolution.RouteD
