module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpTable
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Local

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.G2D4
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

section Consumer

variable [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem exists_te6Base_partner_noexc (hf : 1 ≤ f) (hMFZ : Gaps.FundNoncentral p)
    (hIH : LocalLieSystems p f Ω) (c : UCtx p f 5 Ω K z) (nd : UNodes c)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (Dz : LieSystemData p f (locQuot Ω z) (locFamily Ω z)) {β : Subgroup G}
    (hβ : IsPartnerU c nd β) (hn3 : ¬ Commutes β (nd.j 3))
    (hP1x : LocalOddCentral Ω {z * nd.w 0})
    (hTable : TE6PerpTableR p f) (hAdapt : TE6Adaptation hf nd) :
    ∃ V : Fin 3 → Subgroup G, IsTE6Base p f hf Ω K z V ∧ TE6Partner p f Ω V := by
  classical
  obtain ⟨D⟩ := exists_lieSystemData hIH (not_subset_center_mul hMFZ c nd hsingle Dz)
  have hβx : β ∈ centralizingMembers Ω {z * nd.w 0} :=
    ⟨hβ.mem, UCtx.partner_le_centralizer_mul c nd (by norm_num : 0 < 5) hβ.mem hβ.pK hβ.p0⟩
  have hlink := linked_of_visible c nd hβx hβ.nK hβ.n0 hn3
  obtain ⟨φ, hφ, hφK⟩ := exists_visible_equiv' c nd
  have hKx := UNodes.K_mem_centralizingMembers_mul c nd (by norm_num : 0 < 5)
  have hcard₀ : D.card = 1 := card_eq_one_of_linked c.hΩ c.hex hP1x D hKx c.hz.mem hlink
  have hsub₀ : Subsingleton (Fin D.card) := Fin.subsingleton_iff_le_one.mpr hcard₀.le
  have hM0' := UNodes.mem_centralizingMembers_mul c nd (by norm_num : 0 < 5) (Or.inl rfl)
  have hM2' := UNodes.mem_centralizingMembers_mul c nd (by norm_num : 2 < 5)
    (Or.inr (by norm_num))
  obtain ⟨i₀, hi₀⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨K, hKx, rfl⟩)
  have hall : ∀ N ∈ centralizingMembers Ω {z * nd.w 0},
      N ∈ compMembers Ω (z * nd.w 0) D i₀ := by
    intro N hN
    obtain ⟨j, hj⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
    exact ⟨hN, hsub₀.elim j i₀ ▸ hj⟩
  have hexc : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := by
    intro i
    have hi : i = i₀ := hsub₀.elim i i₀
    subst hi
    exact tag_ne_of_commuting_triple c.hp2 c.hΩ c.hex D (hall K hKx) (hall _ hM0') (hall _ hM2')
      (nd.commK 0 (by norm_num)) (nd.commK 2 (by norm_num))
      (nd.far 0 (by norm_num) 2 (by norm_num) (by norm_num))
  obtain ⟨hsc, hperf⟩ := componentFacts_of_no_exotic D c.hp2 (by have := c.hq; omega) hexc
  obtain ⟨hcard, i₁, ht, hn, R₀, hR₀⟩ := shape_of_perpTableR c.hp2 c.hq c.hΩ c.hex hP1x D hexc
    hKx c.hz hlink TE6Layer.rel φ hφ hφK hTable
  have hexp : D.exp i₁ = f := by
    rcases D.exp_eq i₁ with h | ⟨h, -⟩
    · exact h
    · exact absurd (ht.symm.trans h) (by decide)
  have hTwin' : TwinPartnerFactTwin p f (D.tag i₁) (D.rank i₁) (D.exp i₁) := by
    rw [ht, hn, hexp]
    exact twinPartnerFactTwin_pOmegaMinus_five c.hp2 c.hq
  have hsub : Subsingleton (Fin D.card) := Fin.subsingleton_iff_le_one.mpr hcard.le
  have hKc : K ∈ compMembers Ω (z * nd.w 0) D i₁ := ⟨hKx, hR₀.2.2 ▸ Subgroup.map_le_range _ _⟩
  have hM0 := UNodes.mem_centralizingMembers_mul c nd (by norm_num : 0 < 5) (Or.inl rfl)
  have hMc : nd.j 0 ∈ compMembers Ω (z * nd.w 0) D i₁ := by
    obtain ⟨j, hj⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨nd.j 0, hM0, rfl⟩)
    exact ⟨hM0, hsub.elim j i₁ ▸ hj⟩
  obtain ⟨N, hN, pKN, pNM⟩ := exists_twin_partner_of_twin c.hq c.hΩ c.hex hP1x D (hsc i₁)
    (hperf i₁) hTwin' hKc hMc (nd.ne_K 0 (by norm_num)).symm (nd.commK 0 (by norm_num))
    c.hz.mem (nd.isCl 0 (by norm_num)).mem c.hz.orderOf_eq_two
    (nd.isCl 0 (by norm_num)).orderOf_eq_two rfl
  obtain ⟨V, hV, hV0, hc1, hc2⟩ := hAdapt N hN.1 pKN pNM
  refine ⟨V, hV, N, hN.1.1, ?_, hc1, hc2⟩
  rw [hV0]
  exact pNM

theorem routeD_typeU_five_of_nonclassical_noexc (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .twistedE6 0 p f) (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeU p f 5 Ω z)
    (hP1 : LocalOddCentral Ω {z}) (hMFZ : Gaps.FundNoncentral p)
    (hIH : LocalLieSystems p f Ω)
    (hP1x : ∀ (c : UCtx p f 5 Ω K z) (nd : UNodes c) {β : Subgroup G}, IsPartnerU c nd β →
      ¬ Commutes β (nd.j 3) → LocalOddCentral Ω {z * nd.w 0})
    (hTable : TE6PerpTableR p f)
    (hAdapt : ∀ (c : UCtx p f 5 Ω K z) (nd : UNodes c) {β : Subgroup G}, IsPartnerU c nd β →
      ¬ Commutes β (nd.j 3) → TE6Adaptation hadm.2.1 nd) :
    (∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSU ∧ D.rank i = 8) ∨
      ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .twistedE6 ∧ D.rank i = 0 :=
  (routeD_typeU_dichotomy hp2 hq (by norm_num) hΩ hex hK hsingle hconn hz hshape hP1).imp id
    fun hobs => by
      obtain ⟨c, nd, β, hβΩ, hβcl, hnK, hpK, hn0, hp0, hlast, hmid, hnot⟩ := hobs
      obtain ⟨Dz, -⟩ := hshape
      have hβ : IsPartnerU c nd β := ⟨hβΩ, hβcl, hnK, hpK, hn0, hp0, hlast, hmid⟩
      obtain ⟨V, hV, hpart⟩ := exists_te6Base_partner_noexc hadm.2.1 hMFZ hIH c nd hsingle Dz hβ
        hnot (hP1x c nd hβ hnot) hTable (hAdapt c nd hβ hnot)
      exact routeD_twistedE6_of_base hadm hq hΩ hK hsingle hconn hz hV hpart

theorem routeD_typeU_five_of_adaptation_noexc (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .twistedE6 0 p f) (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeU p f 5 Ω z)
    (hP1 : LocalOddCentral Ω {z}) (hMFZ : Gaps.FundNoncentral p)
    (hIH : LocalLieSystems p f Ω)
    (hP1x : ∀ (c : UCtx p f 5 Ω K z) (nd : UNodes c) {β : Subgroup G}, IsPartnerU c nd β →
      ¬ Commutes β (nd.j 3) → LocalOddCentral Ω {z * nd.w 0})
    (hAdapt : ∀ (c : UCtx p f 5 Ω K z) (nd : UNodes c) {β : Subgroup G}, IsPartnerU c nd β →
      ¬ Commutes β (nd.j 3) → TE6Adaptation hadm.2.1 nd) :
    (∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSU ∧ D.rank i = 8) ∨
      ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .twistedE6 ∧ D.rank i = 0 :=
  routeD_typeU_five_of_nonclassical_noexc hp2 hadm hq hΩ hex hK hsingle hconn hz hshape hP1 hMFZ
    hIH hP1x (te6PerpTableR p f) hAdapt

end Consumer

end CFSG.ClassicalInvolution.RouteD.NonClassical
