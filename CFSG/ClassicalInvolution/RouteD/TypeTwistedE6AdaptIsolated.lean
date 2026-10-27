module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptClass
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6P1x
public import CFSG.ClassicalInvolution.RouteD.NoG2D4SU6
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptModel
public import CFSG.ClassicalInvolution.RouteD.SmallTwinChainX
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import CFSG.ClassicalInvolution.Models.SymplecticPairs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.G2D4
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

section Isolated

variable [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem te6PartnerIsolated_of_partner (hMFZ : Gaps.FundNoncentral p)
    (hIH : LocalLieSystems p f Ω) (c : UCtx p f 5 Ω K z) (nd : UNodes c)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (Dz : LieSystemData p f (locQuot Ω z) (locFamily Ω z)) {β : Subgroup G}
    (hβ : IsPartnerU c nd β) (hn3 : ¬ Commutes β (nd.j 3))
    (hP1x : LocalOddCentral Ω {z * nd.w 0}) : TE6PartnerIsolated c nd := by
  classical
  obtain ⟨D⟩ := exists_lieSystemData hIH (not_subset_center_mul hMFZ c nd hsingle Dz)
  have hβx : β ∈ centralizingMembers Ω {z * nd.w 0} :=
    ⟨hβ.mem, UCtx.partner_le_centralizer_mul c nd (by norm_num : 0 < 5) hβ.mem hβ.pK hβ.p0⟩
  have hlink := linked_of_visible c nd hβx hβ.nK hβ.n0 hn3
  obtain ⟨φ, hφ, hφK⟩ := exists_visible_equiv' c nd
  have hKx := UNodes.K_mem_centralizingMembers_mul c nd (by norm_num : 0 < 5)
  have hcard₀ : D.card = 1 := card_eq_one_of_linked c.hΩ c.hex hP1x D hKx c.hz.mem hlink
  have hsub : Subsingleton (Fin D.card) := Fin.subsingleton_iff_le_one.mpr hcard₀.le
  have hM0' := UNodes.mem_centralizingMembers_mul c nd (by norm_num : 0 < 5) (Or.inl rfl)
  have hM2' := UNodes.mem_centralizingMembers_mul c nd (by norm_num : 2 < 5)
    (Or.inr (by norm_num))
  obtain ⟨i₀, hi₀⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨K, hKx, rfl⟩)
  have hall : ∀ N ∈ centralizingMembers Ω {z * nd.w 0},
      N ∈ compMembers Ω (z * nd.w 0) D i₀ := by
    intro N hN
    obtain ⟨j, hj⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
    exact ⟨hN, hsub.elim j i₀ ▸ hj⟩
  have hexc : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := by
    intro i
    have hi : i = i₀ := hsub.elim i i₀
    subst hi
    exact tag_ne_of_commuting_triple c.hp2 c.hΩ c.hex D (hall K hKx) (hall _ hM0') (hall _ hM2')
      (nd.commK 0 (by norm_num)) (nd.commK 2 (by norm_num))
      (nd.far 0 (by norm_num) 2 (by norm_num) (by norm_num))
  obtain ⟨hsc, hperf⟩ := componentFacts_of_no_exotic D c.hp2 (by have := c.hq; omega) hexc
  obtain ⟨hcard, i₁, ht, hn, R₀, hR₀⟩ := shape_of_perpTableR c.hp2 c.hq c.hΩ c.hex hP1x D hexc
    hKx c.hz hlink TE6Layer.rel φ hφ hφK (te6PerpTableR p f)
  have hexp : D.exp i₁ = f := by
    rcases D.exp_eq i₁ with h | ⟨h, -⟩
    · exact h
    · exact absurd (ht.symm.trans h) (by decide)
  have hF : NoCommonCommutant p f (D.tag i₁) (D.rank i₁) (D.exp i₁) := by
    rw [ht, hn, hexp]
    exact noCommonCommutant_pOmegaMinus_five c.hp2 c.hq
  have hall₁ : ∀ N ∈ centralizingMembers Ω {z * nd.w 0},
      N ∈ compMembers Ω (z * nd.w 0) D i₁ := fun N hN => by
    have := hsub.elim i₀ i₁
    subst this
    exact hall N hN
  intro N hN pKN _ L hL hLK hNL
  have hLx : L ∈ centralizingMembers Ω {z * nd.w 0} :=
    (mem_centralizingMembers_pair.mp hL).1
  have hLz : L ∈ centralizingMembers Ω {z} :=
    ⟨hLx.1, (mem_centralizingMembers_pair.mp hL).2⟩
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨c.hK, le_centralizer_of_isClassicalMember c.hz⟩
  have hKL : Commutes K L := by
    rcases commutes_or_eq_at_conj hMFZ c.hΩ c.hex c.hP1 Dz (g := 1) (y := z) (by simp) hKz hLz
      c.hz with h | h
    · exact h
    · exact absurd h hLK
  obtain ⟨R_K, hRK⟩ := exists_corr_left c.hΩ c.hex D (hall₁ K hKx)
  obtain ⟨R_N, hRN⟩ := exists_corr_left c.hΩ c.hex D (hall₁ N hN)
  obtain ⟨R_L, hRL⟩ := exists_corr_left c.hΩ c.hex D (hall₁ L hLx)
  have hlin : ∃ W, LinearBlockStandardPair (GaloisField p f) W (R_K.map (D.hom i₁))
      (R_N.map (D.hom i₁)) := by
    obtain ⟨W₀, hW₀⟩ := pKN
    obtain ⟨W, hW⟩ := RouteD.linearBlockStandardPair_locImg hP1x (le_centralizingLayer hKx)
      (le_centralizingLayer hN) ⟨W₀, hW₀⟩
    rw [hRK.2.2, hRN.2.2] at hW
    exact ⟨W, hW⟩
  exact hF (D.hom i₁) (D.ker_le_center i₁) R_K hRK.2.1 R_N hRN.2.1 R_L hRL.2.1 hlin
    ((corr_commutes c.hΩ hP1x (hperf i₁) hRK hRL).mp hKL).symm
    ((corr_commutes c.hΩ hP1x (hperf i₁) hRN hRL).mp hNL).symm

end Isolated

end CFSG.ClassicalInvolution.RouteD.NonClassical
