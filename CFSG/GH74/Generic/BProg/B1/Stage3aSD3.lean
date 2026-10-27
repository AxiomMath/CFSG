module

public import CFSG.GH74.Generic.S3.OnlyInvO3
public import CFSG.GH74.Generic.BProg.B1.Stage3aSD1

public section

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup G}

theorem S3PairData.false_of_universal
    (h : S3PairData G x K) (hU : IsUniversalComponent K) : False := by
  have : IsSimpleGroup G := h.hyp.simple
  obtain ⟨e, heC, he2, hex⟩ := h.exists_e
  have hxC : x ∈ centralizer (K : Set G) := by
    rw [mem_centralizer_iff]
    intro k hk
    exact mem_centralizer_singleton_iff.1 (h.le hk)
  have heCK : e ∈ centralizer (K : Set G) := h.cxk_le heC
  have hq : CFSG.Assembly.IsQuasisimple K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr h.hq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrk : 2 ≤ CFSG.Assembly.pRank 2 K := by
    have h1 : CFSG.pRank 2 ↥K = CFSG.Open.pRank 2 K :=
      (CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥K).trans
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup K).symm
    have h2 : 2 ≤ CFSG.Open.pRank 2 K := h1 ▸ h.two_le_pRank_K
    exact h2
  have hCeven : Even (Nat.card (centralizer (K : Set G))) := by
    have h3 := orderOf_dvd_natCard (⟨x, hxC⟩ : centralizer (K : Set G))
    have e' : orderOf (⟨x, hxC⟩ : centralizer (K : Set G)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact h.x2
    rw [e'] at h3
    exact even_iff_two_dvd.2 h3
  have hstd : CFSG.Assembly.ComponentType.IsStandardSubgroup K :=
    universal_rank_two_component_isStandardSubgroup h.hyp.nonab hq hrk hCeven hU
  have hrank : 2 ≤ CFSG.Open.pRank 2 (centralizer (K : Set G)) := by
    have h1 : CFSG.pRank 2 ↥(centralizer (K : Set G)) =
        CFSG.Open.pRank 2 (centralizer (K : Set G)) :=
      (CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥(centralizer (K : Set G))).trans
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (centralizer (K : Set G))).symm
    rw [← h1]
    refine two_le_pRank_of_two_involutions (a := ⟨e, heCK⟩) (b := ⟨x, hxC⟩) ?_ ?_ ?_ ?_
    · rw [Subgroup.orderOf_mk]; exact he2
    · rw [Subgroup.orderOf_mk]; exact h.x2
    · intro h'
      exact hex (congrArg Subtype.val h')
    · exact Subtype.ext (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 heC).1)
  have hO : Open.standardComponentOddCore G = ⊥ := by
    refine sSup_eq_bot.2 fun N hN => ?_
    have := hN.1
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal N).resolve_right fun htop => ?_
    have hGodd : Odd (Nat.card G) := by
      rw [← Subgroup.card_top (G := G), ← htop]
      exact hN.2
    exact Nat.not_even_iff_odd.2 hGodd (even_card_of_nonabelian_simple h.hyp.nonab)
  have hnotnormal : ¬ K.Normal := by
    intro hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hb | ht
    · obtain ⟨a, b, hab⟩ := S45.exists_noncomm_of_isQuasisimple h.hq
      apply hab
      have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.1 (hb ▸ a.2))
      rw [ha]; simp
    · have hxz : x ∈ center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        have hg : g ∈ K := by rw [ht]; trivial
        exact (mem_centralizer_iff.1 hxC) g hg
      rw [center_eq_bot_of_isSimpleGroup h.hyp.simple h.hyp.nonab] at hxz
      have hx1 : x = 1 := Subgroup.mem_bot.1 hxz
      have := h.x2
      rw [hx1, orderOf_one] at this
      omega
  let eK : (↥K ⧸ center ↥K) ≃* (↥K ⧸ pPrimeCore 2 ↥K) :=
    QuotientGroup.quotientMulEquivOfEq h.pPrimeCore_eq_center.symm
  obtain ⟨p, f, hp, hp2, hq3, hmodel⟩ := h.shape
  have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq5 : 5 ≤ p ^ f := by
    have := Nat.odd_iff.1 hqodd
    omega
  have hcard : 505 ≤ Nat.card (↥K ⧸ center ↥K) := by
    rw [Nat.card_congr eK.toEquiv]
    exact le_card_of_l3 hp2 hq5 hmodel
  have hAlt : ∀ n : ℕ, 5 ≤ n → n.factorial / 2 < 505 →
      ¬ Nonempty ((↥K ⧸ center ↥K) ≃* alternatingGroup (Fin n)) := by
    intro n hn hlt ⟨e'⟩
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have h' := Nat.card_congr e'.toEquiv
    have h2 : Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [h2] at h'
    omega
  have h28 : ¬ StatedClassicalModel (↥K ⧸ center ↥K) .PSL 2 2 3 := by
    intro h'
    have hl : LieModel (↥K ⧸ center ↥K) .PSL 2 2 3 := lieModel_of_statedClassicalModel (by decide) h'
    have h504 := card_of_lieModel_PSL (by norm_num) hl
    rw [show (2 - 1 : ℕ) = 1 from rfl, show (2 : ℕ) ^ 3 = 8 from rfl, ordA_one_eight] at h504
    omega
  have hlie : OddLieType (↥K ⧸ center ↥K) := by
    rcases hmodel with hm | hm
    · obtain ⟨hadm, -⟩ := stated_of_lieModel_PSL hm
      exact ⟨.PSL, 3, p, f, hp, hp2, hadm, lieModel_of_mulEquiv eK.symm hm⟩
    · obtain ⟨hadm, -⟩ := stated_of_lieModel_PSU hm
      exact ⟨.PSU, 3, p, f, hp, hp2, hadm, lieModel_of_mulEquiv eK.symm hm⟩
  exact RankTwoFoundation.rankTwoOddLieStandard G K
    ⟨kProper_of_kgh h.hyp.kgh, hstd, hnotnormal, hrank⟩ hO
    ⟨hlie, hAlt 5 (by norm_num) (by decide), hAlt 6 (by norm_num) (by decide), h28⟩

end CFSG.GH74.Generic.BProg.B1
