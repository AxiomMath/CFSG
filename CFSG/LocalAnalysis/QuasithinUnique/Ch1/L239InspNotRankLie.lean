module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspNotRank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOddRankOneGlue
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134EvenClassicalProp

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique.Setup.Family

section Rank

theorem two_le_pRank_of_not_isCyclic {P : Type} [Group P] [Finite P] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hP : IsPGroup p P) (hnc : ¬ IsCyclic P) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup P) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p P) := ⟨hP⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hp2 hnc
  exact CFSG.SectionRank.le_pRank hp.one_lt le_top
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p S).1 hSel) hScard

theorem two_le_pRank_of_surjective {G Q : Type} [Group G] [Finite G] [Group Q] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (f : G →* Q) (hf : Function.Surjective f)
    (h : 2 ≤ CFSG.pRank p Q) : 2 ≤ CFSG.pRank p G := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite Q := Finite.of_surjective f hf
  by_contra hlt
  have hlt' : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hlt
    omega
  have hcycG : ∀ P : Sylow p G, IsCyclic ↥(P : Subgroup G) := by
    intro P
    by_contra hnc
    have h2 := two_le_pRank_of_not_isCyclic hp hp2 P.isPGroup' hnc
    have h3 := CFSG.SectionRank.pRank_le_map hp.one_lt (P : Subgroup G).subtype
      (P : Subgroup G).subtype_injective ⊤
    have h4 := CFSG.SectionRank.pRank_mono hp.one_lt
      (le_top : ((⊤ : Subgroup ↥(P : Subgroup G)).map (P : Subgroup G).subtype) ≤ ⊤)
    omega
  have hcycQ : ∀ P : Sylow p Q, IsCyclic ↥(P : Subgroup Q) := by
    intro P
    obtain ⟨P', rfl⟩ := Sylow.mapSurjective_surjective hf p P
    have := hcycG P'
    rw [Sylow.coe_mapSurjective]
    refine isCyclic_of_surjective
      (((f.comp (P' : Subgroup G).subtype).codRestrict ((P' : Subgroup G).map f)
        fun x => ⟨x, x.2, rfl⟩) : ↥(P' : Subgroup G) →* ↥((P' : Subgroup G).map f)) ?_
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have h1 := CFSG.QuasithinUnique.Id2519.pRank_le_one_of_sylow_cyclic hp hcycQ
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  omega

theorem pRank_pCore_quotient {G : Type} [Group G] [Finite G] (L : Subgroup G) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.pRank r (↥L ⧸ CFSG.pCore 2 ↥L) = CFSG.pRank r ↥L := by
  have : Fact r.Prime := ⟨hr⟩
  have hN : ¬ r ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    rw [hk]
    intro h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥L) hN

theorem oddRankLeOne_of_a38Types
    {X : Type} [Group X] [Finite X] (hA : A38Types X) :
    OddRankLeOne X := by
  intro r hr hr2
  have := CFSG.QuasithinUnique.Id2519.lemma122Rank X hA r hr hr2
  rwa [← CFSG.SectionRank.pRank_eq_open_pRank_top] at this

end Rank

section Cases

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_isBadLieChar2
    (h : IsBadLieChar2 ↥L) (hL : OddRankLeOne ↥L) : False := by
  rcases h with ⟨f, ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, -, hm⟩⟩ | hT | h5 | hU
  · have := oddRankOneChevalley ↥L hL .G2 2 f (by simp [chevalleyExceptionalTags]) hm
    simp at this
  · obtain ⟨-, -, hf1⟩ := oddRankOneChevalley ↥L hL .trialityD4 2 f
      (by simp [chevalleyExceptionalTags]) hm
    subst hf1
    have h2 := trialityTwoHasRankTwo ↥L hm
    have h3 := hL 3 Nat.prime_three (by norm_num)
    omega
  · exact oddRankOneReeTits ↥L hL .twistedF4 2 f (by simp [reeTitsTags]) hm
  · exact oddRankOneReeTits ↥L hL .Tits 2 1 (by simp [reeTitsTags]) hT
  · rcases CFSG.QuasithinUnique.Vol2Native.EvenWit.oddRankOneEvenClassical ↥L hL .PSL 5 1 h5 with
      ⟨-, h2, -⟩ | ⟨-, h3, -⟩ <;> omega
  · have := oddRankOneOddClassical ↥L hL 3 Nat.prime_three (by norm_num) .PSU 3 1 hU
    simp at this

theorem false_of_psl_four_two (h : StatedClassicalModel ↥L .PSL 4 2 1) (hL : OddRankLeOne ↥L) :
    False := by
  rcases CFSG.QuasithinUnique.Vol2Native.EvenWit.oddRankOneEvenClassical ↥L hL .PSL 4 1 h with
    ⟨-, h2, -⟩ | ⟨-, h3, -⟩ <;> omega

theorem false_of_psl_three_three (h : StatedClassicalModel ↥L .PSL 3 3 1) (hL : OddRankLeOne ↥L) :
    False := by
  obtain ⟨-, h2, -⟩ := oddRankOneOddClassical ↥L hL 3 Nat.prime_three (by norm_num) .PSL 3 1 h
  omega

theorem false_of_centralQuotientAlt_seven (h : CentralQuotientAlt L 7) (hL : OddRankLeOne ↥L) :
    False := by
  obtain ⟨e⟩ := h
  have h2 := two_le_pRank_three_of_alternating (by norm_num) e
  have h3 := two_le_pRank_of_surjective Nat.prime_three (by norm_num)
    (QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _) h2
  have h4 := hL 3 Nat.prime_three (by norm_num)
  omega

end Cases

theorem l239NotRankOne
    : L239NotRankOne := by
  intro G _ _ L _ hL hA
  have hX : OddRankLeOne (↥L ⧸ CFSG.pCore 2 ↥L) := oddRankLeOne_of_a38Types hA
  have hLr : OddRankLeOne ↥L := fun r hr hr2 => by
    rw [← pRank_pCore_quotient L hr hr2]
    exact hX r hr hr2
  rcases hL with h | h | h | h | h | h | h
  · exact false_of_isBadLieChar2 h hLr
  · have := oddRankOneChevalley _ hX .G2 2 2 (by simp [chevalleyExceptionalTags]) h
    simp at this
  · exact l239NotRankOne_sporadic L (Or.inl h) hA
  · exact l239NotRankOne_sporadic L (Or.inr h) hA
  · exact false_of_psl_four_two h hLr
  · exact false_of_centralQuotientAlt_seven h hLr
  · exact false_of_psl_three_three h hLr

end CFSG.QuasithinUnique.Vol2Native.L239
