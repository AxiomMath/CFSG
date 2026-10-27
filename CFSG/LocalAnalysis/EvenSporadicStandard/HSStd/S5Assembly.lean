module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FactsHS
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Ind
public import CFSG.LocalAnalysis.OddStandard.AltStdFaithfulRank
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.OddStandard
  CFSG.EvenSporadicStandard.Induction
open CFSG.SignalizerFunctorTheorem (IsSectionOf)

theorem hsSection5_at (G : Type) [Group G] [Finite G] (L : Subgroup G)
    (hset : HSLemma21Setting G L) (h : HSMainHiS G) : False := by
  obtain ⟨hStd, hL, -, -, -⟩ := hset
  have hsimple : IsSimpleGroup G := hStd.simple
  have hnab := hStd.nonabelian
  have hLs : standardComponentIsStandard L := hStd.standard
  have hCeven : Even (Nat.card (centralizer (L : Set G))) := hLs.2.1
  have hGeven : Even (Nat.card G) :=
    even_iff_two_dvd.2 ((even_iff_two_dvd.1 hCeven).trans
      (Subgroup.card_subgroup_dvd_card (centralizer (L : Set G))))
  have hO : CFSG.oddCore G = ⊥ := by
    unfold CFSG.oddCore
    refine le_antisymm (sSup_le ?_) bot_le
    rintro N ⟨hN, hodd⟩
    rcases hsimple.eq_bot_or_eq_top_of_normal N with hb | ht
    · exact hb ▸ le_rfl
    · exfalso
      subst ht
      rw [Subgroup.card_top] at hodd
      exact (Nat.not_even_iff_odd.2 hodd) hGeven
  have hZ : center G = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (center G) with hb | ht
    · exact hb
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have : a ∈ center G := ht ▸ Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.1 this b).symm
  obtain ⟨S, hS⟩ := hStd.cyclicSylow
  have hrank : Open.pRank 2 (centralizer (L : Set G)) = 1 :=
    CFSG.OddStandard.AltStdFaithful.pRank_two_eq_one_of_isCyclic hCeven S hS
  have hbal : ∀ t : G, orderOf t = 2 → CFSG.oddCore (centralizer ({t} : Set G)) = ⊥ :=
    fun t ht => hStd.oddCore t ht
  obtain ⟨K₁, K₂, hK₁, -, hq₁, -, -, -⟩ := h hO L hLs hL hrank hbal
  have hLcard : Nat.card L = Nat.card (K₁ ⧸ center K₁) := card_eq_of_isSporadic hL hq₁
  rcases hK₁.eq_bot_or_top_of_isSimpleGroup hsimple with h1 | h1
  · subst h1
    have h2 : Nat.card (↥(⊥ : Subgroup G) ⧸ center ↥(⊥ : Subgroup G)) ∣
        Nat.card ↥(⊥ : Subgroup G) := Subgroup.card_quotient_dvd_card _
    rw [Subgroup.card_bot, Nat.dvd_one] at h2
    have hL1 : L = ⊥ := Subgroup.eq_bot_of_card_eq L (hLcard.trans h2)
    apply hLs.2.2.2.2 1
    rw [hL1]
    simp
  · subst h1
    have hZ' : center ↥(⊤ : Subgroup G) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      have hz' : (z : G) ∈ center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, Subgroup.mem_top g⟩)
      rw [hZ] at hz'
      exact Subgroup.mem_bot.1 hz'
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥(⊤ : Subgroup G))
    have hc1 : Nat.card (center ↥(⊤ : Subgroup G)) = 1 := by rw [hZ', Subgroup.card_bot]
    rw [hc1, mul_one, Subgroup.card_top] at hc
    have hLtop : L = ⊤ := Subgroup.eq_top_of_card_eq L (hLcard.trans hc.symm)
    have h3 : centralizer (L : Set G) = ⊥ := by
      rw [hLtop, Subgroup.coe_top, Subgroup.centralizer_univ]
      exact hZ
    rw [h3, Subgroup.card_bot] at hCeven
    exact (Nat.not_even_iff_odd.2 odd_one) hCeven

theorem hsLemma21Setting_of_stdHyp
    {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (h : StdHyp G L) (hL : IsSporadic L .HS) : HSLemma21Setting G L :=
  ⟨h, hL, fun S => h.card_sylow_eq_two_hs hsFacts hL S,
    fun _ ht ht2 => h.sylowFusion_hs hsFacts hL ht ht2,
    fun _ ht ht2 => h.relIndex_dvd_two_hs hsFacts hL ht ht2⟩

end CFSG.EvenSporadicStandard.HSStd
