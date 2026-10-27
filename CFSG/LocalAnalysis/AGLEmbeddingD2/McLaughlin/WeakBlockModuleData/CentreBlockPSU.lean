module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PSURank3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CentreBlockTypeTwo

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData


theorem kFactCentreBlockPLRankPSU_proved (hG : GriessAllModelsStatement) :
    KFactCentreBlockPLRankPSU := by
  intro G _ _ M S L hL h2 hsolv hSyl hZP hZ hpsu
  have h3p : Nat.Prime 3 := Nat.prime_three
  obtain ⟨hY, hpar, hS⟩ := h2
  have h2' : NineThreeTwo M S L := ⟨hY, hpar, hS⟩
  have hnot : ¬ IsSylowTwoOf (pCoreOf 2 (barM M (Subgroup.normalizer (S : Set G) ⊓ L)))
      (barM M L) := hS ▸ hSyl h2'
  obtain ⟨T, hT, hNJ, hJne, hJperf⟩ := exists_overgroup_quotient_map _ _ hpar hnot hsolv
  obtain ⟨d, ⟨r, q, hd, hq, h3r⟩, ⟨e0⟩⟩ := hpsu
  obtain ⟨d1, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨hp, hqe⟩ := primePower_card_two' hq
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hr3 : 3 ≤ r := by
    have h2r := hrange.1
    by_contra hlt
    have : r = 2 := by omega
    have := hrange.2 this
    omega
  have hn6 : 6 ≤ r + 1 := by omega
  have hperfX : commutator ↥(barM M L) = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr (barM_perfect hL.le hL.perfect))
  have hcard := card_inf_centralizer_eq_card_center (barM M L)
  have h3 : 3 ∣ Nat.card (Subgroup.center ↥(barM M L)) := by rw [← hcard]; exact hZ
  have hperfY : Group.IsPerfect (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := by
    haveI : Group.IsPerfect ↥(barM M L) := ⟨hperfX⟩
    exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center ↥(barM M L)))
      (QuotientGroup.mk'_surjective _)
  have hYc := center_eq_bot_of_mulEquiv_lie hperfY e0
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e0
  rw [hp, hqe] at hm
  obtain ⟨-, F, hFf, hFfin, hF, ⟨e⟩⟩ := hm
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have hPL : barM M (Subgroup.normalizer (S : Set G) ⊓ L) ≤ barM M L := barM_mono inf_le_right
  have hZP' : Subgroup.center ↥(barM M L) ≤
      (barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM M L) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    apply hZP
    refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    have := Subgroup.mem_center_iff.mp hx ⟨h, hh⟩
    exact congrArg Subtype.val this
  have hrank := three_le_pRank_of_psu_extension hG hF hn6 h3r ⟨hperfX⟩ _ hZP' h3 e hYc hT hNJ hJne
    hJperf
  have hmap := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 h3p
    (barM M L).subtype (barM M L).subtype_injective
    ((barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM M L))
  rw [Subgroup.map_subgroupOf_eq_of_le hPL] at hmap
  omega

theorem kFactCentreBlockPLRank_proved (hG : GriessAllModelsStatement) :
    KFactCentreBlockPLRank :=
  kFactCentreBlockPLRank_of_psu hG (kFactCentreBlockPLRankPSU_proved hG)

end CFSG.AGLEmbeddingD2.McLaughlin
