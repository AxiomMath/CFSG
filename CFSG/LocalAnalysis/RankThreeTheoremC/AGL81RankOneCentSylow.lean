module

import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111WeakCore
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenParabolicOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneElevenEleven
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CfgData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_of_elemAbelian {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hS : Setting G)
    (hd : AGL81CfgData p P M H Q K) {C E T : Subgroup G} (hET : E ≤ T) (hTC : T ≤ C ⊓ M)
    (hT : IsPGroup p T) (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) :
    ∃ B : Subgroup G, T ≤ B ∧ B ≤ C ⊓ M ∧ IsPGroup p B ∧
      (∃ S : Sylow p ↥C, (S : Subgroup ↥C).map C.subtype = B) ∧
      Open.pRank p B = 3 ∧ Open.pRank p C = 3 := by
  have hp : p.Prime := Fact.out
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have h3 : 3 ≤ Open.pRank p (C ⊓ M) :=
    CFSG.SectionRank.le_pRank hp.one_lt (hET.trans hTC) hE hEc
  obtain ⟨W, hW⟩ := (hT.comap_subtype (K := C ⊓ M)).exists_le_sylow
  obtain ⟨S, hSW⟩ := isSylow_of_inter hesc.weakCore_le h3 W
  set B : Subgroup G := (W : Subgroup ↥(C ⊓ M)).map (C ⊓ M).subtype with hBdef
  have hTB : T ≤ B := fun t ht => ⟨⟨t, hTC ht⟩, hW ht, rfl⟩
  have hBCM : B ≤ C ⊓ M := Subgroup.map_subtype_le _
  have hBp : IsPGroup p B := W.isPGroup'.map _
  have hB3 : Open.pRank p B = 3 := le_antisymm
    ((CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp (hBCM.trans inf_le_right)).trans
      (pRank_le_three_of_escape hS hd))
    (CFSG.SectionRank.le_pRank hp.one_lt (hET.trans hTB) hE hEc)
  have hBC : Open.pRank p B = Open.pRank p C := by
    refine pRank_eq_of_sylow hp (hBCM.trans inf_le_left) hBp ?_
    rw [← hSW]
    change ¬ p ∣ (((S : Subgroup ↥C).map C.subtype).comap C.subtype).index
    rw [Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    exact S.not_dvd_index
  exact ⟨B, hTB, hBCM, hBp, ⟨S, hSW⟩, hB3, hBC ▸ hB3⟩

theorem mem_d1PlusCore_of_central {p : ℕ} {Y : Subgroup G} {x : G} (hxY : x ∈ Y)
    (hx : ∀ y ∈ Y, x * y = y * x) (K : Subgroup (Y ⧸ primeComplementCore (G := Y) p)) :
    x ∈ d1PlusCore p Y K := by
  refine ⟨⟨x, hxY⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  intro h _
  induction h using QuotientGroup.induction_on with
  | H c =>
    change (QuotientGroup.mk c : Y ⧸ primeComplementCore (G := Y) p) * QuotientGroup.mk _ =
      QuotientGroup.mk _ * QuotientGroup.mk c
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hx c c.2).symm

theorem mem_zpowers_of_pRank_le_one {p : ℕ} (hp : p.Prime) {X : Subgroup G}
    (hX : Open.pRank p X ≤ 1) {b u : G} (hbX : b ∈ X) (hbo : orderOf b = p)
    (hbc : ∀ x ∈ X, b * x = x * b) (huX : u ∈ X) (huo : orderOf u = p) :
    u ∈ Subgroup.zpowers b := by
  by_contra hu
  obtain ⟨hE, hEc⟩ := RankOne.elemAbelian_pair hp hbo huo hu (hbc u huX)
  have hle : Subgroup.zpowers b ⊔ Subgroup.zpowers u ≤ X :=
    sup_le (Subgroup.zpowers_le.mpr hbX) (Subgroup.zpowers_le.mpr huX)
  have := CFSG.SectionRank.le_pRank hp.one_lt hle hE hEc
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
