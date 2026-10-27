module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveKer
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.SevenHull
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.SevenHullThirteen
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTwelveThirteenKerSetup
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTwelveThirteenKerFrame
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTwelveThirteenKerQuot
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenKStar
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

@[expose] def NineTwelveThirteenKer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G),
    NineSettingGen G M 13 Q H E 2 → H ∈ H2Fam M Q → 13 ∉ sigmaM G M → pLayerIn 13 H ≤ M →
    ∀ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 R (relPPrimeCore 13 H) →
      kSub 13 M H = (kSub 13 M H ⊓ Subgroup.centralizer (R : Set G)) ⊔ kerIn M (kSub 13 M H)

namespace NineSettingGen

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

theorem kSub_le_oPPrimeHull_sup_kerIn_of_quotient (h : NineSettingGen G M p Q H E k) {d : ℕ}
    [Fact d.Prime] (F : Subgroup (StarGroup p H)) [F.Normal] (hFM : F ≤ starImg p H M)
    (hgen : (kStar p M H).map (QuotientGroup.mk' F) ≤
      oPPrimeHull d ((kStar p M H).map (QuotientGroup.mk' F))) :
    kSub p M H ≤ oPPrimeHull d (kSub p M H) ⊔ kerIn M (kSub p M H) := by
  let φ : ↥(kSub p M H) →* StarGroup p H ⧸ F :=
    (QuotientGroup.mk' F).comp ((QuotientGroup.mk' (primeComplementCore (G := ↥H) p)).comp
      (Subgroup.inclusion (kSub_le p M H)))
  have hrange : φ.range = (kStar p M H).map (QuotientGroup.mk' F) := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  refine le_oPPrimeHull_sup_of_hom φ (fun a ha => h.mem_kerIn_of_mk_mem (kSub_le p M H)
    inferInstance hFM a ((QuotientGroup.eq_one_iff (N := F)
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
        (Subgroup.inclusion (kSub_le p M H) a))).mp ha)) ?_
  rw [hrange]
  exact hgen

theorem kStar_map_le_oPPrimeHull_seven_of_layer_eq_bot (h910 : NineTenGen)
    (h : NineSettingGen G M 13 Q H E 2) (hH2 : H ∈ H2Fam M Q) (hp : 13 ∉ sigmaM G M)
    (hL0 : pLayerIn 13 H = ⊥) {F : Subgroup (StarGroup 13 H)} [F.Normal]
    (hOF : CFSG.pCore 13 (StarGroup 13 H) ≤ F) :
    (kStar 13 M H).map (QuotientGroup.mk' F) ≤
      oPPrimeHull 7 ((kStar 13 M H).map (QuotientGroup.mk' F)) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hLM : pLayerIn 13 H ≤ M := by
    rw [hL0]
    exact bot_le
  obtain ⟨hlist, hcard⟩ := (h910 G M Q H E 13 h hH2 hp).2.2 hL0
  exact map_le_oPPrimeHull_of_quotient F (kStar 13 M H) (CFSG.pCore 13 ↥(kStar 13 M H))
    ((map_le_pCore_of_isPGroup (p := 13) (T := CFSG.pCore 13 ↥(kStar 13 M H))
      (kStar_normal_of_le hLM) CFSG.pCore_normal CFSG.pCore_isPGroup).trans hOF)
    (oPPrimeHull_seven_of_sixThreeOneList_thirteen hlist hcard)

theorem kStar_map_le_oPPrimeHull_seven_of_layer_ne_bot (h910 : NineTenGen)
    (h : NineSettingGen G M 13 Q H E 2) (hH2 : H ∈ H2Fam M Q) (hp : 13 ∉ sigmaM G M)
    (hL0 : pLayerIn 13 H ≠ ⊥) (hL : pLayerIn 13 H ≤ M) {F : Subgroup (StarGroup 13 H)}
    [F.Normal] (hLF : starImg 13 H (pLayerIn 13 H) ≤ F)
    (hOF : CFSG.pCore 13 (StarGroup 13 H) ≤ F) :
    (kStar 13 M H).map (QuotientGroup.mk' F) ≤
      oPPrimeHull 7 ((kStar 13 M H).map (QuotientGroup.mk' F)) := by
  have h13 : Nat.Prime 13 := by norm_num
  rcases (h910 G M Q H E 13 h hH2 hp).2.1 hL0 hL with
    ⟨h3, -⟩ | ⟨-, -, -, hHull, hExt⟩ | ⟨h3, -⟩
  · exact absurd h3 (by norm_num)
  · obtain ⟨W, hWn, hW, hV, -⟩ := hExt
    have := hWn
    have hVn : (oPPrimeHull 13 (cStarL 13 H)).Normal :=
      oPPrimeHull_normal 13 (cStarL_normal_of_prime h13 H)
    exact Nonempty.elim hV fun e => map_le_oPPrimeHull_seven_of_sl2_thirteen F
      (kStar_normal_of_le hL) (kStar_le_oPPrimeHull h13 hL)
      ((kStar_le_oPPrimeHull_top h13 hL).trans hHull.le) hLF W
      ((map_le_pCore_of_isPGroup hVn hWn (isPGroup_of_isHomocyclicRank2 hW)).trans hOF) e
  · exact absurd h3 (by norm_num)

theorem kSub_le_oPPrimeHull_seven_sup_kerIn (h910 : NineTenGen) (h991 : NineNineOneInput)
    (h : NineSettingGen G M 13 Q H E 2) (hH2 : H ∈ H2Fam M Q) (hp : 13 ∉ sigmaM G M)
    (hL : pLayerIn 13 H ≤ M) :
    kSub 13 M H ≤ oPPrimeHull 7 (kSub 13 M H) ⊔ kerIn M (kSub 13 M H) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : (starImg 13 H (pLayerIn 13 H)).Normal := starImg_pLayerIn_normal (by norm_num) H
  have hFM : starImg 13 H (pLayerIn 13 H) ⊔ CFSG.pCore 13 (StarGroup 13 H) ≤ starImg 13 H M :=
    sup_le (Subgroup.map_mono fun x hx => hL hx)
      (h.pCore_star_le_starImg hH2 hp (h991 G M Q H E 13 h hp))
  refine h.kSub_le_oPPrimeHull_sup_kerIn_of_quotient _ hFM ?_
  by_cases hL0 : pLayerIn 13 H = ⊥
  · exact h.kStar_map_le_oPPrimeHull_seven_of_layer_eq_bot h910 hH2 hp hL0 le_sup_right
  · exact h.kStar_map_le_oPPrimeHull_seven_of_layer_ne_bot h910 hH2 hp hL0 hL le_sup_left
      le_sup_right

end NineSettingGen

theorem nineTwelveThirteenKer_of_inputs (h910 : NineTenGen) (h991 : NineNineOneInput) :
    NineTwelveThirteenKer := by
  intro G _ _ M Q H E h hH2 hp hL R hR
  apply le_antisymm
  · calc kSub 13 M H ≤ oPPrimeHull 7 (kSub 13 M H) ⊔ kerIn M (kSub 13 M H) :=
          h.kSub_le_oPPrimeHull_seven_sup_kerIn h910 h991 hH2 hp hL
      _ ≤ ((kSub 13 M H ⊓ centralizer (R : Set G)) ⊔ (kSub 13 M H ⊓ relPPrimeCore 13 H)) ⊔
          kerIn M (kSub 13 M H) := sup_le_sup_right (h.oPPrimeHull_seven_kSub_le hL hR) _
      _ ≤ (kSub 13 M H ⊓ centralizer (R : Set G)) ⊔ kerIn M (kSub 13 M H) :=
          sup_le (sup_le le_sup_left (le_sup_of_le_right
            (inf_le_kerIn_of_normal (X := relPPrimeCore 13 H) (kSub_le 13 M H)
              (sSup_le fun _ hN => hN.1)
              (RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal h.prime H)
              h.relPPrimeCore_le))) le_sup_right
  · exact sup_le inf_le_left fun x hx => (mem_kerIn_iff_forall_conj.mp hx).1

theorem nineTwelveThirteenRankThree_of_ker (h : NineTwelveThirteenKer) :
    NineTwelveThirteenRankThree :=
  fun G _ _ M Q H E hs hH hp hL _ R hR _ => h G M Q H E hs hH hp hL R hR

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
