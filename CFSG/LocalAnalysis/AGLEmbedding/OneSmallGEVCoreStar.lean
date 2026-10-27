module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoverDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVStar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVStarIa
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsAlphaWeakCentral
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoverFree
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVComponents
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIdent
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallConfig
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.exists_compI_star (hSch : KFactCatalogSchreier) (hK1 : KFactOneLie)
    (hU : KFactUnitarySylowStructure) (hβ : KFactBeta) (hα : KFactAlphaW) (h2 : D1CaseTwo)
    (h3 : D1CaseThree) (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z)
    (hR : Nat.card R ≤ p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p)))
    {Hs : Subgroup G} (hHs : GLBIsMaxTwoLocal Hs)
    (hVHs : Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ Hs) :
    ∃ (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs)
      (Rbars : Sylow p (Hs ⧸ primeComplementCore (G := Hs) p))
      (Ks : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)),
      D1CompI p P M Hs R Rbars Ks ∧ d1StarElt p hCHs ∈ Subgroup.centralizer (Ks : Set _) := by
  obtain ⟨hCHs, -, hext⟩ := hd.extremal_of_normalizer_le hz hHs hVHs
  have hcon : ¬ HasPrimeConstraint (G := Hs) p := fun hc =>
    d1ConstrainedCase_of_kFactsW hβ hα G hd.cfg.glob p P M hd.cfg.loc Hs R hext hc
  obtain ⟨Rbars, hcfg⟩ := hext.exists_componentConfig hd.cfg.glob hd.cfg.loc hcon hd.cfg.ind
  by_cases hallc : ∀ L : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p), IsComponentOf L ⊤ →
      IsCyclic ((Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)) ⊓ L :
        Subgroup (Hs ⧸ primeComplementCore (G := Hs) p))
  · exact (h2 G p P M Hs R Rbars hcfg hallc).elim
  push Not at hallc
  obtain ⟨Ks, hKs, hnc⟩ := hallc
  rcases hcfg.red.rankOne_or_center hKs hnc with
    ⟨zs, hzsR, hzsK, hzsp, hzsc, -, -, -, hZ⟩ | hcent
  · have hds : D1CompI p P M Hs R Rbars Ks := ⟨hcfg, hKs, hZ, hnc, ⟨zs, hzsR, hzsK, hzsp, hzsc⟩⟩
    exact ⟨hCHs, Rbars, Ks, hds,
      D1OneSmallData.mem_centralizer_star_of_card hSch hK1 hU hd hz hR hCHs hds⟩
  · exact (h3 _ p P M Hs R Rbars hcfg Ks hKs
      (fun L hL => hcfg.red.eq_of_forall_mem_center hKs hL hcent) hnc hcent).elim

theorem D1OneSmallData.star_smallData_of_card (hSch : KFactCatalogSchreier) (hK1 : KFactOneLie)
    (hU : KFactUnitarySylowStructure) (hβ : KFactBeta) (hα : KFactAlphaW) (h2 : D1CaseTwo)
    (h3 : D1CaseThree) (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z)
    (hR : Nat.card R ≤ p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p)))
    (hIso : D1CzIso p z K) : D1GEVStarSmall p P M R z K := by
  intro Hs hHs hVHs
  obtain ⟨hCHs, Rbars, Ks, hds, hzsC⟩ :=
    D1OneSmallData.exists_compI_star hSch hK1 hU hβ hα h2 h3 hd hz hR hHs hVHs
  obtain ⟨eL⟩ := hd.iso_of_centralized_component hz hIso hCHs hds.cfg hds.comp hzsC
  obtain ⟨hds', hzs'⟩ := hd.smallData_of_component_iso hz hCHs hds.cfg hds.comp hzsC eL
  exact ⟨Rbars, Ks, hds', hzs', ⟨eL⟩⟩

omit [Finite G] in
theorem card_inf_eq_of_mulEquiv [Finite G] {Hs : Subgroup G}
    {Rbars : Sylow p (Hs ⧸ primeComplementCore (G := Hs) p)}
    {Ls : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)}
    (hd : D1OneSmallData p P M H R Rbar K) (hds : D1OneSmallData p P M Hs R Rbars Ls)
    (e : Ls ≃* K) :
    Nat.card ((Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)) ⊓ Ls :
      Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)) =
      Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
  have : Fact p.Prime := ⟨hd.cfg.red.prime⟩
  obtain ⟨T₁, hT₁, -⟩ := hd.exists_sylow
  obtain ⟨Ts, hTs, -⟩ := hds.exists_sylow
  rw [← hT₁, ← hTs, Subgroup.card_map_of_injective K.subtype_injective,
    Subgroup.card_map_of_injective Ls.subtype_injective, Sylow.card_eq_multiplicity,
    Sylow.card_eq_multiplicity, Nat.card_congr e.toEquiv]

theorem D1OneSmallData.not_outerR_of_card (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z)
    (hR : Nat.card R ≤ p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p))) :
    ¬ D1SmallOuterR p H Rbar K := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set zb := π ⟨z, hz.2.2.1⟩ with hzb
  set C := Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) with hC
  have hzbR : zb ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    rw [hd.cfg.rbar]
    exact ⟨⟨z, hz.2.2.1⟩, hz.1, rfl⟩
  have hzbC : zb ∈ C := hz.2.2.2
  have hzbp : orderOf zb = p := orderOf_mk_of_coprime hp _ (primeComplementCore_coprime p)
    (by rw [← Subgroup.orderOf_coe]; exact hz.2.1)
  have hKC : K ⊓ C = ⊥ := inf_centralizer_eq_bot_of_center hd.center
  have hdisj : ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ⊓
      Subgroup.zpowers zb = ⊥ := by
    rw [eq_bot_iff, ← hKC]
    exact le_inf (inf_le_left.trans inf_le_right)
      (inf_le_right.trans (Subgroup.zpowers_le.mpr hzbC))
  have hle : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K ⊔ Subgroup.zpowers zb ≤
      Rbar := sup_le inf_le_left (Subgroup.zpowers_le.mpr hzbR)
  have hRbar : Nat.card (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) = Nat.card R := by
    rw [hd.cfg.rbar, card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p)
      (T := R.subgroupOf H) hd.cfg.ext.isPGroup.comap_subtype]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hd.cfg.ext.le_H).toEquiv
  have heq : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K ⊔
      Subgroup.zpowers zb = Rbar := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have h1 := mul_card_le_of_inf_eq_bot (le_sup_left :
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K ≤
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K ⊔ Subgroup.zpowers zb)
      le_sup_right hdisj
    rw [Nat.card_zpowers, hzbp] at h1
    rw [hRbar]
    calc Nat.card R ≤ p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
          Subgroup (H ⧸ primeComplementCore (G := H) p)) := hR
      _ = Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
          Subgroup (H ⧸ primeComplementCore (G := H) p)) * p := mul_comm _ _
      _ ≤ _ := h1
  intro hout
  apply hout
  rw [← heq]
  exact sup_le (inf_le_right.trans le_sup_left)
    ((Subgroup.zpowers_le.mpr hzbC).trans le_sup_right)

end CFSG.AGLEmbedding
