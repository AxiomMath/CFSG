module

public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Lemma42
public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Sylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9B
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9CoverAux
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLinesPlanes

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.P5

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankFourTheoremC CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G}
  {M : Subgroup G} {x : G}

theorem gen49q_others_p (hp5 : 5 ≤ p) (hK : P5KFacts) (hG : P5Global G) (hloc : D1Local p P M)
    (hType : PTypeHyp p P M) (h : CFSG.LocalAnalysis.RankFourTheoremC.IsPPoint p P M x)
    (hS : PtShape p P x) {R H : Subgroup G} (hRP : R ≤ (P : Subgroup G)) (hRe : IsElemAbelian p R)
    (hxH : x ∈ H)
    (hOM : primeComplementCore (G := H) p ≤ (H ⊓ M).subgroupOf H)
    (hxo' : orderOf (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hxH⟩) = p) :
    ∀ a ∈ (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)), a ≠ 1 →
      zpowers a ≠ zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hxH⟩) →
      centralizer ({a} : Set (H ⧸ primeComplementCore (G := H) p)) ≤
          ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ∧
        normalizer ((zpowers a : Subgroup (H ⧸ primeComplementCore (G := H) p)) :
            Set (H ⧸ primeComplementCore (G := H) p)) ≤
          ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
  have hpr : p.Prime := hp.out
  rintro _ ⟨r, hr, rfl⟩ hr1 hrx
  have hrR : (r : G) ∈ R := hr
  have hrP : (r : G) ∈ (P : Subgroup G) := hRP hrR
  have hr1' : (r : G) ≠ 1 := fun hh => hr1 (by rw [show r = 1 from Subtype.ext hh, map_one])
  have hrp : (r : G) ^ p = 1 := hRe.2 _ hrR
  have hrx' : (r : G) ∉ zpowers x := by
    intro hmem
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
    have hrk : r = (⟨x, hxH⟩ : H) ^ k := Subtype.ext (by rw [← hk]; rfl)
    have hmem' : QuotientGroup.mk' (primeComplementCore (G := H) p) r ∈
        zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hxH⟩) := by
      rw [hrk, map_zpow]
      exact zpow_mem (mem_zpowers _) k
    exact hrx (CFSG.LocalAnalysis.RankThreeTheoremC.eq_zpowers_of_card_eq_prime
      (by rw [Nat.card_zpowers, hxo']) hmem' hr1).symm
  have hCM : centralizer ({(r : G)} : Set G) ≤ M :=
    centralizer_le_of_not_mem_zpowers_p hp5 hK hG hloc hType h hrP hrp hrx'
  have hPC : (P : Subgroup G) ≤ centralizer ({(r : G)} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hS.abelian.is_comm.comm ⟨g, hg⟩ ⟨r, hrP⟩))
  have hNM : normalizer ((zpowers (r : G) : Subgroup G) : Set G) ≤ M :=
    normalizer_zpowers_le_of_centralizer_le hG.fc hloc hCM
      (by rw [inf_of_le_left hPC]; have := four_le_pRank_sylow hloc.beta P; omega)
  have hro : orderOf r = p := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime hrp hr1'
  refine ⟨(centralizer_mk_le_map hpr hro).trans (Subgroup.map_mono fun c hc => ?_), ?_⟩
  · exact Subgroup.mem_subgroupOf.mpr ⟨c.2, hCM (mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc)))⟩
  · rw [← MonoidHom.map_zpowers]
    refine gen49q_normalizer_map_mk_le hpr hOM (D := zpowers r)
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hro, pow_one])) ?_
    rw [MonoidHom.map_zpowers]
    exact hNM

theorem gen49q_hyp_p (hp5 : 5 ≤ p) (hK : P5KFacts) (hG : P5Global G) (hloc : D1Local p P M)
    (hType : PTypeHyp p P M) (h : CFSG.LocalAnalysis.RankFourTheoremC.IsPPoint p P M x)
    (hS : PtShape p P x)
    {R H R' : Subgroup G} (hRP : R ≤ (P : Subgroup G)) (hRe : IsElemAbelian p R)
    (hRc : Nat.card R = p ^ 2) (hxR : x ∈ R) (hHtop : H ≠ ⊤) (hRH : R ≤ H)
    (hrk : CFSG.Open.pRank p H ≤ 2)
    (hOM : primeComplementCore (G := H) p ≤ (H ⊓ M).subgroupOf H)
    (hR'H : CFSG.ABGLocalTools.IsSylowOf p R' H) (hRR' : R ≤ R') (hR'M : R' ≤ M) :
    Gen49BHyp p ((R'.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
      ((R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
      (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hRH hxR⟩) := by
  have hpr : p.Prime := hp.out
  have hxH : x ∈ H := hRH hxR
  set O : Subgroup H := primeComplementCore (G := H) p
  have hPM : (P : Subgroup G) ≤ M := sylow_le_of_core hloc
  have hRp : IsPGroup p R := elementary_isPGroup p R hRe
  have hxo : orderOf (⟨x, hxH⟩ : H) = p := by
    rw [Subgroup.orderOf_mk]
    exact h.elem.2.1
  have hxo' : orderOf (QuotientGroup.mk' O ⟨x, hxH⟩) = p :=
    orderOf_mk_of_coprime hpr O (primeComplementCore_coprime p) hxo
  have hab := isMulCommutative_sylow_quotient (N := H) fun _ hQ =>
    PPointP.isMulCommutative_of_isPGroup_p hS.abelian hQ
  obtain ⟨T, hT⟩ := hR'H.exists_sylow_eq_subgroupOf
  set Q : Sylow p (H ⧸ O) := T.mapSurjective (QuotientGroup.mk'_surjective O) with hQdef
  have hQS : (Q : Subgroup (H ⧸ O)) = (R'.subgroupOf H).map (QuotientGroup.mk' O) := by
    rw [hQdef, Sylow.coe_mapSurjective, hT]
  have hxS : QuotientGroup.mk' O ⟨x, hxH⟩ ∈ (R'.subgroupOf H).map (QuotientGroup.mk' O) :=
    ⟨⟨x, hxH⟩, hRR' hxR, rfl⟩
  have hN₁ : normalizer (R' : Set G) ≤ M := normalizer_le_of_two_le_pRank hG.fc hloc
    hR'H.isPGroup hR'M (le_pRank_of_elemAbelian_card hRR' hRe hRc)
  have hN₂ : normalizer (R : Set G) ≤ M := normalizer_le_of_two_le_pRank hG.fc hloc
    hRp (hRP.trans hPM) (le_pRank_of_elemAbelian_card le_rfl hRe hRc)
  exact
    { ne_two := by omega
      core_eq_bot := primeComplementCore_quotient_eq_bot p
      catalog := (catalogSimpleSections_of_isKProper hG.glob.kProper H hHtop).quotient O
      sylow := isSylowOf_top_map_mk hR'H
      abelian := by
        rw [← hQS]
        exact hab Q
      le_sylow := Subgroup.map_mono (Subgroup.subgroupOf_mono H hRR')
      elemAbelian := gen49q_isElemAbelian_map _ (isElemAbelian_subgroupOf hRe H)
      card_eq := by
        rw [card_map_mk_of_isPGroup hpr O (primeComplementCore_coprime p)
          (show IsPGroup p (R.subgroupOf H) from hRp.comap_subtype),
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv]
        exact hRc
      pRank_le := gen49q_pRank_top_quotient_le hpr hrk
      mem := ⟨⟨x, hxH⟩, hxR, rfl⟩
      ne_one := fun hh => by
        rw [hh, orderOf_one] at hxo'
        exact hpr.one_lt.ne hxo'
      weakClosed := fun g hg => weaklyClosed_map_mk hxo hab
        (fun Q' hxQ' g' hg' => PPointP.weakClosed_sylow_p hS.weak Q' hxQ' g' hg') Q
        (hQS ▸ hxS) g (by rw [hQS]; exact hg)
      normalizer_S := gen49q_normalizer_map_mk_le hpr hOM
        (show IsPGroup p (R'.subgroupOf H) from hR'H.isPGroup.comap_subtype)
        (by rw [Subgroup.map_subgroupOf_eq_of_le hR'H.le]; exact hN₁)
      normalizer_R := gen49q_normalizer_map_mk_le hpr hOM
        (show IsPGroup p (R.subgroupOf H) from hRp.comap_subtype)
        (by rw [Subgroup.map_subgroupOf_eq_of_le hRH]; exact hN₂)
      others := gen49q_others_p hp5 hK hG hloc hType h hS hRP hRe hxH hOM hxo' }

theorem gen49Cover_p (hp5 : 5 ≤ p) (hK : P5KFacts) (hG : P5Global G) (hloc : D1Local p P M)
    (hType : PTypeHyp p P M) (h : CFSG.LocalAnalysis.RankFourTheoremC.IsPPoint p P M x)
    {A : Subgroup G} (hAP : A ≤ (P : Subgroup G)) (hAe : IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) (hxA : x ∈ A) : Gen49Cover G p M x A := by
  have hS : PtShape p P x := shape_p hp5 hK hG hloc hType h
  intro H hHtop hRH hrk hHM hOM'
  have hOM := gen49q_core_le_subgroupOf_inf hOM'
  obtain ⟨R', hR'H, hRR', hR'M⟩ := exists_sylow_through_plane_p hG hloc hAP hAe hAc hRH
  rcases gl83Generic4_9B_holds hK.hInn hK.hWC
      (gen49q_hyp_p hp5 hK hG hloc hType h hS hAP hAe hAc hxA hHtop hRH hrk hOM hR'H hRR' hR'M)
    with hΓ | ⟨K, hKn, hKC, hKΓ⟩
  · exact absurd hΓ (map_mk_inf_ne_top hOM hHM)
  · exact gen49q_extract (hRH hxA) hKn hKC hKΓ

end CFSG.LocalAnalysis.RankFourTheoremC.P5
