module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Ctx
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9CoverAux
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9CoverSylow
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Setup2
public import CFSG.LocalAnalysis.AGLEmbedding.CentralComponent
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerOdd

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem gen49q_others [Fact p.Prime] (hG : Gen5Global G) (hl : Gen5Local G p P M x)
    {R H : Subgroup G} (hRP : R ≤ (P : Subgroup G)) (hRe : IsElemAbelian p R) (hxH : x ∈ H)
    (hOM : primeComplementCore (G := H) p ≤ (H ⊓ M).subgroupOf H)
    (hxo' : orderOf (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hxH⟩) = p) :
    ∀ a ∈ (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)), a ≠ 1 →
      zpowers a ≠ zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hxH⟩) →
      centralizer ({a} : Set (H ⧸ primeComplementCore (G := H) p)) ≤
          ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ∧
        normalizer ((zpowers a : Subgroup (H ⧸ primeComplementCore (G := H) p)) :
            Set (H ⧸ primeComplementCore (G := H) p)) ≤
          ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
  have hp := gen5_prime hl
  rintro _ ⟨r, hr, rfl⟩ hr1 hrx
  have hrR : (r : G) ∈ R := hr
  have hrP : (r : G) ∈ (P : Subgroup G) := hRP hrR
  have hr1' : (r : G) ≠ 1 := fun h => hr1 (by rw [show r = 1 from Subtype.ext h, map_one])
  have hrp : (r : G) ^ p = 1 := hRe.2 _ hrR
  obtain ⟨hU, -, hPab⟩ := generic_central_abelian hG.setting hG.d1 hG.u0 hG.layer hl.sigma
    hl.core hl.fail hl.larger hl.generic
  have hrx' : (r : G) ∉ zpowers x := by
    intro hmem
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
    have hrk : r = (⟨x, hxH⟩ : H) ^ k := Subtype.ext (by rw [← hk]; rfl)
    have hmem' : QuotientGroup.mk' (primeComplementCore (G := H) p) r ∈
        zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hxH⟩) := by
      rw [hrk, map_zpow]
      exact zpow_mem (mem_zpowers _) k
    exact hrx (eq_zpowers_of_card_eq_prime (by rw [Nat.card_zpowers, hxo']) hmem' hr1).symm
  have hCM : centralizer ({(r : G)} : Set G) ≤ M :=
    centralizer_le_of_not_mem_zpowers hG.setting hl.sigma hl.core hU hPab hrP hr1' hrp hrx'
  have hPC : (P : Subgroup G) ≤ centralizer ({(r : G)} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (hPab.is_comm.comm ⟨g, hg⟩ ⟨r, hrP⟩))
  have hNM : normalizer ((zpowers (r : G) : Subgroup G) : Set G) ≤ M :=
    normalizer_zpowers_le_of_centralizer_le hG.setting hG.u0 hl.sigma hl.core
      (by rw [inf_of_le_left hPC, (sylow_le_of_isCoreMaxLocal hG.setting hl.sigma hl.core).2]
          norm_num) hCM
  have hro : orderOf r = p := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime hrp hr1'
  refine ⟨(centralizer_mk_le_map hp hro).trans (Subgroup.map_mono fun c hc => ?_), ?_⟩
  · exact Subgroup.mem_subgroupOf.mpr ⟨c.2, hCM (mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc)))⟩
  · rw [← MonoidHom.map_zpowers]
    refine gen49q_normalizer_map_mk_le hp hOM (D := zpowers r)
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hro, pow_one])) ?_
    rw [MonoidHom.map_zpowers]
    exact hNM

theorem gen49q_hyp [Fact p.Prime] (hG : Gen5Global G) (hl : Gen5Local G p P M x)
    {R H R' : Subgroup G} (hRP : R ≤ (P : Subgroup G)) (hRe : IsElemAbelian p R)
    (hRc : Nat.card R = p ^ 2) (hxR : x ∈ R) (hHtop : H ≠ ⊤) (hRH : R ≤ H)
    (hrk : CFSG.Open.pRank p H ≤ 2)
    (hOM : primeComplementCore (G := H) p ≤ (H ⊓ M).subgroupOf H)
    (hR'H : IsSylowOf p R' H) (hRR' : R ≤ R') (hR'M : R' ≤ M) :
    Gen49BHyp p ((R'.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
      ((R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
      (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hRH hxR⟩) := by
  have hp := gen5_prime hl
  have hxH : x ∈ H := hRH hxR
  set O : Subgroup H := primeComplementCore (G := H) p
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hG.setting hl.sigma hl.core).1
  have hRp : IsPGroup p R := elementary_isPGroup p R hRe
  have hxo : orderOf (⟨x, hxH⟩ : H) = p := by
    obtain ⟨-, hx1, hxp, -, -⟩ := hl.generic.2.1
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hxp hx1
  have hxo' : orderOf (QuotientGroup.mk' O ⟨x, hxH⟩) = p :=
    orderOf_mk_of_coprime hp O (primeComplementCore_coprime p) hxo
  have hab := isMulCommutative_sylow_quotient (N := H) fun _ hQ => (gen5_pgroup hG hl hQ).1
  obtain ⟨T, hT⟩ := hR'H.exists_sylow_eq_subgroupOf
  set Q : Sylow p (H ⧸ O) := T.mapSurjective (QuotientGroup.mk'_surjective O) with hQdef
  have hQS : (Q : Subgroup (H ⧸ O)) = (R'.subgroupOf H).map (QuotientGroup.mk' O) := by
    rw [hQdef, Sylow.coe_mapSurjective, hT]
  have hxS : QuotientGroup.mk' O ⟨x, hxH⟩ ∈ (R'.subgroupOf H).map (QuotientGroup.mk' O) :=
    ⟨⟨x, hxH⟩, hRR' hxR, rfl⟩
  have hN₁ : normalizer (R' : Set G) ≤ M := normalizer_le_of_le_of_two_le_pRank hG.setting hG.u0
    hl.sigma hl.core hR'H.isPGroup hR'M (le_pRank_of_elemAbelian_card hRR' hRe hRc)
  have hN₂ : normalizer (R : Set G) ≤ M := normalizer_le_of_le_of_two_le_pRank hG.setting hG.u0
    hl.sigma hl.core hRp (hRP.trans hPM) (le_pRank_of_elemAbelian_card le_rfl hRe hRc)
  exact
    { ne_two := by have := gen5_five_le hG hl; omega
      core_eq_bot := primeComplementCore_quotient_eq_bot p
      catalog := (catalogSimpleSections_of_isKProper hG.setting.kProper H hHtop).quotient O
      sylow := isSylowOf_top_map_mk hR'H
      abelian := by
        rw [← hQS]
        exact hab Q
      le_sylow := Subgroup.map_mono (Subgroup.subgroupOf_mono H hRR')
      elemAbelian := gen49q_isElemAbelian_map _ (isElemAbelian_subgroupOf hRe H)
      card_eq := by
        rw [card_map_mk_of_isPGroup hp O (primeComplementCore_coprime p)
          (show IsPGroup p (R.subgroupOf H) from hRp.comap_subtype),
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv]
        exact hRc
      pRank_le := gen49q_pRank_top_quotient_le hp hrk
      mem := ⟨⟨x, hxH⟩, hxR, rfl⟩
      ne_one := fun h => by
        rw [h, orderOf_one] at hxo'
        exact hp.one_lt.ne hxo'
      weakClosed := fun g hg => weaklyClosed_map_mk hxo hab (gen5_weakly_closed hG hl) Q
        (hQS ▸ hxS) g (by rw [hQS]; exact hg)
      normalizer_S := gen49q_normalizer_map_mk_le hp hOM
        (show IsPGroup p (R'.subgroupOf H) from hR'H.isPGroup.comap_subtype)
        (by rw [Subgroup.map_subgroupOf_eq_of_le hR'H.le]; exact hN₁)
      normalizer_R := gen49q_normalizer_map_mk_le hp hOM
        (show IsPGroup p (R.subgroupOf H) from hRp.comap_subtype)
        (by rw [Subgroup.map_subgroupOf_eq_of_le hRH]; exact hN₂)
      others := gen49q_others hG hl hRP hRe hxH hOM hxo' }

theorem gen49_cover (hG : Gen5Global G) (hl : Gen5Local G p P M x) (hB : GL83Generic4_9B)
    (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    {R : Subgroup G} (hRP : R ≤ (P : Subgroup G)) (hRe : IsElemAbelian p R)
    (hRc : Nat.card R = p ^ 2) (hxR : x ∈ R) : Gen49Cover G p M x R := by
  intro H hHtop hRH hrk hHM hOM'
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  have hOM := gen49q_core_le_subgroupOf_inf hOM'
  obtain ⟨R', hR'H, hRR', hR'M⟩ := gen49q_exists_sylow hG hl hRP hRe hRc hRH
  rcases hB hInn hWC (gen49q_hyp hG hl hRP hRe hRc hxR hHtop hRH hrk hOM hR'H hRR' hR'M) with
    hΓ | ⟨K, hKn, hKC, hKΓ⟩
  · exact absurd hΓ (map_mk_inf_ne_top hOM hHM)
  · exact gen49q_extract (hRH hxR) hKn hKC hKΓ

end CFSG.LocalAnalysis.RankThreeTheoremC
