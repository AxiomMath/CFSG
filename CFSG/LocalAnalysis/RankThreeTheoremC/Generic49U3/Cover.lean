module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Config
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Struct
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.RankTwoAbelian
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9B
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9CoverAux
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLinesPlanes
public import CFSG.LocalAnalysis.AGLEmbedding.CentralComponent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G}

private theorem u3q_exists_sylow [Fact p.Prime] (hS : Setting G) (hU0 : FullCoreLocal G)
    (hp : p ∈ rankThreeSigmaA G) (hM : IsCoreMaxLocal p P M)
    {R H : Subgroup G} (hRP : R ≤ (P : Subgroup G)) (hRe : IsElemAbelian p R)
    (hRc : Nat.card R = p ^ 2) (hRH : R ≤ H) :
    ∃ R' : Subgroup G, IsSylowOf p R' H ∧ R ≤ R' ∧ R' ≤ M := by
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  have hRp : IsPGroup p R := elementary_isPGroup p R hRe
  have hRA : R ≤ H ⊓ M := le_inf hRH (hRP.trans hPM)
  obtain ⟨T₁, hT₁⟩ := (hRp.comap_subtype (K := H ⊓ M)).exists_le_sylow
  set R'' : Subgroup G := (T₁ : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype
  have hR''A : IsSylowOf p R'' (H ⊓ M) := ⟨T₁, rfl⟩
  have hRR'' : R ≤ R'' := fun r hr => ⟨⟨r, hRA hr⟩, hT₁ hr, rfl⟩
  have hR''M : R'' ≤ M := hR''A.le.trans inf_le_right
  have hR''H : R'' ≤ H := hR''A.le.trans inf_le_left
  have hR''p : IsPGroup p R'' := hR''A.isPGroup
  obtain ⟨T₂, hT₂⟩ := (hR''p.comap_subtype (K := H)).exists_le_sylow
  set R' : Subgroup G := (T₂ : Subgroup ↥H).map H.subtype
  have hR'H : IsSylowOf p R' H := ⟨T₂, rfl⟩
  have hR''R' : R'' ≤ R' := fun r hr => ⟨⟨r, hR''H hr⟩, hT₂ hr, rfl⟩
  refine ⟨R', hR'H, hRR''.trans hR''R', ?_⟩
  have hR'R'' : R' ≤ R'' := by
    by_contra hnle
    have hlt : R''.subgroupOf R' < ⊤ :=
      lt_top_iff_ne_top.mpr fun htop => hnle (Subgroup.subgroupOf_eq_top.mp htop)
    have : Group.IsNilpotent ↥R' := hR'H.isPGroup.isNilpotent
    obtain ⟨n, hn, hnB⟩ := IsConcreteLE.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent _ hlt)
    rw [← Subgroup.subgroupOf_normalizer_eq hR''R'] at hn
    have hnM : (n : G) ∈ M := normalizer_le_of_le_of_two_le_pRank hS hU0 hp
      hM hR''p hR''M (le_pRank_of_elemAbelian_card hRR'' hRe hRc) hn
    have hQA : R'' ⊔ zpowers (n : G) ≤ H ⊓ M :=
      sup_le hR''A.le (zpowers_le.mpr ⟨hR'H.le n.2, hnM⟩)
    have hQR' : R'' ⊔ zpowers (n : G) ≤ R' := sup_le hR''R' (zpowers_le.mpr n.2)
    have hQ : R'' ⊔ zpowers (n : G) = R'' :=
      hR''A.eq_of_le le_sup_left hQA (hR'H.isPGroup.to_le hQR')
    exact hnB (hQ ▸ mem_sup_right (mem_zpowers (n : G)))
  exact hR'R''.trans hR''M

private theorem u3q_abelian [Fact p.Prime] (hS : Setting G) (hc : U3Config G p P M x J)
    (hfus : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) ∧ U3LineWC x (P : Subgroup G))
    {A : Subgroup G} (hAp : IsPGroup p A) (hAM : A ≤ M) (hxA : x ∈ A)
    (hrk : CFSG.Open.pRank p A ≤ 2) : IsMulCommutative A := by
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  obtain ⟨m, hm⟩ := pGroup_conjugate_into_sylow_within_overgroup p hc.prime P M hPM A hAp hAM
  set f : G →* G := (MulAut.conj (m : G)).toMonoidHom with hf
  have hfinj : Function.Injective f := (MulAut.conj (m : G)).injective
  have hxm : x ∈ A.map f := by
    have h1 : (Subgroup.zpowers x).map f ≤ (P : Subgroup G) :=
      (Subgroup.map_mono (Subgroup.zpowers_le.mpr hxA)).trans hm
    have h2 := hfus.2 (m : G) h1
    have h3 : x ∈ (Subgroup.zpowers x).map f := by
      rw [hf, h2]
      exact Subgroup.mem_zpowers x
    exact Subgroup.map_mono (Subgroup.zpowers_le.mpr hxA) h3
  have hrk' : CFSG.Open.pRank p (A.map f) ≤ 2 := by
    rw [CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hc.prime f hfinj A]
    exact hrk
  obtain ⟨hT, hTexp, hTnc, -⟩ := u3_T_structure hc
  obtain ⟨Z, hZc, hxZ, hZS, hZT, hTZ, hTZsup⟩ := u3_S_decomp hc
  have hPS : (P : Subgroup G) = u3S P x := (inf_of_le_left hfus.1).symm
  have hZp : IsPGroup p Z := P.isPGroup'.to_le (hZS.trans inf_le_left)
  obtain ⟨-, hx1, hxp, -, -⟩ := hc.generic.2.1
  have hR'' : IsMulCommutative (A.map f) :=
    rank_two_abelian (p := p) (by have := hc.five; omega) hT hTexp hTnc hZc hZp
      (fun t ht c hc' => (hZT c hc' t ht).symm) hTZ hxZ hx1 hxp
      (hm.trans (by rw [hPS, ← hTZsup])) hxm hrk'
  have := Subgroup.comap_injective_isMulCommutative (H := A.map f) hfinj
  rwa [Subgroup.comap_map_eq_self_of_injective hfinj] at this

private theorem u3q_sylow_abelian_of_conj {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (Q₀ : Sylow p K) (h : IsMulCommutative (Q₀ : Subgroup K)) (Q : Sylow p K) :
    IsMulCommutative (Q : Subgroup K) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq K Q₀ Q
  have : (↑(g • Q₀) : Subgroup K) = (Q₀ : Subgroup K).map (MulAut.conj g).toMonoidHom := rfl
  rw [this]
  infer_instance

private theorem u3q_hab [Fact p.Prime] {H R' : Subgroup G} (hR'H : IsSylowOf p R' H)
    (hab : IsMulCommutative R')
    (S : Sylow p (H ⧸ primeComplementCore (G := H) p)) :
    IsMulCommutative (S : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
  obtain ⟨T, rfl⟩ := Sylow.mapSurjective_surjective
    (QuotientGroup.mk'_surjective (primeComplementCore (G := H) p)) p S
  obtain ⟨T₀, hT₀⟩ := hR'H.exists_sylow_eq_subgroupOf
  have hT₀ab : IsMulCommutative (T₀ : Subgroup H) := by
    rw [hT₀]
    exact Subgroup.comap_injective_isMulCommutative (H := R') (f := H.subtype) H.subtype_injective
  have hT' := u3q_sylow_abelian_of_conj T₀ hT₀ab T
  rw [Sylow.coe_mapSurjective]
  infer_instance

private theorem u3q_conj_apply {K : Type*} [Group K] (a y : K) :
    (MulAut.conj a).toMonoidHom y = a * y * a⁻¹ := rfl

private theorem u3q_map_conj_inv_map_conj {K : Type*} [Group K] (B : Subgroup K) (a : K) :
    (B.map (MulAut.conj a⁻¹).toMonoidHom).map (MulAut.conj a).toMonoidHom = B := by
  rw [Subgroup.map_map]
  have : (MulAut.conj a).toMonoidHom.comp (MulAut.conj a⁻¹).toMonoidHom = MonoidHom.id K := by
    ext y
    rw [MonoidHom.comp_apply, u3q_conj_apply, u3q_conj_apply, MonoidHom.id_apply]
    group
  rw [this, Subgroup.map_id]

private theorem u3q_map_conj_comp {K : Type*} [Group K] (B : Subgroup K) (a b : K) :
    (B.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      B.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  have : (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
      (MulAut.conj (a * b)).toMonoidHom := by
    ext y
    rw [MonoidHom.comp_apply, u3q_conj_apply, u3q_conj_apply, u3q_conj_apply]
    group
  rw [this]

private theorem u3q_hweak [Fact p.Prime] (hwc : U3LineWC x (P : Subgroup G)) :
    ∀ Q : Sylow p G, x ∈ (Q : Subgroup G) → ∀ g : G,
      (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup G) →
        (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x := by
  intro Q hxQ g hg
  obtain ⟨c, rfl⟩ := MulAction.exists_smul_eq G P Q
  have hQ : (↑(c • P) : Subgroup G) = (P : Subgroup G).map (MulAut.conj c).toMonoidHom := rfl
  rw [hQ] at hxQ hg
  have h1 : (Subgroup.zpowers x).map (MulAut.conj c⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
    obtain ⟨y, hyP, hyx⟩ := Subgroup.mem_map.mp hxQ
    have hxy : (MulAut.conj c⁻¹).toMonoidHom x = y := by
      rw [← hyx, u3q_conj_apply, u3q_conj_apply]
      group
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have : (MulAut.conj c⁻¹).toMonoidHom (x ^ k) = y ^ k := by
      rw [map_zpow, hxy]
    rw [this]
    exact zpow_mem hyP k
  have e1 := hwc c⁻¹ h1
  have h2 : (Subgroup.zpowers x).map (MulAut.conj (c⁻¹ * g)).toMonoidHom ≤ (P : Subgroup G) := by
    rintro _ ⟨z, hz, rfl⟩
    have hzg : (MulAut.conj g).toMonoidHom z ∈ (P : Subgroup G).map (MulAut.conj c).toMonoidHom :=
      hg ⟨z, hz, rfl⟩
    obtain ⟨y, hyP, hyz⟩ := Subgroup.mem_map.mp hzg
    rw [u3q_conj_apply, u3q_conj_apply] at hyz
    have : (MulAut.conj (c⁻¹ * g)).toMonoidHom z = y := by
      rw [u3q_conj_apply]
      calc c⁻¹ * g * z * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * z * g⁻¹) * c := by group
        _ = c⁻¹ * (c * y * c⁻¹) * c := by rw [hyz]
        _ = y := by group
    rw [this]
    exact hyP
  have e2 := hwc (c⁻¹ * g) h2
  have e3 : (Subgroup.zpowers x).map (MulAut.conj c).toMonoidHom = Subgroup.zpowers x := by
    have := u3q_map_conj_inv_map_conj (Subgroup.zpowers x) c
    rwa [e1] at this
  have e4 : c * (c⁻¹ * g) = g := by group
  calc (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom
      = (Subgroup.zpowers x).map (MulAut.conj (c * (c⁻¹ * g))).toMonoidHom := by rw [e4]
    _ = ((Subgroup.zpowers x).map (MulAut.conj (c⁻¹ * g)).toMonoidHom).map
          (MulAut.conj c).toMonoidHom := (u3q_map_conj_comp _ c (c⁻¹ * g)).symm
    _ = Subgroup.zpowers x := by rw [e2, e3]

private theorem u3q_others [Fact p.Prime] (hS : Setting G) (hU0 : FullCoreLocal G)
    (hc : U3Config G p P M x J)
    (hL42 : ∀ a ∈ u3U0 P x J, a ∉ Subgroup.zpowers x → Subgroup.centralizer ({a} : Set G) ≤ M)
    (hU0e : IsElemAbelian p (u3U0 P x J)) (hU0c : Nat.card (u3U0 P x J) = p ^ 2)
    (hRP : u3U0 P x J ≤ (P : Subgroup G))
    {H : Subgroup G} (hxH : x ∈ H)
    (hOM : primeComplementCore (G := H) p ≤ (H ⊓ M).subgroupOf H)
    (hxo' : orderOf (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hxH⟩) = p) :
    ∀ a ∈ ((u3U0 P x J).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)),
      a ≠ 1 →
      zpowers a ≠ zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hxH⟩) →
      centralizer ({a} : Set (H ⧸ primeComplementCore (G := H) p)) ≤
          ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ∧
        normalizer ((zpowers a : Subgroup (H ⧸ primeComplementCore (G := H) p)) :
            Set (H ⧸ primeComplementCore (G := H) p)) ≤
          ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
  have hp : p.Prime := hc.prime
  rintro _ ⟨r, hr, rfl⟩ hr1 hrx
  have hrR : (r : G) ∈ u3U0 P x J := hr
  have hr1' : (r : G) ≠ 1 := fun h => hr1 (by rw [show r = 1 from Subtype.ext h, map_one])
  have hrp : (r : G) ^ p = 1 := hU0e.2 _ hrR
  have hrx' : (r : G) ∉ zpowers x := by
    intro hmem
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
    have hrk : r = (⟨x, hxH⟩ : H) ^ k := Subtype.ext (by rw [← hk]; rfl)
    have hmem' : QuotientGroup.mk' (primeComplementCore (G := H) p) r ∈
        zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hxH⟩) := by
      rw [hrk, map_zpow]
      exact zpow_mem (mem_zpowers _) k
    exact hrx (eq_zpowers_of_card_eq_prime (by rw [Nat.card_zpowers, hxo']) hmem' hr1).symm
  have hCM : centralizer ({(r : G)} : Set G) ≤ M := hL42 (r : G) hrR hrx'
  have hRC : u3U0 P x J ≤ (P : Subgroup G) ⊓ centralizer ({(r : G)} : Set G) :=
    le_inf hRP fun u hu => mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hU0e.1.is_comm.comm ⟨u, hu⟩ ⟨(r : G), hrR⟩))
  have hNM : normalizer ((zpowers (r : G) : Subgroup G) : Set G) ≤ M :=
    normalizer_zpowers_le_of_centralizer_le hS hU0 hc.sigma hc.core
      (le_pRank_of_elemAbelian_card hRC hU0e hU0c) hCM
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

private theorem u3q_hyp [Fact p.Prime] (hS : Setting G) (hU0 : FullCoreLocal G)
    (hc : U3Config G p P M x J)
    (hfus : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) ∧ U3LineWC x (P : Subgroup G))
    (hL42 : ∀ a ∈ u3U0 P x J, a ∉ Subgroup.zpowers x → Subgroup.centralizer ({a} : Set G) ≤ M)
    (hU0e : IsElemAbelian p (u3U0 P x J)) (hU0c : Nat.card (u3U0 P x J) = p ^ 2)
    (hRP : u3U0 P x J ≤ (P : Subgroup G)) (hxR : x ∈ u3U0 P x J)
    {H R' : Subgroup G} (hHtop : H ≠ ⊤) (hRH : u3U0 P x J ≤ H) (hrk : CFSG.Open.pRank p H ≤ 2)
    (hOM : primeComplementCore (G := H) p ≤ (H ⊓ M).subgroupOf H)
    (hR'H : IsSylowOf p R' H) (hRR' : u3U0 P x J ≤ R') (hR'M : R' ≤ M) :
    Gen49BHyp p ((R'.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
      (((u3U0 P x J).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
      (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hRH hxR⟩) := by
  have hp := hc.prime
  have hxH : x ∈ H := hRH hxR
  set O : Subgroup H := primeComplementCore (G := H) p
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hRp : IsPGroup p (u3U0 P x J) := elementary_isPGroup p _ hU0e
  have hxo : orderOf (⟨x, hxH⟩ : H) = p := by
    obtain ⟨-, hx1, hxp, -, -⟩ := hc.generic.2.1
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hxp hx1
  have hxo' : orderOf (QuotientGroup.mk' O ⟨x, hxH⟩) = p :=
    orderOf_mk_of_coprime hp O (primeComplementCore_coprime p) hxo
  have hR'ab : IsMulCommutative R' :=
    u3q_abelian hS hc hfus hR'H.isPGroup hR'M (hRR' hxR) (hrk.trans' (pRank_mono p hp.one_lt hR'H.le))
  have hab := u3q_hab hR'H hR'ab
  obtain ⟨T, hT⟩ := hR'H.exists_sylow_eq_subgroupOf
  set Q : Sylow p (H ⧸ O) := T.mapSurjective (QuotientGroup.mk'_surjective O) with hQdef
  have hQS : (Q : Subgroup (H ⧸ O)) = (R'.subgroupOf H).map (QuotientGroup.mk' O) := by
    rw [hQdef, Sylow.coe_mapSurjective, hT]
  have hxS : QuotientGroup.mk' O ⟨x, hxH⟩ ∈ (R'.subgroupOf H).map (QuotientGroup.mk' O) :=
    ⟨⟨x, hxH⟩, hRR' hxR, rfl⟩
  have hN₁ : normalizer (R' : Set G) ≤ M := normalizer_le_of_le_of_two_le_pRank hS hU0
    hc.sigma hc.core hR'H.isPGroup hR'M (le_pRank_of_elemAbelian_card hRR' hU0e hU0c)
  have hN₂ : normalizer (u3U0 P x J : Set G) ≤ M := normalizer_le_of_le_of_two_le_pRank hS hU0
    hc.sigma hc.core hRp (hRP.trans hPM) (le_pRank_of_elemAbelian_card le_rfl hU0e hU0c)
  exact
    { ne_two := by have := hc.five; omega
      core_eq_bot := primeComplementCore_quotient_eq_bot p
      catalog := (catalogSimpleSections_of_isKProper hS.kProper H hHtop).quotient O
      sylow := isSylowOf_top_map_mk hR'H
      abelian := by
        rw [← hQS]
        exact hab Q
      le_sylow := Subgroup.map_mono (Subgroup.subgroupOf_mono H hRR')
      elemAbelian := gen49q_isElemAbelian_map _ (isElemAbelian_subgroupOf hU0e H)
      card_eq := by
        rw [card_map_mk_of_isPGroup hp O (primeComplementCore_coprime p)
          (show IsPGroup p ((u3U0 P x J).subgroupOf H) from hRp.comap_subtype),
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv]
        exact hU0c
      pRank_le := gen49q_pRank_top_quotient_le hp hrk
      mem := ⟨⟨x, hxH⟩, hxR, rfl⟩
      ne_one := fun h => by
        rw [h, orderOf_one] at hxo'
        exact hp.one_lt.ne hxo'
      weakClosed := fun g hg => weaklyClosed_map_mk hxo hab (u3q_hweak hfus.2) Q
        (hQS ▸ hxS) g (by rw [hQS]; exact hg)
      normalizer_S := gen49q_normalizer_map_mk_le hp hOM
        (show IsPGroup p (R'.subgroupOf H) from hR'H.isPGroup.comap_subtype)
        (by rw [Subgroup.map_subgroupOf_eq_of_le hR'H.le]; exact hN₁)
      normalizer_R := gen49q_normalizer_map_mk_le hp hOM
        (show IsPGroup p ((u3U0 P x J).subgroupOf H) from hRp.comap_subtype)
        (by rw [Subgroup.map_subgroupOf_eq_of_le hRH]; exact hN₂)
      others := u3q_others hS hU0 hc hL42 hU0e hU0c hRP hxH hOM hxo' }

theorem u3_cover (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hInn : KFactInnerAction) (hWC : KFactWeakClosure) (hc : U3Config G p P M x J)
    (hfus : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) ∧ U3LineWC x (P : Subgroup G))
    (hL42 : ∀ a ∈ u3U0 P x J, a ∉ Subgroup.zpowers x → Subgroup.centralizer ({a} : Set G) ≤ M) :
    Gen49Cover G p M x (u3U0 P x J) := by
  intro H hHtop hRH hrk hHM hOM'
  haveI : Fact p.Prime := ⟨hc.prime⟩
  obtain ⟨hU0e, hU0c, hU0S, hxR, -, -, -⟩ := u3U0_facts hc
  have hRP : u3U0 P x J ≤ (P : Subgroup G) := hU0S.trans inf_le_left
  have hOM := gen49q_core_le_subgroupOf_inf hOM'
  obtain ⟨R', hR'H, hRR', hR'M⟩ := u3q_exists_sylow hS hU0 hc.sigma hc.core hRP hU0e hU0c hRH
  rcases gl83Generic4_9B_holds hInn hWC
      (u3q_hyp hS hU0 hc hfus hL42 hU0e hU0c hRP hxR hHtop hRH hrk hOM hR'H hRR' hR'M) with
    hΓ | ⟨K, hKn, hKC, hKΓ⟩
  · exact absurd hΓ (map_mk_inf_ne_top hOM hHM)
  · exact gen49q_extract (hRH hxR) hKn hKC hKΓ

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
