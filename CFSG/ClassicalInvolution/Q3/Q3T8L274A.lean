module

public import CFSG.ClassicalInvolution.Q3.Q3T7LayerQ
public import CFSG.ClassicalInvolution.Q3.Q3T7LayerAE
public import CFSG.ClassicalInvolution.Asc77.AscT8LayerCl
public import CFSG.ClassicalInvolution.Asc77.AscC25J10

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Layer

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.T8 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.Q3T7 CFSG.ClassicalInvolution.Q3.Disc3
  CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G} {K : Subgroup G}

omit [Finite G] in
theorem _root_.CFSG.ClassicalInvolution.Asc77.T8.XMem.conj3 (hΩ : ConjInvariant Ω)
    (h : XMem Ω x K) {n : G} (hn : n ∈ cenZ x) :
    XMem Ω x (conjSub n K) := by
  obtain ⟨hK, hN, R, hR, hRx⟩ := h
  have hnx : n * x = x * n := mem_cenZ_iff.mp hn
  have hnx' : n⁻¹ * x = x * n⁻¹ := by
    calc n⁻¹ * x = n⁻¹ * (x * n) * n⁻¹ := by group
      _ = n⁻¹ * (n * x) * n⁻¹ := by rw [hnx]
      _ = x * n⁻¹ := by group
  refine ⟨hΩ n K hK, ?_, conjSub n R, hR.conj n, ?_⟩
  · rw [mem_normalizer_iff_conjSub_eq] at hN ⊢
    rw [← conjSub_mul, ← hnx, conjSub_mul, hN]
  · intro r hr
    rw [mem_conjSub_iff] at hr
    have h1 := hRx _ hr
    calc r * x = n * (n⁻¹ * r * n) * (n⁻¹ * x) := by group
      _ = n * (n⁻¹ * r * n) * (x * n⁻¹) := by rw [hnx']
      _ = n * ((n⁻¹ * r * n) * x) * n⁻¹ := by group
      _ = n * (x * (n⁻¹ * r * n)) * n⁻¹ := by rw [h1]
      _ = (n * x) * (n⁻¹ * r * n) * n⁻¹ := by group
      _ = (x * n) * (n⁻¹ * r * n) * n⁻¹ := by rw [hnx]
      _ = x * r := by group

theorem _root_.CFSG.ClassicalInvolution.Asc77.T8.XMem.trivialOnQuot3 (hΩ : HypOmegaGen Ω)
    (hx : x * x = 1) (h : XMem Ω x K) :
    x ∈ trivialOnQuot K := by
  obtain ⟨hK, hN, R, hR, hRx⟩ := h
  have hV : IsPGroup 2 ↥(Subgroup.zpowers x) := isPGroup_zpowers_of_sq hx
  refine ⟨hN, fun k hk => ?_⟩
  exact Sec6Gen.centSylow hΩ hK hR hV
    (fun y hy => mem_normalizer_iff_conjSub_eq.mp
      (Subgroup.zpowers_le.mpr hN hy)) (fun r hr v hv => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
        exact (Commute.zpow_right (show Commute r x from hRx r hr) m).eq) k hk x
    (Subgroup.mem_zpowers x)

theorem _root_.CFSG.ClassicalInvolution.Asc77.T8.XMem.mem_tqMembers3 (hΩ : HypOmegaGen Ω)
    (hx : x * x = 1) (h : XMem Ω x K) :
    K ∈ tqMembers3 Ω x :=
  ⟨h.1, h.trivialOnQuot3 hΩ hx⟩

end Basic

section Img

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}


structure LayerHyp (Ω : Set (Subgroup G)) (x : G) : Prop where
  gen : HypOmegaGen Ω
  sq : x * x = 1
  pair : HypOmegaGen (exactPair3 Ω x)
  quot : HypOmegaGen (layerFam3 Ω x)

theorem LayerHyp.hc2 (L : LayerHyp Ω x) : IsPGroup 2 (Subgroup.zpowers x) :=
  isPGroup_zpowers_of_sq L.sq

theorem LayerHyp.of_stand3 {K₀ : Subgroup G} (hs : AscStand3 Ω K₀) (hx : x * x = 1)
    (hne : (tqMembers3 Ω x).Nonempty) : LayerHyp Ω x where
  gen := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hs.hyp
  sq := hx
  pair := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1)
    (hypOmegaModU_exactPair3 hs (isPGroup_zpowers_of_sq hx) hne)
  quot := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1)
    (Q3T7.hypOmegaModU_layerFam3 hs (isPGroup_zpowers_of_sq hx) hne)

theorem exactCore3_le_exactLayer3' {K : Subgroup G} (hK : K ∈ tqMembers3 Ω x) :
    exactCore3 x K ≤ exactLayer3 Ω x :=
  exactCore3_le_exactLayer3 hK

theorem subgroupOf_mem_exactPair3 {K : Subgroup G} (hK : K ∈ tqMembers3 Ω x) :
    (exactCore3 x K).subgroupOf (exactLayer3 Ω x) ∈ exactPair3 Ω x :=
  ⟨exactCore3 x K, ⟨exactCore3_mem_exactFamily3 hK, exactCore3_le_centralizer x K⟩,
    exactCore3_le_exactLayer3 hK, rfl⟩

@[expose] def layerImg3 (Ω : Set (Subgroup G)) (x : G) (K : Subgroup G) :
    Subgroup (layerQuot3 Ω x) :=
  ((exactCore3 x K).subgroupOf (exactLayer3 Ω x)).map
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer3 Ω x)))

theorem layerImg3_mem {K : Subgroup G} (hK : K ∈ tqMembers3 Ω x) :
    layerImg3 Ω x K ∈ layerFam3 Ω x :=
  ⟨_, subgroupOf_mem_exactPair3 hK, rfl⟩

theorem odd_natCard_oddCore_exactLayer3 :
    Odd (Nat.card (classicalInvolutionOddCore ↥(exactLayer3 Ω x))) :=
  CFSG.ComponentClassification.OddCore.odd_card ↥(exactLayer3 Ω x)

theorem exactCore3_conj_cen {n : G} (hn : n ∈ cenZ x) (K : Subgroup G) :
    conjSub n (exactCore3 x K) = exactCore3 x (conjSub n K) := by
  have h := exactCore3_conjSub n x K
  rw [conj_eq_of_mem_centralizer_singleton (cenZ_eq_centralizer x ▸ hn)] at h
  exact h.symm

theorem mem_normalizer_exactCore3 {K : Subgroup G} {j : G}
    (hjK : j ∈ Subgroup.normalizer (K : Set G)) (hjx : j ∈ cenZ x) :
    j ∈ Subgroup.normalizer ((exactCore3 x K : Subgroup G) : Set G) :=
  mem_normalizer_inf hjK (Subgroup.le_normalizer (cenZ_eq_centralizer x ▸ hjx))

theorem exactLayer3_le_cenZ (Ω : Set (Subgroup G)) (x : G) : exactLayer3 Ω x ≤ cenZ x :=
  (cenZ_eq_centralizer x).symm ▸ exactLayer3_le_centralizer Ω x

theorem layerImg3_isSylow2In {K P : Subgroup G} (hK : K ∈ tqMembers3 Ω x) (hP : IsSylow2In P K)
    (hPx : P ≤ cenZ x) :
    IsSylow2In ((P.subgroupOf (exactLayer3 Ω x)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer3 Ω x)))) (layerImg3 Ω x K) := by
  have hPc : IsSylow2In P (exactCore3 x K) :=
    isSylow2In_of_le_of_le hP (le_inf hP.1 ((cenZ_eq_centralizer x) ▸ hPx)) inf_le_left
  exact isSylow2In_map_mk odd_natCard_oddCore_exactLayer3
    (hPc.subgroupOf (exactCore3_le_exactLayer3 hK))

theorem layerImg3_omegaNbr {K J P : Subgroup G} (hK : K ∈ tqMembers3 Ω x)
    (hJ : J ∈ tqMembers3 Ω x) (hP : IsSylow2In P J) (hPx : P ≤ cenZ x)
    (hPN : P ≤ Subgroup.normalizer (K : Set G)) (hne : layerImg3 Ω x K ≠ layerImg3 Ω x J) :
    layerImg3 Ω x J ∈ omegaNbr (layerFam3 Ω x) (layerImg3 Ω x K) := by
  have hT := layerImg3_isSylow2In hJ hP hPx
  refine ⟨layerImg3_mem hJ, fun h => hne h.symm, _,
    mem_RSet_of_isSylow2In (layerImg3_mem hJ) hT, hT.1, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have htK : (t : G) ∈ Subgroup.normalizer (K : Set G) := hPN (Subgroup.mem_subgroupOf.mp ht)
  have htx : (t : G) ∈ cenZ x := hPx (Subgroup.mem_subgroupOf.mp ht)
  have htN : (t : G) ∈ Subgroup.normalizer ((exactCore3 x K : Subgroup G) : Set G) :=
    mem_normalizer_exactCore3 htK htx
  have htN' := (mem_normalizer_subgroupOf_iff (exactCore3_le_exactLayer3 hK)).mp htN
  exact mem_normalizer_map_hom _ htN'

theorem layerImg3_ne {K J P Q : Subgroup G} (hK : K ∈ tqMembers3 Ω x) (hJ : J ∈ tqMembers3 Ω x)
    (hP : IsSylow2In P K) (hQ : IsSylow2In Q J) (hPx : P ≤ cenZ x) (hQx : Q ≤ cenZ x)
    (hc : Commutes P Q) (hPQ : P ≠ Q) : layerImg3 Ω x K ≠ layerImg3 Ω x J := by
  intro h
  have hodd := odd_natCard_oddCore_exactLayer3 (Ω := Ω) (x := x)
  have hPL : IsSylow2In P (exactCore3 x K) :=
    isSylow2In_of_le_of_le hP (le_inf hP.1 ((cenZ_eq_centralizer x) ▸ hPx)) inf_le_left
  have hQL : IsSylow2In Q (exactCore3 x J) :=
    isSylow2In_of_le_of_le hQ (le_inf hQ.1 ((cenZ_eq_centralizer x) ▸ hQx)) inf_le_left
  have hP1 := hPL.subgroupOf (exactCore3_le_exactLayer3 hK)
  have hQ1 := hQL.subgroupOf (exactCore3_le_exactLayer3 hJ)
  have hPs := isSylow2In_map_mk hodd hP1
  have hQs := isSylow2In_map_mk hodd hQ1
  change IsSylow2In _ (layerImg3 Ω x K) at hPs
  change IsSylow2In _ (layerImg3 Ω x J) at hQs
  rw [← h] at hQs
  have hc' : Commutes (P.subgroupOf (exactLayer3 Ω x)) (Q.subgroupOf (exactLayer3 Ω x)) :=
    fun a ha b hb => Subtype.ext
      (hc a (Subgroup.mem_subgroupOf.mp ha) b (Subgroup.mem_subgroupOf.mp hb))
  have hc'' : Commutes (Q.subgroupOf (exactLayer3 Ω x)) (P.subgroupOf (exactLayer3 Ω x)) :=
    fun b hb a ha => (hc' a ha b hb).symm
  have hcmap : Commutes ((P.subgroupOf (exactLayer3 Ω x)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer3 Ω x))))
      ((Q.subgroupOf (exactLayer3 Ω x)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer3 Ω x)))) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc' a ha b hb]
  have heq := eq_of_commutes_isSylow2In hPs hQs hcmap
  have h1 := le_of_map_le_of_commutes _ hodd hP1.2.1 hQ1.2.1 hc' heq.ge
  have h2 := le_of_map_le_of_commutes _ hodd hQ1.2.1 hP1.2.1 hc'' heq.le
  have hPY : P ≤ exactLayer3 Ω x := hPL.1.trans (exactCore3_le_exactLayer3 hK)
  have hQY : Q ≤ exactLayer3 Ω x := hQL.1.trans (exactCore3_le_exactLayer3 hJ)
  refine hPQ (le_antisymm (fun y hy => ?_) (fun y hy => ?_))
  · exact Subgroup.mem_subgroupOf.mp
      (h1 (Subgroup.mem_subgroupOf.mpr hy : (⟨y, hPY hy⟩ : ↥(exactLayer3 Ω x)) ∈ _))
  · exact Subgroup.mem_subgroupOf.mp
      (h2 (Subgroup.mem_subgroupOf.mpr hy : (⟨y, hQY hy⟩ : ↥(exactLayer3 Ω x)) ∈ _))

theorem layerImg3_conj_of_mem_oddCore {K : Subgroup G} {ν : G}
    (hν : ν ∈ oddCoreOf (exactLayer3 Ω x)) : layerImg3 Ω x (conjSub ν K) = layerImg3 Ω x K := by
  obtain ⟨ν', hν', rfl⟩ := Subgroup.mem_map.mp hν
  change layerImg3 Ω x (conjSub ((ν' : ↥(exactLayer3 Ω x)) : G) K) = _
  have hνc : ((ν' : ↥(exactLayer3 Ω x)) : G) ∈ cenZ x := exactLayer3_le_cenZ Ω x ν'.2
  have hn1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer3 Ω x)) ν' = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hν'
  unfold layerImg3
  rw [← exactCore3_conj_cen hνc, ← conjSub_subgroupOf, AscQuot.map_conjSub, hn1, conjSub_one]

theorem isUniqueInvolution_exactCore3 {K : Subgroup G}
    (hxK : x ∈ Subgroup.normalizer (K : Set G)) {z : G} (hz : IsUniqueInvolution K z) :
    IsUniqueInvolution (exactCore3 x K) z := by
  have hzx : x * z = z * x := by
    have h := hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp hxK)
    calc x * z = (x * z * x⁻¹) * x := by group
      _ = z * x := by rw [h]
  refine ⟨⟨hz.mem, Subgroup.mem_centralizer_singleton_iff.mpr hzx.symm⟩, hz.ne_one, hz.sq,
    fun y hy hy2 => hz.unique y (exactCore3_le_left x K hy) hy2⟩

theorem eq_of_exactCore3_eq (L : LayerHyp Ω x) {K J : Subgroup G} (hK : K ∈ tqMembers3 Ω x)
    (hJ : J ∈ tqMembers3 Ω x) (h : exactCore3 x K = exactCore3 x J) : K = J := by
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
    (bot_le : (⊥ : Subgroup G) ≤ exactCore3 x K)
  have hVK := ((isSylow2In_exactCore3_iff L.hc2 hK.2).mp hV).1
  have hVJ := ((isSylow2In_exactCore3_iff L.hc2 hJ.2).mp (h ▸ hV)).1
  have h8 := Sec6Gen.eight_le_of_mem_RSet L.gen (mem_RSet_of_isSylow2In hK.1 hVK)
  exact Sec6Gen.eq_of_le_of_le L.gen hK.1 hJ.1 hVK.2.1 (by omega) hVK.1 hVJ.1

theorem layer_omegaNbr3 (L : LayerHyp Ω x) {K J : Subgroup G} (hK : K ∈ tqMembers3 Ω x)
    (hJ : J ∈ tqMembers3 Ω x) (m : ↥(exactLayer3 Ω x))
    (h : (exactCore3 x J).subgroupOf (exactLayer3 Ω x) ∈
      omegaNbr (exactPair3 Ω x) (conjSub m ((exactCore3 x K).subgroupOf (exactLayer3 Ω x)))) :
    J ∈ omegaNbr Ω (conjSub (m : G) K) := by
  obtain ⟨-, hne, T', hT'R, hT'J, hT'N⟩ := h
  have hmc : (m : G) ∈ cenZ x := exactLayer3_le_cenZ Ω x m.2
  have hmc' : (m : G) ∈ Subgroup.centralizer ({x} : Set G) := (cenZ_eq_centralizer x) ▸ hmc
  have hKm : conjSub (m : G) K ∈ tqMembers3 Ω x :=
    conjSub_mem_tqMembers3 L.gen.conjInvariant hmc' hK
  have hLm : exactCore3 x (conjSub (m : G) K) = conjSub (m : G) (exactCore3 x K) :=
    (exactCore3_conj_cen hmc K).symm
  have hYJ : exactCore3 x J ≤ exactLayer3 Ω x := exactCore3_le_exactLayer3 hJ
  have hYKm : exactCore3 x (conjSub (m : G) K) ≤ exactLayer3 Ω x := exactCore3_le_exactLayer3 hKm
  have hTJ : T'.map (exactLayer3 Ω x).subtype ≤ exactCore3 x J := by
    have := Subgroup.map_mono (f := (exactLayer3 Ω x).subtype) hT'J
    rwa [Subgroup.map_subgroupOf_eq_of_le hYJ] at this
  obtain ⟨J₀, ⟨⟨J₀', hJ₀', rfl⟩, -⟩, hJ₀Y, hTJ₀⟩ := exists_isSylow2In_of_mem_RSet_restrict hT'R
  have hTK₀ : IsSylow2In (T'.map (exactLayer3 Ω x).subtype) J₀' :=
    ((isSylow2In_exactCore3_iff L.hc2 hJ₀'.2).mp hTJ₀).1
  have h8 := Sec6Gen.eight_le_of_mem_RSet L.gen (mem_RSet_of_isSylow2In hJ₀'.1 hTK₀)
  have hJJ : J₀' = J := Sec6Gen.eq_of_le_of_le L.gen hJ₀'.1 hJ.1 hTK₀.2.1 (by omega) hTK₀.1
    (hTJ.trans (exactCore3_le_left x J))
  subst hJJ
  have hKJ : conjSub (m : G) K ≠ J₀' := by
    intro hKJ
    apply hne
    rw [← hKJ, hLm, conjSub_subgroupOf]
  obtain ⟨z', hz'⟩ := Sec6Gen.exists_uniqueInvolution L.gen hKm.1
  have hz'L : IsUniqueInvolution (exactCore3 x (conjSub (m : G) K)) z' :=
    isUniqueInvolution_exactCore3 hKm.2.1 hz'
  have hYm : conjSub (m : G) (exactCore3 x K) ≤ exactLayer3 Ω x := by
    rw [← hLm]
    exact hYKm
  have hTN : T'.map (exactLayer3 Ω x).subtype ≤
      Subgroup.normalizer ((exactCore3 x (conjSub (m : G) K) : Subgroup G) : Set G) := by
    rintro _ ⟨u', hu', rfl⟩
    have h1 := hT'N hu'
    rw [conjSub_subgroupOf] at h1
    show (u' : G) ∈ _
    rw [hLm]
    exact (mem_normalizer_subgroupOf_iff hYm).mpr h1
  have hAc : T'.map (exactLayer3 Ω x).subtype ≤ Subgroup.centralizer ({z'} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := conj_eq_of_conjSub_eq hz' (exactCore3_le_left x (conjSub (m : G) K)) hz'L.mem
      (mem_normalizer_iff_conjSub_eq.mp (hTN hu))
    calc u * z' = (u * z' * u⁻¹) * u := by group
      _ = z' * u := by rw [this]
  have hTNK : T'.map (exactLayer3 Ω x).subtype ≤ Subgroup.normalizer (conjSub (m : G) K : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer L.gen hKm.1 hJ₀'.1 hKJ hz' hTK₀.1 hTK₀.2.1
      (by omega) hAc
  exact ⟨hJ₀'.1, fun h => hKJ h.symm, _, mem_RSet_of_isSylow2In hJ₀'.1 hTK₀,
    hTJ.trans (exactCore3_le_left x J₀'), hTNK⟩

theorem exists_oddCore_conj_of_layerImg3_eq (L : LayerHyp Ω x) {K J : Subgroup G}
    (hK : K ∈ tqMembers3 Ω x) (hJ : J ∈ tqMembers3 Ω x)
    (h : layerImg3 Ω x K = layerImg3 Ω x J) :
    ∃ n ∈ oddCoreOf (exactLayer3 Ω x), conjSub n K = J := by
  have hodd := odd_natCard_oddCore_exactLayer3 (Ω := Ω) (x := x)
  obtain ⟨m, hm, hJ'⟩ := T3CII.exists_conj_of_map_eq_gen L.pair hodd (subgroupOf_mem_exactPair3 hK)
    (subgroupOf_mem_exactPair3 hJ) h
  have hmy : ((m : ↥(exactLayer3 Ω x)) : G) ∈ exactLayer3 Ω x := m.2
  have hmc : ((m : ↥(exactLayer3 Ω x)) : G) ∈ cenZ x := exactLayer3_le_cenZ Ω x hmy
  have hmc' : ((m : ↥(exactLayer3 Ω x)) : G) ∈ Subgroup.centralizer ({x} : Set G) :=
    (cenZ_eq_centralizer x) ▸ hmc
  refine ⟨(m : G), ⟨m, hm, rfl⟩, ?_⟩
  rw [conjSub_subgroupOf] at hJ'
  have h2 := Subgroup.subgroupOf_inj.mp hJ'
  rw [inf_eq_left.mpr (exactCore3_le_exactLayer3 hJ)] at h2
  have hKm : conjSub (m : G) K ∈ tqMembers3 Ω x :=
    conjSub_mem_tqMembers3 L.gen.conjInvariant hmc' hK
  have h3 : conjSub (m : G) (exactCore3 x K) ≤ exactLayer3 Ω x := by
    rw [exactCore3_conj_cen hmc K]
    exact exactCore3_le_exactLayer3 hKm
  rw [inf_eq_left.mpr h3] at h2
  exact eq_of_exactCore3_eq L hKm hJ ((exactCore3_conj_cen hmc K).symm.trans h2.symm)

theorem exists_oddCore_conj_omegaNbr3 (L : LayerHyp Ω x) {K J : Subgroup G}
    (hK : K ∈ tqMembers3 Ω x) (hJ : J ∈ tqMembers3 Ω x)
    (h : layerImg3 Ω x J ∈ omegaNbr (layerFam3 Ω x) (layerImg3 Ω x K)) :
    ∃ n ∈ oddCoreOf (exactLayer3 Ω x), J ∈ omegaNbr Ω (conjSub n K) := by
  have hodd := odd_natCard_oddCore_exactLayer3 (Ω := Ω) (x := x)
  obtain ⟨m, hmN, hm⟩ := C25J.exists_conj_omegaNbr_gen L.pair L.quot hodd
    (subgroupOf_mem_exactPair3 hK) (subgroupOf_mem_exactPair3 hJ) h
  exact ⟨(m : G), ⟨m, hmN, rfl⟩, layer_omegaNbr3 L hK hJ m hm⟩

theorem exists_oddCore_conj_mem_dComp3 (L : LayerHyp Ω x) {K : Subgroup G}
    (hK : K ∈ tqMembers3 Ω x) (hconn : DConnected (layerFam3 Ω x)) {M : Subgroup G}
    (hM : M ∈ tqMembers3 Ω x) :
    ∃ ν ∈ oddCoreOf (exactLayer3 Ω x), conjSub ν M ∈ dComp Ω K := by
  have key : ∀ U : Subgroup (layerQuot3 Ω x),
      Relation.ReflTransGen
        (fun A B : Subgroup (layerQuot3 Ω x) => B ∈ layerFam3 Ω x ∧ dAdj (layerFam3 Ω x) A B)
        (layerImg3 Ω x K) U →
      U ∈ layerFam3 Ω x ∧ ∀ M' : Subgroup G, M' ∈ tqMembers3 Ω x → layerImg3 Ω x M' = U →
        ∃ ν ∈ oddCoreOf (exactLayer3 Ω x), conjSub ν M' ∈ dComp Ω K := by
    intro U hU
    induction hU with
    | refl =>
      refine ⟨layerImg3_mem hK, fun M' hM' h => ?_⟩
      obtain ⟨n, hn, hnM⟩ := exists_oddCore_conj_of_layerImg3_eq L hK hM' h.symm
      refine ⟨n⁻¹, (oddCoreOf _).inv_mem hn, ?_⟩
      rw [← hnM, conjSub_inv_conjSub]
      exact Relation.ReflTransGen.refl
    | @tail b c hab hbc ih =>
      obtain ⟨hbΦ, hPb⟩ := ih
      obtain ⟨hcΦ, hadj⟩ := hbc
      refine ⟨hcΦ, fun M' hM' hMc => ?_⟩
      obtain ⟨_, ⟨L₀, ⟨⟨M₁, hM₁, rfl⟩, -⟩, hLY, rfl⟩, hb⟩ := hbΦ
      have hb' : layerImg3 Ω x M₁ = b := hb
      obtain ⟨ν₁, hν₁, hM₂⟩ := hPb M₁ hM₁ hb'
      have hν₁c : ν₁ ∈ cenZ x := exactLayer3_le_cenZ Ω x (oddCoreOf_le_self _ hν₁)
      have hν₁c' : ν₁ ∈ Subgroup.centralizer ({x} : Set G) := (cenZ_eq_centralizer x) ▸ hν₁c
      have hM₂X : conjSub ν₁ M₁ ∈ tqMembers3 Ω x :=
        conjSub_mem_tqMembers3 L.gen.conjInvariant hν₁c' hM₁
      have hM₂b : layerImg3 Ω x (conjSub ν₁ M₁) = b :=
        (layerImg3_conj_of_mem_oddCore hν₁).trans hb'
      have hdc : dComp Ω (conjSub ν₁ M₁) = dComp Ω K := dComp_eq_of_mem hK.1 hM₂
      rcases hadj with hc1 | hc2
      · rw [← hM₂b, ← hMc] at hc1
        obtain ⟨m, hm, hmn⟩ := exists_oddCore_conj_omegaNbr3 L hM₂X hM' hc1
        refine ⟨m⁻¹, (oddCoreOf _).inv_mem hm, ?_⟩
        have h1 := omegaNbr_conj L.gen.conjInvariant hmn m⁻¹
        rw [conjSub_inv_conjSub] at h1
        have h2 := mem_dComp_of_mem_omegaNbr h1
        rwa [hdc] at h2
      · rw [← hM₂b, ← hMc] at hc2
        obtain ⟨m, hm, hmn⟩ := exists_oddCore_conj_omegaNbr3 L hM' hM₂X hc2
        refine ⟨m, hm, ?_⟩
        exact Relation.ReflTransGen.tail hM₂
          ⟨L.gen.conjInvariant m M' hM'.1, Or.inr hmn⟩
  exact (key _ (hconn _ (layerImg3_mem hK) _ (layerImg3_mem hM))).2 M hM rfl

end Img

end CFSG.ClassicalInvolution.Q3.Q3T8.Layer
