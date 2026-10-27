module

public import CFSG.GH74.GLS.C3.Layer1.EvenSetup
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cA
public import CFSG.GH74.GLS.C3.Layer1.Th2CaseISyl
public import CFSG.GH74.GLS.C3.Layer1.St1PumpH1
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.AS16.Defs
public import CFSG.GH74.GLS.C3.Layer1.Th2Pump

public section

namespace CFSG.GH74.GLS.EvenSelP

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.ComponentClassification
open scoped commutatorElement


variable {G : Type} [Group G] [Finite G]

structure TermK (K : Subgroup G) : Prop where
  quasi : CFSG.IsQuasisimple ↥K
  oddCore : pPrimeCoreOf 2 K = ⊥
  even : 2 ∣ Nat.card ↥K
  comp : ∀ y : G, orderOf y = 2 → y ∈ centralizer (K : Set G) →
    IsCompIn (centralizer ({y} : Set G)) K

namespace TermK

variable {K : Subgroup G} (hK : TermK K)

include hK in
theorem isPCompIn {y : G} (hy2 : orderOf y = 2) (hyK : y ∈ centralizer (K : Set G)) :
    IsPCompIn 2 (centralizer ({y} : Set G)) K := by
  have hKcomp := hK.comp y hy2 hyK
  have hKC : K ≤ centralizer ({y} : Set G) := hKcomp.1
  refine ⟨hKC, CFSG.LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2
    hKcomp.2 fun hle => ?_⟩
  have h1 : Nat.card ↥(K.subgroupOf (centralizer ({y} : Set G))) ∣
      Nat.card ↥(pPrimeCore 2 ↥(centralizer ({y} : Set G))) := Subgroup.card_dvd_of_le hle
  have h2 : Nat.card ↥(K.subgroupOf (centralizer ({y} : Set G))) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv
  rw [h2] at h1
  have h3 := Nat.Coprime.coprime_dvd_right h1 CFSG.pPrimeCore_coprime_card
  have h4 := Nat.Coprime.eq_one_of_dvd h3 hK.even
  omega

omit [Finite G] in
include hK in
theorem mem_cSec_iff {c : G} :
    c ∈ centralizerSection K (pPrimeCoreOf 2 K) ↔ c ∈ centralizer (K : Set G) := by
  rw [hK.oddCore, mem_centralizerSection_bot_iff', Subgroup.mem_centralizer_iff]
  exact Iff.rfl

omit [Finite G] in
include hK in
theorem eq_one_of_mem_centralizer (hs : IsSimpleGroup ↥K) {z : G} (hzK : z ∈ K)
    (hzC : z ∈ centralizer (K : Set G)) : z = 1 := by
  have hc : Subgroup.center ↥K = ⊥ := center_eq_bot_of_simple_quasisimple hs hK.quasi
  have hz : (⟨z, hzK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hzC g g.2)
  rw [hc, Subgroup.mem_bot] at hz
  exact congrArg Subtype.val hz

include hK in
theorem normal_of_involution (hs : IsSimpleGroup ↥K) (hr4 : pRank 2 G ≤ 4)
    {E : Subgroup G} (hEK : E ≤ K) (hEel : CFSG.IsElementaryAbelian 2 ↥E) (hE2 : 2 ≤ pRank 2 ↥E)
    {u : G} (hu2 : orderOf u = 2) (huK : u ∈ centralizer (K : Set G)) :
    ∀ c ∈ centralizer ({u} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
  intro c hc k hk
  by_contra hkc
  have hKu := hK.isPCompIn hu2 huK
  have hK' : IsPCompIn 2 (centralizer ({u} : Set G)) (cj c K) := by
    have := Stage1.Thm2.Recip.isPCompIn_map_conj hKu c
    rwa [C3.Layer1.Thm1.map_conj_eq_self_of_mem hc] at this
  have hne : cj c K ≠ K := by
    intro h0
    apply hkc
    have hmem : c * k * c⁻¹ ∈ cj c K := ⟨k, hk, by simp [MulAut.conj_apply]⟩
    rwa [h0] at hmem
  have hle : cj c K ≤ CxK u K := le_inf hK'.1 (Stage1.Thm2.Recip.le_cSec_of_ne hK' hKu hne)
  have hKC : ∀ z ∈ CxK u K, z ∈ centralizer (K : Set G) := fun z hz =>
    Subgroup.mem_centralizer_iff.2 fun k' hk' => (commute_of_mem_cSec hK.quasi hz.2 k' hk').symm
  have hE'K : cj c E ≤ cj c K := Subgroup.map_mono hEK
  have hE'C : cj c E ≤ centralizer (K : Set G) := fun z hz => hKC z (hle (hE'K hz))
  have hE'el := isElementaryAbelian_cj c hEel
  have hE'rk : pRank 2 ↥(cj c E) = pRank 2 ↥E := pRank_cj c E
  have huE' : u ∉ cj c E := by
    intro huE
    have h1 : c⁻¹ * u * c ∈ K := (mem_cj_iff c K u).1 (hE'K huE)
    have hcu : c⁻¹ * u * c = u := by
      have := mem_centralizer_singleton_iff.1 hc
      calc c⁻¹ * u * c = c⁻¹ * (u * c) := by group
        _ = c⁻¹ * (c * u) := by rw [this]
        _ = u := by group
    rw [hcu] at h1
    have := hK.eq_one_of_mem_centralizer hs h1 huK
    have h2 := hu2
    rw [this, orderOf_one] at h2
    omega
  have hxel : CFSG.IsElementaryAbelian 2 ↥(zpowers u) := Th2.isElementaryAbelian_zpowers_of_orderOf_two hu2
  have hcd : CommDisj (cj c E) (zpowers u) := by
    refine ⟨fun e he t ht => ?_, ?_⟩
    · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ht
      have : e ∈ centralizer ({u} : Set G) := (hle (hE'K he)).1
      exact (Commute.zpow_right (mem_centralizer_singleton_iff.1 this) m).symm.eq.symm
    · refine eq_bot_iff.2 fun z hz => ?_
      rcases mem_zpowers_two hu2 hz.2 with h0 | h0
      · simp [h0]
      · exact absurd (h0 ▸ hz.1) huE'
  have hFel := hcd.isElementaryAbelian_sup' hE'el hxel le_rfl le_rfl
  have hFrk : pRank 2 ↥(cj c E ⊔ zpowers u) = pRank 2 ↥E + 1 := by
    rw [hcd.pRank_sup hE'el hxel le_rfl le_rfl, hE'rk, Th2.pRank_zpowers_of_orderOf_two hu2]
  have hFC : cj c E ⊔ zpowers u ≤ centralizer (K : Set G) :=
    sup_le hE'C (zpowers_le.2 huK)
  have hcd2 : CommDisj E (cj c E ⊔ zpowers u) := by
    refine ⟨fun e he f hf => ?_, ?_⟩
    · exact Subgroup.mem_centralizer_iff.1 (hFC hf) e (hEK he)
    · refine eq_bot_iff.2 fun z hz => ?_
      have := hK.eq_one_of_mem_centralizer hs (hEK hz.1) (hFC hz.2)
      simp [this]
  have hAel := hcd2.isElementaryAbelian_sup' hEel hFel le_rfl le_rfl
  have hArk : pRank 2 ↥(E ⊔ (cj c E ⊔ zpowers u)) = pRank 2 ↥E + (pRank 2 ↥E + 1) := by
    rw [hcd2.pRank_sup hEel hFel le_rfl le_rfl, hFrk]
  have h4 := pRank_le_top' (E ⊔ (cj c E ⊔ zpowers u))
  omega

include hK in
theorem pumpUpLT_trivial {u : G} {x' : G} {K' : Subgroup G} (hlt : PumpUpLT 2 u K x' K') :
    x' ∈ centralizer (K : Set G) ∧ K' = K := by
  obtain ⟨-, hILo', -, hx'S, hK'⟩ := hlt
  have hx'C : x' ∈ centralizer (K : Set G) := (hK.mem_cSec_iff).1 hx'S
  have hKx' := hK.isPCompIn hILo'.1 hx'C
  obtain ⟨hpump, hKK⟩ := Th2.pumpUp_eq_self hKx'.1 hKx'
  rw [hpump] at hK'
  exact ⟨hx'C, C3.Layer1.PumpH1.eq_of_isPCompIn_self hKK hK'⟩

include hK in
theorem isTwoTerminal_of_central_sylow
    {R : Subgroup G} (hR : IsSylowOf 2 R (centralizer (K : Set G)))
    {u : G} (hu2 : orderOf u = 2) (huR : u ∈ R) (huc : ∀ r ∈ R, r * u = u * r)
    (hrank : 3 ≤ pRank 2 ↥(centralizer ({u} : Set G))) :
    IsTwoTerminal u K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have huK : u ∈ centralizer (K : Set G) := hR.le huR
  have hKu := hK.isPCompIn hu2 huK
  unfold IsTwoTerminal IsPTerminal
  refine ⟨⟨hu2, by simpa [oBound] using hrank, hKu⟩, ?_, ?_⟩
  · intro x' K' hlt
    obtain ⟨-, hK'eq⟩ := hK.pumpUpLT_trivial hlt
    rw [hK'eq]
    exact ⟨Subgroup.centralizer_le_normalizer (K : Set G) huK, ⟨MulEquiv.refl _⟩⟩
  · intro Q' hQ' x' K' hlt hx'Q' hx'c
    obtain ⟨hx'C, hK'eq⟩ := hK.pumpUpLT_trivial hlt
    rw [hK'eq]
    set C : Subgroup G := centralizer ({u} : Set G) ⊓ centralizerSection K (pPrimeCoreOf 2 K) with hC
    have hCK : C ≤ centralizer (K : Set G) := fun z hz => (hK.mem_cSec_iff).1 hz.2
    have hRC : R ≤ C := fun r hr =>
      ⟨mem_centralizer_singleton_iff.2 (huc r hr), (hK.mem_cSec_iff).2 (hR.le hr)⟩
    have hRsyl : IsSylowOf 2 R C := hR.of_le hRC hCK
    have hcard : Nat.card ↥Q' = Nat.card ↥R := hQ'.card_eq.trans hRsyl.card_eq.symm
    have hQ'K : IsSylowOf 2 Q' (centralizer (K : Set G)) :=
      isSylowOf_of_card (hQ'.le.trans hCK) (hcard.trans hR.card_eq)
    have hQ'D : Q' ≤ centralizer ({x'} : Set G) ⊓ centralizerSection K (pPrimeCoreOf 2 K) := fun q hq =>
      ⟨mem_centralizer_singleton_iff.2 (hx'c q hq).symm, (hK.mem_cSec_iff).2 (hQ'K.le hq)⟩
    exact hQ'K.of_le hQ'D (fun z hz => (hK.mem_cSec_iff).1 hz.2)

end TermK

omit [Finite G] in
theorem exists_isSylowOf_ge' {Q R : Subgroup G} (hQ : IsPGroup 2 Q) (hQR : Q ≤ R) :
    ∃ T : Subgroup G, IsSylowOf 2 T R ∧ Q ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ' : IsPGroup 2 (Q.subgroupOf R) := hQ.comap_subtype
  obtain ⟨T', hT'⟩ := hQ'.exists_le_sylow
  refine ⟨(T' : Subgroup R).map R.subtype, ⟨T', rfl⟩, fun q hq => ?_⟩
  exact ⟨⟨q, hQR hq⟩, hT' (show (⟨q, hQR hq⟩ : R) ∈ Q.subgroupOf R from hq), rfl⟩

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer' (K : Subgroup G) :
    normalizer (K : Set G) ≤ normalizer ((centralizer (K : Set G) : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ m ∈ normalizer (K : Set G), ∀ c ∈ centralizer (K : Set G),
      m * c * m⁻¹ ∈ centralizer (K : Set G) := by
    intro m hm c hc
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : m⁻¹ * w * m ∈ K := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hm) w).1 hw
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hc _ hw'
    calc w * (m * c * m⁻¹) = m * ((m⁻¹ * w * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * w * m)) * m⁻¹ := by rw [h1]
      _ = m * c * m⁻¹ * w := by group
  intro c
  exact ⟨fun hc => key n hn c hc, fun hc => by
    have := key n⁻¹ (inv_mem hn) _ hc
    simpa [mul_assoc] using this⟩

structure GoodK (K : Subgroup G) : Prop extends TermK K where
  simple : IsSimpleGroup ↥K
  rank2 : ∃ E : Subgroup G, E ≤ K ∧ CFSG.IsElementaryAbelian 2 ↥E ∧ 2 ≤ pRank 2 ↥E

namespace GoodK

variable {K : Subgroup G} (hK : GoodK K)

include hK in
theorem normal_of_involution (hr4 : pRank 2 G ≤ 4) {u : G} (hu2 : orderOf u = 2)
    (huK : u ∈ centralizer (K : Set G)) :
    ∀ c ∈ centralizer ({u} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
  obtain ⟨E, hEK, hEel, hE2⟩ := hK.rank2
  exact hK.toTermK.normal_of_involution hK.simple hr4 hEK hEel hE2 hu2 huK

include hK in
theorem sylow_centralizer_of_central (hr4 : pRank 2 G ≤ 4) {T' : Subgroup G}
    (hT' : IsSylowOf 2 T' (normalizer (K : Set G))) {u : G} (hu2 : orderOf u = 2)
    (huK : u ∈ centralizer (K : Set G)) (hTu : ∀ t ∈ T', t * u = u * t) :
    IsSylowOf 2 T' (centralizer ({u} : Set G)) := by
  have hTC : T' ≤ centralizer ({u} : Set G) := fun t ht =>
    mem_centralizer_singleton_iff.2 (hTu t ht)
  obtain ⟨S₁, hS₁, hT'S₁⟩ := exists_isSylowOf_ge' hT'.isPGroup hTC
  have hS₁N : S₁ ≤ normalizer (K : Set G) := fun s hs =>
    C3.Layer1.U1a.mem_normalizer_of_norm (M := centralizer ({u} : Set G)) (L := K)
      (hK.normal_of_involution hr4 hu2 huK) (hS₁.le hs)
  have hS₁T : S₁ = T' := hT'.eq_of_le hT'S₁ hS₁N hS₁.isPGroup
  rw [hS₁T] at hS₁
  exact hS₁

include hK in
theorem good_pair (hG : IsKProperSimple G) (h3 : 3 ≤ pRank 2 G) (hr4 : pRank 2 G ≤ 4)
    {T' : Subgroup G} (hT' : IsSylowOf 2 T' (normalizer (K : Set G))) {x : G}
    (hx2 : orderOf x = 2) (hxK : x ∈ centralizer (K : Set G)) (hxT' : x ∈ T')
    (hxc : ∀ t ∈ T', t * x = x * t) :
    IsTwoTerminal x K ∧ IsSylowOf 2 T' (centralizer ({x} : Set G)) ∧
      IsSylowOf 2 (T' ⊓ centralizer (K : Set G)) (centralizer (K : Set G)) ∧
      T' ⊓ CxK x K = T' ⊓ centralizer (K : Set G) ∧
      (∀ u ∈ T' ⊓ CxK x K, (∀ t ∈ T', u * t = t * u) → orderOf u = 2 →
        IsSylowOf 2 T' (centralizer ({u} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCN : centralizer (K : Set G) ≤ normalizer (K : Set G) :=
    Subgroup.centralizer_le_normalizer (K : Set G)
  have hQsyl : IsSylowOf 2 (T' ⊓ centralizer (K : Set G)) (centralizer (K : Set G)) :=
    hT'.inf_of_le_normalizer hCN (normalizer_le_normalizer_centralizer' K)
  have hCxK : T' ⊓ CxK x K = T' ⊓ centralizer (K : Set G) := by
    ext t
    constructor
    · rintro ⟨ht, htC, htS⟩
      exact ⟨ht, (hK.toTermK.mem_cSec_iff).1 htS⟩
    · rintro ⟨ht, htC⟩
      exact ⟨ht, mem_centralizer_singleton_iff.2 (hxc t ht), (hK.toTermK.mem_cSec_iff).2 htC⟩
  refine ⟨?_, hK.sylow_centralizer_of_central hr4 hT' hx2 hxK hxc, hQsyl, hCxK, ?_⟩
  · exact hK.toTermK.isTwoTerminal_of_central_sylow hQsyl hx2 ⟨hxT', hxK⟩
      (fun r hr => hxc r hr.1)
      (TwoThin.rankThreeCentralizers G hG.1 hG.2.1 h3 x hx2)
  · intro u hu hTu hu2
    rw [hCxK] at hu
    exact hK.sylow_centralizer_of_central hr4 hT' hu2 hu.2 (fun t ht => (hTu t ht).symm)

end GoodK

theorem termK_of_twoTerminal (hG : IsKProperSimple G) (h3 : 3 ≤ pRank 2 G)
    (hOdd : ∀ t : G, orderOf t = 2 → pPrimeCore 2 ↥(centralizer ({t} : Set G)) = ⊥)
    {x : G} {K : Subgroup G} (hx : IsTwoTerminal x K) : TermK K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hILo : IsILo 2 x K := hx.1
  have hxo : orderOf x = 2 := hILo.1
  have hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K := hILo.2.2
  have hOx := hOdd x hxo
  have hKq : CFSG.IsQuasisimple ↥K := Th2.P72c.isQuasisimple_of_isPCompIn hKc hOx
  have hKsub : (K.subgroupOf (centralizer ({x} : Set G))).IsSubnormal :=
    Components.mathlib_subnormal_of_chain (TwoThin.isPCompIn_two_iff.mp hKc).2.1
      Subgroup.IsSubnormal.top
  have hOK : pPrimeCore 2 ↥K = ⊥ := pPrimeCore_eq_bot_of_subnormal hKc.1 hKsub hOx
  have hOKG : pPrimeCoreOf 2 K = ⊥ := by
    unfold pPrimeCoreOf
    rw [hOK, Subgroup.map_bot]
  have hev : 2 ∣ Nat.card ↥K := by
    by_contra hodd
    have hodd' : Odd (Nat.card ↥K) := Nat.odd_iff.2 (by omega)
    have hsolv : Group.IsSolvable ↥K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd'
    have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hKq
    have : Group.IsPerfect ↥K := hKq.1
    exact Group.IsPerfect.not_isSolvable ↥K inferInstance
  have hCxK : CxK x K ≤ centralizer (K : Set G) := fun c hc =>
    Subgroup.mem_centralizer_iff.2 fun k hk => (commute_of_mem_cSec hKq hc.2 k hk).symm
  have hCK_cs : centralizer (K : Set G) ≤ centralizerSection K (pPrimeCoreOf 2 K) := fun c hc =>
    C3.Layer1.Back.mem_centralizerSection_of_centralizes
      (fun k hk => (Subgroup.mem_centralizer_iff.1 hc k hk).symm) (TwoThin.pPrimeCoreOf_le K)
  have hxCx : x ∈ CxK x K := ⟨mem_centralizer_singleton_iff.2 rfl, hCK_cs (by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact mem_centralizer_singleton_iff.1 (hKc.1 hk))⟩
  have hxel : CFSG.IsElementaryAbelian 2 ↥(zpowers x) :=
    Th2.isElementaryAbelian_zpowers_of_orderOf_two hxo
  have hxel2 : IsPGroup 2 ↥(zpowers x) := CFSG.IsElementaryAbelian.isPGroup 2 _
  obtain ⟨Q, hQsyl, hxQ'⟩ := exists_isSylowOf_ge' hxel2 (zpowers_le.2 hxCx)
  have hxQ : x ∈ Q := hxQ' (mem_zpowers x)
  have hQ2 : IsPGroup 2 ↥Q := hQsyl.isPGroup
  have hQC : Q ≤ centralizer (K : Set G) := hQsyl.le.trans hCxK
  have hcomp : ∀ u ∈ Q, orderOf u = 2 → IsCompIn (centralizer ({u} : Set G)) K := by
    intro u hu hu2
    have hux : u ∈ CxK x K := hQsyl.le hu
    have hrank : 3 ≤ pRank 2 ↥(centralizer ({u} : Set G)) :=
      TwoThin.rankThreeCentralizers G hG.1 hG.2.1 h3 u hu2
    obtain ⟨J, hJ⟩ := TwoThin.exists_pumpup_of_involution hxo hu2 hKc hux.1 hux.2 hILo hrank
    have htriv : IsTrivialPumpupAt x K u := fun K' hK' => hx.2.1 u K' hK'
    obtain ⟨hJK, hJc⟩ := Th2.P72c.pumpUp_eq_of_pPrimeCore_eq_bot hOx (hOdd u hu2) hJ htriv
    rw [hJK] at hJc
    exact Th2.P72c.isCompIn_of_isPCompIn hJc (hOdd u hu2)
  have hKcomp2 : ∀ u ∈ Q, orderOf u = 2 → IsPCompIn 2 (centralizer ({u} : Set G)) K := by
    intro u hu hu2
    have hKcomp := hcomp u hu hu2
    have hKC : K ≤ centralizer ({u} : Set G) := hKcomp.1
    refine ⟨hKC, CFSG.LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2
      hKcomp.2 fun hle => ?_⟩
    have h1 : Nat.card ↥(K.subgroupOf (centralizer ({u} : Set G))) ∣
        Nat.card ↥(pPrimeCore 2 ↥(centralizer ({u} : Set G))) := Subgroup.card_dvd_of_le hle
    have h2 : Nat.card ↥(K.subgroupOf (centralizer ({u} : Set G))) = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv
    rw [h2] at h1
    have h3' := Nat.Coprime.coprime_dvd_right h1 CFSG.pPrimeCore_coprime_card
    have h4 := Nat.Coprime.eq_one_of_dvd h3' hev
    omega
  obtain ⟨Qs, hQs, hQQs⟩ := exists_isSylowOf_ge' hQ2 hQC
  have hQs2 : IsPGroup 2 ↥Qs := hQs.isPGroup
  have hxQs : x ∈ Qs := hQQs hxQ
  have hW : Qs ⊓ centralizer ({x} : Set G) = Q :=
    hQsyl.eq_of_le (fun q hq => ⟨hQQs hq, hQsyl.le hq |>.1⟩)
      (fun c hc => ⟨hc.2, hCK_cs (hQs.le hc.1)⟩) hQs2.to_inf_left
  have hQsne : Qs ≠ ⊥ := by
    intro h0
    have : x ∈ (⊥ : Subgroup G) := h0 ▸ hxQs
    rw [Subgroup.mem_bot] at this
    have := hxo
    simp_all
  obtain ⟨u, huQs, hu2, huc⟩ := Th2.exists_central_involution hQs2 hQsne
  have huQ : u ∈ Q := by
    rw [← hW]
    exact ⟨huQs, mem_centralizer_singleton_iff.2 (huc x hxQs)⟩
  have huK : u ∈ centralizer (K : Set G) := hQs.le huQs
  have hKu := hKcomp2 u huQ hu2
  obtain ⟨hpumpK, hKK⟩ := Th2.pumpUp_eq_self hKu.1 hKu
  have hrank : 3 ≤ pRank 2 ↥(centralizer ({u} : Set G)) :=
    TwoThin.rankThreeCentralizers G hG.1 hG.2.1 h3 u hu2
  have hILo_u : IsILo 2 u K := ⟨hu2, by simpa [oBound] using hrank, hKu⟩
  have hpump : PumpUpLT 2 x K u K :=
    ⟨hILo, hILo_u, (hQsyl.le huQ).1, (hQsyl.le huQ).2, by rw [hpumpK]; exact hKK⟩
  have hsyl_u := hx.2.2 Q hQsyl u K hpump huQ (fun q hq => huc q (hQQs hq))
  have hQsle : Qs ≤ centralizer ({u} : Set G) ⊓ centralizerSection K (pPrimeCoreOf 2 K) :=
    le_inf (fun c hc => mem_centralizer_singleton_iff.2 (huc c hc).symm)
      (fun c hc => hCK_cs (hQs.le hc))
  have hEq : Qs = Q := hsyl_u.eq_of_le hQQs hQsle hQs2
  rw [hEq] at hQs
  refine ⟨hKq, hOKG, hev, ?_⟩
  intro y' hy2 hyK
  have hyel := Th2.isElementaryAbelian_zpowers_of_orderOf_two hy2
  have hyp : IsPGroup 2 ↥(zpowers y') := CFSG.IsElementaryAbelian.isPGroup 2 _
  obtain ⟨g, hgC, hgW⟩ := Th2.exists_cj_le_of_isSylowOf hQs (zpowers_le.2 hyK) hyp
  have hv : g * y' * g⁻¹ ∈ Q := by
    apply hgW
    rw [Th2.mem_cj_iff]
    have : g⁻¹ * (g * y' * g⁻¹) * g = y' := by group
    rw [this]
    exact mem_zpowers y'
  have hv2 : orderOf (g * y' * g⁻¹) = 2 := by
    rw [CFSG.BenderGlauberman.orderOf_conj_eq]; exact hy2
  have h1 := AS16.isCompIn_conj (hcomp _ hv hv2) g
  have hK : conjugate K g = K := by
    ext k
    rw [AS16.mem_conjugate_iff']
    constructor
    · intro hk
      have hc := Subgroup.mem_centralizer_iff.1 hgC _ hk
      have : g * k * g⁻¹ = k := by
        have h2 : g * (g * k * g⁻¹) = g * k := by
          calc g * (g * k * g⁻¹) = (g * k * g⁻¹) * g := hc.symm
            _ = g * k := by group
        exact mul_left_cancel h2
      rw [this] at hk
      exact hk
    · intro hk
      have hc := Subgroup.mem_centralizer_iff.1 hgC _ hk
      have : g * k * g⁻¹ = k := by rw [← hc]; group
      rw [this]
      exact hk
  have hC : conjugate (centralizer ({g * y' * g⁻¹} : Set G)) g = centralizer ({y'} : Set G) := by
    rw [AS16.conjugate_centralizer_singleton]
    have : g⁻¹ * (g * y' * g⁻¹) * g = y' := by group
    rw [this]
  rwa [hK, hC] at h1

end CFSG.GH74.GLS.EvenSelP
