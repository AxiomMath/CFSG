module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.Defs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812Omega
import CFSG.GroupTheory.PComponentInvert
import CFSG.RankThree.PartTwo.KFacts.K71Coprime
import CFSG.GH74.Generic.BProg.BpGeneral
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneTypeThreeGroup
import CFSG.GroupTheory.CentralizerSup
import CFSG.GroupTheory.NormalizerInfCentralizer
import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812Four
import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient
public import CFSG.Quasithin.Background.B1MoreTwelveA

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open Subgroup
open scoped commutatorElement Pointwise

@[expose] def KFactFieldAutInvert : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    ∀ L : Subgroup X, CFSG.IsComponent L → L.Normal → CFSG.Open.pRank 3 L = 1 →
      ∀ a : X, a ^ 3 = 1 → a ∉ L ⊔ Subgroup.centralizer (L : Set X) →
        ∀ A : Subgroup X, A ≤ L → Nat.card A = 3 → (∀ z ∈ A, a * z = z * a) →
          ∃ t ∈ L, t * a = a * t ∧ ∀ z ∈ A, t * z * t⁻¹ = z⁻¹

private theorem card_pPrimeCore_subgroupOf {X : Type*} [Group X] [Finite X]
    {M K : Subgroup X} (hKM : K ≤ M) (p : ℕ) :
    Nat.card (CFSG.pPrimeCore p ↥(K.subgroupOf M)) =
      Nat.card (CFSG.pPrimeCore p ↥K) := by
  let e : ↥(K.subgroupOf M) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKM
  rw [← CFSG.pPrimeCore_map_iso p e]
  exact (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).symm

private theorem conj_comp_subtype {X : Type*} [Group X] {Xsub : Subgroup X} (c : ↥Xsub) :
    ((MulAut.conj (c : X)).toMonoidHom.comp Xsub.subtype) =
      (Xsub.subtype.comp (MulAut.conj c).toMonoidHom) := by
  ext x
  simp [MulAut.conj_apply]

private theorem map_centralizerSection_core_subgroupOf_le {X : Type*} [Group X] [Finite X]
    {Xsub K : Subgroup X} (hKX : K ≤ Xsub) (p : ℕ) :
    (CFSG.GH74.GLS.centralizerSection (K.subgroupOf Xsub)
      ((CFSG.pPrimeCore p ↥(K.subgroupOf Xsub)).map (K.subgroupOf Xsub).subtype)).map
        Xsub.subtype ≤
      CFSG.GH74.GLS.centralizerSection K ((CFSG.pPrimeCore p ↥K).map K.subtype) := by
  have hcoremap : ((CFSG.pPrimeCore p ↥(K.subgroupOf Xsub)).map
      (K.subgroupOf Xsub).subtype).map Xsub.subtype =
      (CFSG.pPrimeCore p ↥K).map K.subtype :=
    CFSG.GH74.Generic.BProg.map_pPrimeCoreOf_subgroupOf p hKX
  have hKmap : (K.subgroupOf Xsub).map Xsub.subtype = K :=
    Subgroup.map_subgroupOf_eq_of_le hKX
  intro c hc
  obtain ⟨cX, hcX, rfl⟩ := Subgroup.mem_map.mp hc
  obtain ⟨hcK, hcQ, hcComm⟩ := hcX
  have hmapK : K.map (MulAut.conj (cX : X)).toMonoidHom = K := by
    rw [← hKmap, Subgroup.map_map, conj_comp_subtype, ← Subgroup.map_map]
    have h := Subgroup.mem_normalizer_iff_map_conj_eq.mp hcK
    rw [show Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj cX)) (K.subgroupOf Xsub) =
      K.subgroupOf Xsub from h]
  have hmapQ : ((CFSG.pPrimeCore p ↥K).map K.subtype).map
      (MulAut.conj (cX : X)).toMonoidHom = (CFSG.pPrimeCore p ↥K).map K.subtype := by
    rw [← hcoremap, Subgroup.map_map, conj_comp_subtype, ← Subgroup.map_map]
    have h := Subgroup.mem_normalizer_iff_map_conj_eq.mp hcQ
    rw [show Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj cX))
      ((CFSG.pPrimeCore p ↥(K.subgroupOf Xsub)).map (K.subgroupOf Xsub).subtype) =
      (CFSG.pPrimeCore p ↥(K.subgroupOf Xsub)).map (K.subgroupOf Xsub).subtype from h]
  refine ⟨Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmapK,
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmapQ, ?_⟩
  intro k hk
  have hkX : (⟨k, hKX hk⟩ : Xsub) ∈ K.subgroupOf Xsub := Subgroup.mem_subgroupOf.mpr hk
  have hmem : ⁅(⟨k, hKX hk⟩ : Xsub), cX⁆ ∈
      (CFSG.pPrimeCore p ↥(K.subgroupOf Xsub)).map (K.subgroupOf Xsub).subtype :=
    hcComm ⟨k, hKX hk⟩ hkX
  have himg : Xsub.subtype ⁅(⟨k, hKX hk⟩ : Xsub), cX⁆ ∈
      (CFSG.pPrimeCore p ↥K).map K.subtype := by
    rw [← hcoremap]
    exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
  rw [map_commutatorElement] at himg
  simpa using himg

private theorem isSylowOf_map_pPrimeCore {X : Type*} [Group X] [Finite X] {p q : ℕ}
    (hq : q.Prime) {K P Q : Subgroup X} [Q.Normal]
    (hQ : Q = (CFSG.pPrimeCore p ↥K).map K.subtype) (hPK : P ≤ K)
    (hSyl : CFSG.ABGLocalTools.IsSylowOf q P K) :
    CFSG.ABGLocalTools.IsSylowOf q (P.map (QuotientGroup.mk' Q))
      (K.map (QuotientGroup.mk' Q)) := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have hQle : Q ≤ K := by rw [hQ]; exact Subgroup.map_subtype_le _
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hSyl ⊢
  obtain ⟨-, hPp, hPidx⟩ := hSyl
  refine ⟨Subgroup.map_mono hPK, hPp.map _, ?_⟩
  have hKQ : K ⊔ Q = K := sup_eq_left.mpr hQle
  have hidx : (P.map (QuotientGroup.mk' Q)).relIndex (K.map (QuotientGroup.mk' Q)) =
      (P ⊔ Q).relIndex K := by
    rw [Subgroup.relIndex_map_map, QuotientGroup.ker_mk', hKQ]
  rw [hidx]
  exact fun hdvd => hPidx (hdvd.trans (Subgroup.relIndex_dvd_of_le_left (L := K) le_sup_left))

private theorem exists_not_commuting_of_outer (hFA : KFactFieldAutThree)
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hX : CFSG.Open.IsKGroup X)
    {K S : Subgroup X} (hK : CFSG.IsPComponent p K) (hKn : K.Normal)
    (hr : CFSG.Open.pRank 3 K = 1) (hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K))
    (hS3 : IsPGroup 3 S) (hSK : CFSG.ABGLocalTools.IsSylowOf 3 (S ⊓ K) K)
    {a : X} (haS : a ∈ S) (ha3 : a ^ 3 = 1)
    (hout : a ∉ K ⊔ CFSG.GH74.GLS.centralizerSection K ((CFSG.pPrimeCore p ↥K).map K.subtype)) :
    ∃ x ∈ S ⊓ K, a * x ≠ x * a := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : K.Normal := hKn
  let Q : Subgroup X := (CFSG.pPrimeCore p ↥K).map K.subtype
  let Xq := X ⧸ Q
  let Kq : Subgroup Xq := K.map (QuotientGroup.mk' Q)
  let aq : Xq := QuotientGroup.mk' Q a
  let P : Subgroup X := S ⊓ K
  let Pq : Subgroup Xq := P.map (QuotientGroup.mk' Q)
  haveI hQn : Q.Normal := by
    change (Subgroup.map K.subtype (CFSG.pPrimeCore p ↥K)).Normal
    exact ConjAct.normal_of_characteristic_of_normal
  have hXq : CFSG.Open.IsKGroup Xq := hX.quotient Q
  have hKqdata := image_isComponent_pRank hp hK hKn (Q := Q) rfl hcop
  obtain ⟨hKqn, hKqc, hKqr⟩ := hKqdata
  have hPq : CFSG.ABGLocalTools.IsSylowOf 3 Pq Kq :=
    isSylowOf_map_pPrimeCore (p := p) Nat.prime_three (K := K) (P := P) (Q := Q) rfl
      inf_le_right hSK
  have haq3 : aq ^ 3 = 1 := by
    change (QuotientGroup.mk' Q a) ^ 3 = 1
    rw [← map_pow, ha3, map_one]
  have haq1 : aq ≠ 1 := by
    intro h1
    apply hout
    refine mem_sup_centralizerSection_of_mem_map_sup_centralizer hKn (Q := Q) rfl ?_
    change aq ∈ Kq ⊔ Subgroup.centralizer (Kq : Set Xq)
    rw [h1]
    exact Subgroup.mem_sup_left (Kq.one_mem)
  have houtq : aq ∉ Kq ⊔ Subgroup.centralizer (Kq : Set Xq) :=
    fun hmem => hout (mem_sup_centralizerSection_of_mem_map_sup_centralizer hKn (Q := Q) rfl hmem)
  have hPnorm : P.map (MulAut.conj a).toMonoidHom = P := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro z ⟨x, hx, rfl⟩
      change a * x * a⁻¹ ∈ P
      exact ⟨S.mul_mem (S.mul_mem haS (Subgroup.mem_inf.mp hx).1) (S.inv_mem haS),
        hKn.conj_mem x (Subgroup.mem_inf.mp hx).2 a⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj a).injective]
  have haP : a ∈ Subgroup.normalizer (P : Set X) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hPnorm
  have hcomp : ((MulAut.conj aq).toMonoidHom.comp (QuotientGroup.mk' Q)) =
      ((QuotientGroup.mk' Q).comp (MulAut.conj a).toMonoidHom) := by
    ext x
    change (QuotientGroup.mk' Q a) * (QuotientGroup.mk' Q) x *
        (QuotientGroup.mk' Q a)⁻¹ =
      (QuotientGroup.mk' Q) (a * x) * ((QuotientGroup.mk' Q) a)⁻¹
    rw [map_mul]
  have hPqnorm : Pq.map (MulAut.conj aq).toMonoidHom = Pq := by
    change (P.map (QuotientGroup.mk' Q)).map (MulAut.conj aq).toMonoidHom =
      P.map (QuotientGroup.mk' Q)
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hPnorm]
  have haqP : aq ∈ Subgroup.normalizer (Pq : Set Xq) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hPqnorm
  obtain ⟨xq, hxqP, hneq⟩ :=
    hFA Xq hXq Kq hKqc hKqn (hKqr.trans hr) aq (orderOf_eq_prime haq3 haq1) houtq
      Pq hPq haqP
  obtain ⟨x, hxP, hxq⟩ := Subgroup.mem_map.mp hxqP
  refine ⟨x, hxP, ?_⟩
  intro hcomm
  apply hneq
  rw [← hxq, ← map_mul, ← map_mul, hcomm]

private theorem mem_of_pow_three_eq_one_of_cyclic {X : Type} [Group X] [Finite X]
    {P A : Subgroup X} [IsCyclic ↥P] (hAP : A ≤ P) (hA3 : Nat.card A = 3)
    {z : X} (hzP : z ∈ P) (hz3 : z ^ 3 = 1) : z ∈ A := by
  obtain ⟨b, hb3⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) 3 (by rw [hA3])
  have hbP : (b : X) ∈ P := hAP b.2
  have hb3' : orderOf (b : X) = 3 := (Subgroup.orderOf_coe b).trans hb3
  exact (Subgroup.zpowers_le.mpr b.2)
    (CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27.mem_zpowers_of_pow_three_eq_one
      (Q := P) (z := (b : X)) inferInstance hb3' hbP hzP hz3)

private theorem commutator_ne_one_of_generator {X : Type*} [Group X]
    {P : Subgroup X} {a x y : X} (hzy : Subgroup.zpowers y = P)
    (hxP : x ∈ P) (hneq : a * x ≠ x * a) : y * a * y⁻¹ ≠ a := by
  intro h
  apply hneq
  have hay : a * y = y * a := by
    calc a * y = (y * a * y⁻¹) * y := by rw [h]
      _ = y * a := by group
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hzy ▸ hxP)
  rw [← hm]
  exact (Commute.zpow_right hay m).eq

private theorem exists_generator_not_commuting {X : Type*} [Group X]
    {P : Subgroup X} (hPcyc : IsCyclic ↥P) {a x : X} (hxP : x ∈ P)
    (hneq : a * x ≠ x * a) :
    ∃ y : X, Subgroup.zpowers y = P ∧ a * y ≠ y * a := by
  obtain ⟨y, hzy⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top P).mp hPcyc
  refine ⟨y, hzy, ?_⟩
  intro hay
  apply hneq
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hzy ▸ hxP)
  rw [← hm]
  exact (Commute.zpow_right hay m).eq

private theorem mem_normalizer_inf_of_mem_of_normal {X : Type*} [Group X] [Finite X]
    {K S : Subgroup X} (hKn : K.Normal) {a : X} (haS : a ∈ S) :
    a ∈ Subgroup.normalizer ((S ⊓ K : Subgroup X) : Set X) := by
  have hPnorm : (S ⊓ K).map (MulAut.conj a).toMonoidHom = S ⊓ K := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro z ⟨x, hx, rfl⟩
      change a * x * a⁻¹ ∈ S ⊓ K
      exact ⟨S.mul_mem (S.mul_mem haS (Subgroup.mem_inf.mp hx).1) (S.inv_mem haS),
        hKn.conj_mem x (Subgroup.mem_inf.mp hx).2 a⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj a).injective]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hPnorm

theorem exists_mem_inf_conj_mul_inv_mem_of_not_mem_sup (hFA : KFactFieldAutThree)
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hX : CFSG.Open.IsKGroup X)
    {K S A : Subgroup X} (hK : CFSG.IsPComponent p K) (hKn : K.Normal)
    (hr : CFSG.Open.pRank 3 K = 1) (hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K))
    (hS3 : IsPGroup 3 S) (hSK : CFSG.ABGLocalTools.IsSylowOf 3 (S ⊓ K) K)
    (hAK : A ≤ K) (hAS : A ≤ S) (hA3 : Nat.card A = 3)
    {a : X} (haS : a ∈ S) (ha3 : a ^ 3 = 1)
    (hout : a ∉ K ⊔ CFSG.GH74.GLS.centralizerSection K ((CFSG.pPrimeCore p ↥K).map K.subtype)) :
    ∃ y ∈ S ⊓ K, y * a * y⁻¹ * a⁻¹ ∈ A ∧ y * a * y⁻¹ ≠ a := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hxSK, hxne⟩ :=
    exists_not_commuting_of_outer hFA hp hX hK hKn hr hcop hS3 hSK haS ha3 hout
  have hPcyc : IsCyclic ↥(S ⊓ K) := by
    refine CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_of_pRank_le_one
      Nat.prime_three (by norm_num) hSK.isPGroup ?_
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) inf_le_right).trans (le_of_eq hr)
  obtain ⟨y, hzy, hne⟩ := exists_generator_not_commuting hPcyc hxSK hxne
  have hyP : y ∈ S ⊓ K := hzy ▸ Subgroup.mem_zpowers y
  have haP : a ∈ Subgroup.normalizer ((S ⊓ K : Subgroup X) : Set X) :=
    mem_normalizer_inf_of_mem_of_normal hKn haS
  have hcomm3 : ⁅a, y⁆ ^ 3 = 1 :=
    CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27.commutator_pow_three_of_isCyclic
      (Q := S ⊓ K) hPcyc hSK.isPGroup haP ha3 hyP
  have hz3 : (y * a * y⁻¹ * a⁻¹) ^ 3 = 1 := by
    have hz_eq : y * a * y⁻¹ * a⁻¹ = ⁅a, y⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [hz_eq, inv_pow, hcomm3, inv_one]
  have hzP : y * a * y⁻¹ * a⁻¹ ∈ S ⊓ K := by
    have h1 : a * y⁻¹ * a⁻¹ ∈ S ⊓ K :=
      (Subgroup.mem_normalizer_iff.mp haP y⁻¹).mp ((S ⊓ K).inv_mem hyP)
    have h2 : y * (a * y⁻¹ * a⁻¹) ∈ S ⊓ K := (S ⊓ K).mul_mem hyP h1
    simpa [mul_assoc] using h2
  have hzA : y * a * y⁻¹ * a⁻¹ ∈ A :=
    mem_of_pow_three_eq_one_of_cyclic (le_inf hAS hAK) hA3 hzP hz3
  have hz1 : y * a * y⁻¹ ≠ a := commutator_ne_one_of_generator hzy hxSK hxne
  exact ⟨y, hyP, hzA, hz1⟩

private theorem card_map_quotient_core_eq_three {X : Type} [Group X] [Finite X] {p : ℕ}
    {K A Q : Subgroup X} [Q.Normal] (hQ : Q = (CFSG.pPrimeCore p ↥K).map K.subtype)
    (hAK : A ≤ K) (hA3 : Nat.card A = 3)
    (hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K)) :
    Nat.card (A.map (QuotientGroup.mk' Q)) = 3 := by
  have hdvd : Nat.card (A.map (QuotientGroup.mk' Q)) ∣ 3 := by
    rw [← hA3]
    exact Subgroup.card_map_dvd A (QuotientGroup.mk' Q)
  have hne : Nat.card (A.map (QuotientGroup.mk' Q)) ≠ 1 := by
    intro h1
    have hbot : A.map (QuotientGroup.mk' Q) = ⊥ := Subgroup.card_eq_one.mp h1
    have hAQ : A ≤ Q := by
      intro z hz
      have hzq : QuotientGroup.mk' Q z ∈ A.map (QuotientGroup.mk' Q) :=
        Subgroup.mem_map_of_mem _ hz
      rw [hbot, Subgroup.mem_bot] at hzq
      exact (QuotientGroup.eq_one_iff z).mp hzq
    have hAle : A ≤ ⊥ := by
      rw [← CFSG.GroupTheory.inf_pPrimeCore_map_eq_bot (K := K) hA3 hcop]
      exact le_inf le_rfl (hQ ▸ hAQ)
    have hdvd : Nat.card A ∣ 1 := by simpa using Subgroup.card_dvd_of_le hAle
    rw [hA3] at hdvd
    omega
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact absurd h hne
  · exact h

private theorem exists_quotient_inverting (hFI : KFactFieldAutInvert)
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hX : CFSG.Open.IsKGroup X)
    {K A Q : Subgroup X} [Q.Normal] (hQ : Q = (CFSG.pPrimeCore p ↥K).map K.subtype)
    (hK : CFSG.IsPComponent p K) (hKn : K.Normal)
    (hr : CFSG.Open.pRank 3 K = 1) (hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K))
    (hAK : A ≤ K) (hA3 : Nat.card A = 3)
    {a : X} (ha3 : a ^ 3 = 1)
    (hout : a ∉ K ⊔ CFSG.GH74.GLS.centralizerSection K ((CFSG.pPrimeCore p ↥K).map K.subtype))
    (haA : ∀ z ∈ A, a * z = z * a) :
    ∃ tq ∈ K.map (QuotientGroup.mk' Q),
      tq * QuotientGroup.mk' Q a = QuotientGroup.mk' Q a * tq ∧
      (∀ z ∈ A.map (QuotientGroup.mk' Q), tq * z * tq⁻¹ = z⁻¹) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : K.Normal := hKn
  let Xq := X ⧸ Q
  let Kq : Subgroup Xq := K.map (QuotientGroup.mk' Q)
  let aq : Xq := QuotientGroup.mk' Q a
  let Aq : Subgroup Xq := A.map (QuotientGroup.mk' Q)
  have hXq : CFSG.Open.IsKGroup Xq := hX.quotient Q
  have hKqdata := image_isComponent_pRank hp hK hKn (Q := Q) hQ hcop
  obtain ⟨hKqn, hKqc, hKqr⟩ := hKqdata
  have haq3 : aq ^ 3 = 1 := by
    change (QuotientGroup.mk' Q a) ^ 3 = 1
    rw [← map_pow, ha3, map_one]
  have haq1 : aq ≠ 1 := by
    intro h1
    apply hout
    have hmem : aq ∈ Kq ⊔ Subgroup.centralizer (Kq : Set Xq) := by
      rw [h1]
      exact Subgroup.mem_sup_left (Kq.one_mem)
    have h := mem_sup_centralizerSection_of_mem_map_sup_centralizer hKn (Q := Q) hQ hmem
    rw [hQ] at h
    exact h
  have houtq : aq ∉ Kq ⊔ Subgroup.centralizer (Kq : Set Xq) := by
    intro hmem
    have h := mem_sup_centralizerSection_of_mem_map_sup_centralizer hKn (Q := Q) hQ hmem
    rw [hQ] at h
    exact hout h
  have hAqK : Aq ≤ Kq := Subgroup.map_mono hAK
  have hAq3 : Nat.card Aq = 3 := card_map_quotient_core_eq_three hQ hAK hA3 hcop
  have hAqcomm : ∀ z ∈ Aq, aq * z = z * aq := by
    intro z hz
    obtain ⟨zX, hzA, rfl⟩ := Subgroup.mem_map.mp hz
    change QuotientGroup.mk' Q a * QuotientGroup.mk' Q zX =
      QuotientGroup.mk' Q zX * QuotientGroup.mk' Q a
    rw [← map_mul, ← map_mul, haA zX hzA]
  exact hFI Xq hXq Kq hKqc hKqn (hKqr.trans hr) aq haq3 houtq Aq hAqK hAq3 hAqcomm

private theorem map_quotient_centralizes {X : Type} [Group X] [Finite X] {p : ℕ}
    {K B Q : Subgroup X} [Q.Normal] (hQ : Q = (CFSG.pPrimeCore p ↥K).map K.subtype)
    (hBK : ⁅B, K⁆ ≤ (CFSG.pPrimeCore p ↥K).map K.subtype) :
    ∀ b ∈ B.map (QuotientGroup.mk' Q), ∀ k ∈ K.map (QuotientGroup.mk' Q), b * k = k * b := by
  intro b hb k hk
  obtain ⟨bX, hbB, rfl⟩ := Subgroup.mem_map.mp hb
  obtain ⟨kX, hkK, rfl⟩ := Subgroup.mem_map.mp hk
  have hcomm : ⁅bX, kX⁆ ∈ Q := hQ ▸ (Subgroup.commutator_le.mp hBK) bX hbB kX hkK
  have hQ1 : QuotientGroup.mk' Q ⁅bX, kX⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hcomm
  change QuotientGroup.mk' Q bX * QuotientGroup.mk' Q kX =
    QuotientGroup.mk' Q kX * QuotientGroup.mk' Q bX
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, hQ1]


private theorem D_isPGroup_and_normalizes {X : Type} [Group X] {p : ℕ}
    {K B D Q : Subgroup X} [Q.Normal] (hQ : Q = (CFSG.pPrimeCore p ↥K).map K.subtype)
    (hKn : K.Normal) (hBK : ⁅B, K⁆ ≤ (CFSG.pPrimeCore p ↥K).map K.subtype)
    (hB3 : IsPGroup 3 B) {a : X} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (haB : ∀ b ∈ B, a * b = b * a) (hD : D = Subgroup.zpowers a ⊔ B) :
    IsPGroup 3 D ∧ D ≤ Subgroup.normalizer (K : Set X) ∧
      D ≤ Subgroup.normalizer (Q : Set X) := by
  subst hD
  have hZa : IsPGroup 3 (Subgroup.zpowers a) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
    norm_num
  have hD3 : IsPGroup 3 ↥(Subgroup.zpowers a ⊔ B) := by
    refine hZa.to_sup_of_normal_right' hB3 ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer (B : Set X)
      (Subgroup.mem_centralizer_iff.mpr fun b hb => (haB b hb).symm)
  have hQle : Q ≤ K := by rw [hQ]; exact Subgroup.map_subtype_le _
  have hBKnorm : B ≤ Subgroup.normalizer (K : Set X) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb k hk
    have hcomm : ⁅b, k⁆ ∈ Q := hQ ▸ (Subgroup.commutator_le.mp hBK) b hb k hk
    have h1 : b * k * b⁻¹ = ⁅b, k⁆ * k := by rw [commutatorElement_def]; group
    rw [h1]
    exact K.mul_mem (hQle hcomm) hk
  have hDK : Subgroup.zpowers a ⊔ B ≤ Subgroup.normalizer (K : Set X) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer_of_normal (Subgroup.mem_top a)))
      hBKnorm
  exact ⟨hD3, hDK, fun _ _ => Subgroup.le_normalizer_of_normal (Subgroup.mem_top _)⟩

private theorem D_bar_commutes {X : Type} [Group X] [Finite X] {p : ℕ}
    {K B D Q : Subgroup X} [Q.Normal] (hQ : Q = (CFSG.pPrimeCore p ↥K).map K.subtype)
    {a : X} (ha3 : a ^ 3 = 1) (hD : D = Subgroup.zpowers a ⊔ B)
    {tq : X ⧸ Q} (htqcomm : tq * QuotientGroup.mk' Q a = QuotientGroup.mk' Q a * tq)
    (htqB : ∀ b ∈ B.map (QuotientGroup.mk' Q), tq * b = b * tq) :
    ∀ d : ↥D, QuotientGroup.mk' Q (d : X) * tq = tq * QuotientGroup.mk' Q (d : X) := by
  have hDbarcent : D.map (QuotientGroup.mk' Q) ≤
      Subgroup.centralizer ({tq} : Set (X ⧸ Q)) := by
    have haqCent : QuotientGroup.mk' Q a ∈
        Subgroup.centralizer ({tq} : Set (X ⧸ Q)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact htqcomm.symm
    have hBqCent : B.map (QuotientGroup.mk' Q) ≤
        Subgroup.centralizer ({tq} : Set (X ⧸ Q)) := by
      intro b hb
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (htqB b hb).symm
    rw [hD, Subgroup.map_sup, MonoidHom.map_zpowers]
    exact sup_le (Subgroup.zpowers_le.mpr haqCent) hBqCent
  intro d
  have hmem : QuotientGroup.mk' Q (d : X) ∈ D.map (QuotientGroup.mk' Q) :=
    Subgroup.mem_map_of_mem _ d.2
  exact Subgroup.mem_centralizer_singleton_iff.mp (hDbarcent hmem)

private theorem exists_coprime_fixed_lift {X : Type} [Group X] [Finite X] {p : ℕ}
    {K D Q : Subgroup X} [Q.Normal] (hQ : Q = (CFSG.pPrimeCore p ↥K).map K.subtype)
    (hKn : K.Normal) (hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K))
    (hD3 : IsPGroup 3 D) (hDK : D ≤ Subgroup.normalizer (K : Set X))
    (hDQ : D ≤ Subgroup.normalizer (Q : Set X))
    {tq : X ⧸ Q} (htqK : tq ∈ K.map (QuotientGroup.mk' Q))
    (hDbarcomm : ∀ d : ↥D, QuotientGroup.mk' Q (d : X) * tq =
      tq * QuotientGroup.mk' Q (d : X)) :
    ∃ y' : ↥K, QuotientGroup.mk' Q (y' : X) = tq ∧
      ∀ d : ↥D, (d : X) * (y' : X) * (d : X)⁻¹ = (y' : X) := by
  classical
  haveI : K.Normal := hKn
  have hNsub : Q.subgroupOf K = CFSG.pPrimeCore p ↥K := by
    rw [hQ]
    change Subgroup.comap K.subtype (Subgroup.map K.subtype (CFSG.pPrimeCore p ↥K)) =
      CFSG.pPrimeCore p ↥K
    rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  haveI : (Q.subgroupOf K).Normal := by
    rw [hNsub]
    exact CFSG.pPrimeCore_normal
  have hNcop : ¬ 3 ∣ Nat.card (Q.subgroupOf K) := by
    rw [hNsub]
    exact hcop
  let φ : ↥D →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hDK)
  have hφN : ∀ d : ↥D, ∀ n ∈ Q.subgroupOf K, (φ d) n ∈ Q.subgroupOf K := by
    intro d n hn
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    change (d : X) * (n : X) * (d : X)⁻¹ ∈ Q
    exact (Subgroup.mem_normalizer_iff.mp (hDQ d.2) (n : X)).mp hn
  obtain ⟨yX, hyK, hyq⟩ := Subgroup.mem_map.mp htqK
  let y : ↥K := ⟨yX, hyK⟩
  have hy : ∀ d : ↥D, (((φ d) y : ↥K) : ↥K ⧸ Q.subgroupOf K) =
      (y : ↥K ⧸ Q.subgroupOf K) := by
    intro d
    rw [QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    have hφy : QuotientGroup.mk' Q (((φ d) y : ↥K) : X) = tq := by
      change QuotientGroup.mk' Q ((d : X) * (yX : X) * (d : X)⁻¹) = tq
      calc QuotientGroup.mk' Q ((d : X) * (yX : X) * (d : X)⁻¹)
          = (QuotientGroup.mk' Q (d : X) * tq) *
              (QuotientGroup.mk' Q (d : X))⁻¹ := by
              rw [map_mul, map_mul, map_inv, hyq]
        _ = (tq * QuotientGroup.mk' Q (d : X)) *
              (QuotientGroup.mk' Q (d : X))⁻¹ := by rw [hDbarcomm d]
        _ = tq := by group
    have h1 : QuotientGroup.mk' Q ((((φ d) y : ↥K) : X)⁻¹ * (y : X)) = 1 := by
      rw [map_mul, map_inv, hφy, hyq, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨y', hy'same, hy'fix⟩ :=
    CFSG.RankThree.PartTwo.KFacts.exists_fixed_of_coprime hD3 φ (Q.subgroupOf K) hNcop
      hφN y hy
  have hy'eq : QuotientGroup.mk' Q (y' : X) = tq := by
    have hmem : ((y' : ↥K)⁻¹ * y) ∈ Q.subgroupOf K := (QuotientGroup.eq.mp hy'same)
    have hQmem : ((y' : X)⁻¹ * (y : X)) ∈ Q := Subgroup.mem_subgroupOf.mp hmem
    have h1 : QuotientGroup.mk' Q ((y' : X)⁻¹ * (y : X)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hQmem
    rw [map_mul, map_inv, hyq] at h1
    exact inv_mul_eq_one.mp h1
  refine ⟨y', hy'eq, ?_⟩
  intro d
  have h := congrArg Subtype.val (hy'fix d)
  simpa [φ] using h

private theorem lift_inverts_mod_core {X : Type} [Group X] {Q A : Subgroup X} [Q.Normal]
    {t : X} {tq : X ⧸ Q} (ht1q : QuotientGroup.mk' Q t = tq)
    (htqinv : ∀ z ∈ A.map (QuotientGroup.mk' Q), tq * z * tq⁻¹ = z⁻¹) :
    ∀ z ∈ A, (t * z * t⁻¹) * z ∈ Q := by
  intro z hz
  have hzq : QuotientGroup.mk' Q z ∈ A.map (QuotientGroup.mk' Q) := Subgroup.mem_map_of_mem _ hz
  have hInv := htqinv _ hzq
  have h1 : QuotientGroup.mk' Q (t * z * t⁻¹) = (QuotientGroup.mk' Q z)⁻¹ := by
    rw [map_mul, map_mul, map_inv, ht1q, hInv]
  have h2 : QuotientGroup.mk' Q ((t * z * t⁻¹) * z) = 1 := by
    rw [map_mul, h1]
    exact inv_mul_cancel _
  exact (QuotientGroup.eq_one_iff _).mp h2


private theorem commute_of_conj_eq_self {X : Type*} [Group X] {t d : X}
    (h : d * t * d⁻¹ = t) : t * d = d * t := by
  have h2 : d * t = t * d := by
    calc d * t = (d * t * d⁻¹) * d := by group
      _ = t * d := by rw [h]
  exact h2.symm

private theorem exists_D0_conj_eq {X : Type} [Group X] [Finite X] {p : ℕ}
    {K A B D Q : Subgroup X} [Q.Normal] (hQ : Q = (CFSG.pPrimeCore p ↥K).map K.subtype)
    (hAK : A ≤ K) (hA3 : Nat.card A = 3)
    (hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K)) {a : X}
    (hD : D = Subgroup.zpowers a ⊔ B) (hA_cent_D : A ≤ Subgroup.centralizer (D : Set X))
    {t : X} (htcentD : t ∈ Subgroup.centralizer (D : Set X))
    (hmod : ∀ z ∈ A, (t * z * t⁻¹) * z ∈ Q) :
    ∃ d ∈ Q ⊓ Subgroup.centralizer (D : Set X),
      A.map (MulAut.conj t).toMonoidHom = A.map (MulAut.conj d).toMonoidHom := by
  let D0 : Subgroup X := Q ⊓ Subgroup.centralizer (D : Set X)
  let C : Subgroup X := K ⊓ Subgroup.centralizer (D : Set X)
  have hAC : A ≤ C := le_inf hAK hA_cent_D
  have hCQ : C ≤ Subgroup.normalizer (Q : Set X) :=
    inf_le_left.trans (Subgroup.le_normalizer_of_normal (H := Q))
  have hCD : C ≤ Subgroup.centralizer (D : Set X) := inf_le_right
  have hD0norm : C ≤ Subgroup.normalizer (D0 : Set X) :=
    fun c hc => CFSG.GroupTheory.mem_normalizer_inf_centralizer
      (Subgroup.centralizer_le_normalizer (D : Set X) (hCD hc)) (hCQ hc)
  have hAnorm : A ≤ Subgroup.normalizer (D0 : Set X) :=
    fun c hc => CFSG.GroupTheory.mem_normalizer_inf_centralizer
      (Subgroup.centralizer_le_normalizer (D : Set X) (hA_cent_D hc))
      (Subgroup.le_normalizer_of_normal (H := Q) (Subgroup.mem_top c))
  have hQcop : ¬ 3 ∣ Nat.card Q := by
    rw [hQ, Subgroup.card_map_of_injective K.subtype_injective]
    exact hcop
  have hD0cop : ¬ 3 ∣ Nat.card (D0 : Subgroup X) :=
    fun h => hQcop (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hADdisj : Disjoint A D0 := by
    rw [disjoint_iff]
    refine le_antisymm ?_ bot_le
    calc A ⊓ D0 ≤ A ⊓ Q := inf_le_inf (le_refl A) (inf_le_left : D0 ≤ Q)
      _ = ⊥ := by
        rw [hQ]
        exact CFSG.GroupTheory.inf_pPrimeCore_map_eq_bot (K := K) hA3 hcop
  have hADcard : Nat.card (A ⊔ D0 : Subgroup X) = 3 * Nat.card D0 := by
    have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      D0 A hAnorm hADdisj.symm
    rw [sup_comm, hcard, hA3]
    exact Nat.mul_comm (Nat.card D0) 3
  let P : Subgroup X := A.map (MulAut.conj t).toMonoidHom
  have hPcard : Nat.card P = 3 := by
    rw [show P = A.map (MulAut.conj t).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (MulAut.conj t).injective, hA3]
  have hP3 : IsPGroup 3 ↥P := IsPGroup.of_card (n := 1) (by rw [hPcard]; norm_num)
  have hPAD : P ≤ A ⊔ D0 := by
    intro z hz
    obtain ⟨zX, hzA, rfl⟩ := Subgroup.mem_map.mp hz
    have hcommQ : ((t : X) * zX * t⁻¹) * zX ∈ Q := hmod zX hzA
    have hcent : ((t : X) * zX * t⁻¹) * zX ∈ Subgroup.centralizer (D : Set X) :=
      (Subgroup.centralizer (D : Set X)).mul_mem
        ((Subgroup.centralizer (D : Set X)).mul_mem
          ((Subgroup.centralizer (D : Set X)).mul_mem htcentD (hA_cent_D hzA))
          ((Subgroup.centralizer (D : Set X)).inv_mem htcentD))
        (hA_cent_D hzA)
    have hmemD0 : ((t : X) * zX * t⁻¹) * zX ∈ D0 := ⟨hcommQ, hcent⟩
    have hz' : t * zX * t⁻¹ = (((t : X) * zX * t⁻¹) * zX) * zX⁻¹ := by group
    change t * zX * t⁻¹ ∈ A ⊔ D0
    rw [hz', sup_comm]
    exact Subgroup.mul_mem_sup hmemD0 (A.inv_mem hzA)
  obtain ⟨d, hdD0, hconj⟩ :=
    CFSG.GroupTheory.exists_mem_inf_conj_eq_of_isSylowOf hAC hD0norm hADcard hD0cop
      hA3 hPcard hP3 hPAD
  exact ⟨d, hdD0, hconj⟩

private theorem exists_inverting_final {X : Type} [Group X] [Finite X] {p : ℕ}
    {K A B D Q : Subgroup X} [Q.Normal] (hQ : Q = (CFSG.pPrimeCore p ↥K).map K.subtype)
    (hAK : A ≤ K) (hA3 : Nat.card A = 3)
    (hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K)) {a : X}
    (hD : D = Subgroup.zpowers a ⊔ B)
    {t : X} (htK : t ∈ K) (htcentD : t ∈ Subgroup.centralizer (D : Set X))
    (hmod : ∀ z ∈ A, (t * z * t⁻¹) * z ∈ Q)
    (hconj : ∃ d ∈ Q ⊓ Subgroup.centralizer (D : Set X),
      A.map (MulAut.conj t).toMonoidHom = A.map (MulAut.conj d).toMonoidHom) :
    ∃ u ∈ K, u * a = a * u ∧ (∀ b ∈ B, u * b = b * u) ∧
      ∀ z ∈ A, u * z * u⁻¹ = z⁻¹ := by
  obtain ⟨d, hdD0, hconj⟩ := hconj
  have hQle : Q ≤ K := by rw [hQ]; exact Subgroup.map_subtype_le _
  let C : Subgroup X := K ⊓ Subgroup.centralizer (D : Set X)
  have htC : t ∈ C := ⟨htK, htcentD⟩
  have hdN : d ∈ Q := hdD0.1
  have hdC : d ∈ C := ⟨hQle hdD0.1, hdD0.2⟩
  have hAN : A ⊓ Q = ⊥ := by
    rw [hQ]
    exact CFSG.GroupTheory.inf_pPrimeCore_map_eq_bot (K := K) hA3 hcop
  obtain ⟨u, huC, huinv⟩ :=
    CFSG.GroupTheory.exists_inverting_of_conj_eq
      (Subgroup.le_normalizer_of_normal (H := Q)) hAK htC hdN hdC hAN hmod hconj
  refine ⟨u, huC.1, ?_, ?_, ?_⟩
  · have haD : a ∈ D := hD ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
    exact ((Subgroup.mem_centralizer_iff.mp huC.2) a haD).symm
  · intro b hb
    have hbD : b ∈ D := hD ▸ Subgroup.mem_sup_right hb
    exact ((Subgroup.mem_centralizer_iff.mp huC.2) b hbD).symm
  · exact huinv


private theorem A_le_centralizer_D {X : Type*} [Group X] {A B D : Subgroup X} {a : X}
    (hD : D = Subgroup.zpowers a ⊔ B) (haA : ∀ z ∈ A, a * z = z * a)
    (hAB : ∀ z ∈ A, ∀ b ∈ B, z * b = b * z) :
    A ≤ Subgroup.centralizer (D : Set X) := by
  have hA_cent_a : A ≤ Subgroup.centralizer (Subgroup.zpowers a : Set X) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (show Commute a z from haA z hz) i).eq
  have hA_cent_B : A ≤ Subgroup.centralizer (B : Set X) :=
    fun z hz => Subgroup.mem_centralizer_iff.mpr fun b hb => (hAB z hz b hb).symm
  rw [hD, CFSG.centralizer_sup_eq]
  exact le_inf hA_cent_a hA_cent_B

theorem exists_inv_mem_centralizer_of_not_mem_sup (hFI : KFactFieldAutInvert)
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hX : CFSG.Open.IsKGroup X)
    {K A B : Subgroup X} (hK : CFSG.IsPComponent p K) (hKn : K.Normal)
    (hr : CFSG.Open.pRank 3 K = 1) (hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K))
    (hAK : A ≤ K) (hA3 : Nat.card A = 3)
    (hB3 : IsPGroup 3 B) (hBK : ⁅B, K⁆ ≤ (CFSG.pPrimeCore p ↥K).map K.subtype)
    (hAB : ∀ z ∈ A, ∀ b ∈ B, z * b = b * z)
    {a : X} (ha3 : a ^ 3 = 1)
    (hout : a ∉ K ⊔ CFSG.GH74.GLS.centralizerSection K ((CFSG.pPrimeCore p ↥K).map K.subtype))
    (haA : ∀ z ∈ A, a * z = z * a) (haB : ∀ b ∈ B, a * b = b * a) :
    ∃ t ∈ K, t * a = a * t ∧ (∀ b ∈ B, t * b = b * t) ∧ ∀ z ∈ A, t * z * t⁻¹ = z⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : K.Normal := hKn
  let Q : Subgroup X := (CFSG.pPrimeCore p ↥K).map K.subtype
  haveI hQn : Q.Normal := by
    change (Subgroup.map K.subtype (CFSG.pPrimeCore p ↥K)).Normal
    exact ConjAct.normal_of_characteristic_of_normal
  have hQ : Q = (CFSG.pPrimeCore p ↥K).map K.subtype := rfl
  obtain ⟨tq, htqK, htqcomm, htqinv⟩ :=
    exists_quotient_inverting (hFI := hFI) (hp := hp) (hX := hX) (hQ := hQ)
      (hK := hK) (hKn := hKn) (hr := hr) (hcop := hcop) (hAK := hAK) (hA3 := hA3)
      (ha3 := ha3) (hout := hout) (haA := haA)
  have hBqcent : ∀ b ∈ B.map (QuotientGroup.mk' Q),
      ∀ k ∈ K.map (QuotientGroup.mk' Q), b * k = k * b :=
    map_quotient_centralizes (hQ := hQ) (hBK := hBK)
  have htqB : ∀ b ∈ B.map (QuotientGroup.mk' Q), tq * b = b * tq :=
    fun b hb => (hBqcent b hb tq htqK).symm
  let D : Subgroup X := Subgroup.zpowers a ⊔ B
  have hD : D = Subgroup.zpowers a ⊔ B := rfl
  have ha1 : a ≠ 1 := by
    intro h1
    apply hout
    rw [h1]
    exact Subgroup.mem_sup_left K.one_mem
  obtain ⟨hD3, hDK, hDQ⟩ :=
    D_isPGroup_and_normalizes (hQ := hQ) (hKn := hKn) (hBK := hBK) (hB3 := hB3)
      (ha3 := ha3) (ha1 := ha1) (haB := haB) (hD := hD)
  have hDbarcomm : ∀ d : ↥D, QuotientGroup.mk' Q (d : X) * tq =
      tq * QuotientGroup.mk' Q (d : X) :=
    D_bar_commutes (hQ := hQ) (ha3 := ha3) (hD := hD) (htqcomm := htqcomm)
      (htqB := htqB)
  obtain ⟨y', hy'eq, hy'fix⟩ :=
    exists_coprime_fixed_lift (hQ := hQ) (hKn := hKn) (hcop := hcop) (hD3 := hD3)
      (hDK := hDK) (hDQ := hDQ) (htqK := htqK) (hDbarcomm := hDbarcomm)
  have ht1K : (y' : X) ∈ K := y'.2
  have ht1centD : (y' : X) ∈ Subgroup.centralizer (D : Set X) :=
    Subgroup.mem_centralizer_iff.mpr
      (fun d hd => (commute_of_conj_eq_self (hy'fix ⟨d, hd⟩)).symm)
  have hmodQ : ∀ z ∈ A, ((y' : X) * z * (y' : X)⁻¹) * z ∈ Q :=
    lift_inverts_mod_core (ht1q := hy'eq) (htqinv := htqinv)
  have hA_cent_D : A ≤ Subgroup.centralizer (D : Set X) :=
    A_le_centralizer_D (hD := hD) (haA := haA) (hAB := hAB)
  obtain ⟨d, hdD0, hconj⟩ :=
    exists_D0_conj_eq (hQ := hQ) (hAK := hAK) (hA3 := hA3) (hcop := hcop)
      (hD := hD) (hA_cent_D := hA_cent_D) (htcentD := ht1centD) (hmod := hmodQ)
  exact exists_inverting_final (hQ := hQ) (hAK := hAK) (hA3 := hA3) (hcop := hcop)
    (hD := hD) (htK := ht1K) (htcentD := ht1centD) (hmod := hmodQ) ⟨d, hdD0, hconj⟩


private structure ComponentSup (G : Type) [Group G] [Finite G] (M K S : Subgroup G) (p : ℕ) where
  X : Subgroup G
  hSX : S ≤ X
  hKX : K ≤ X
  hXM : X ≤ M
  hX : CFSG.Open.IsKGroup ↥X
  hKXcomp : CFSG.IsPComponent p (K.subgroupOf X)
  hKXn : (K.subgroupOf X).Normal
  hrX : CFSG.Open.pRank 3 (K.subgroupOf X) = 1
  hcopX : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥(K.subgroupOf X))

private def componentSup_of_le {G : Type} [Group G] [Finite G] {M K S : Subgroup G}
    {p : ℕ} (hp : p.Prime) (hM : CFSG.Open.IsKGroup ↥M) (hKM : K ≤ M) (hSM : S ≤ M)
    (hK : CFSG.IsPComponent p (K.subgroupOf M)) (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hr : CFSG.Open.pRank 3 K = 1) (hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K)) :
    ComponentSup G M K S p := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  let X : Subgroup G := S ⊔ K
  have hSX : S ≤ X := le_sup_left
  have hKX : K ≤ X := le_sup_right
  have hXM : X ≤ M := sup_le hSM hKM
  refine
    { X := X, hSX := hSX, hKX := hKX, hXM := hXM, hX := hM.of_le hXM
      hKXcomp := CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_of_le
        hKX hXM hK
      hKXn := ?_, hrX := ?_, hcopX := ?_ }
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKX]
    exact sup_le hSK Subgroup.le_normalizer
  · exact (CFSG.RankThreeEvenClassification.Helpers.pRank_subgroupOf 3 Nat.prime_three K X
      hKX).trans hr
  · rw [card_pPrimeCore_subgroupOf hKX p]
    exact hcop

private theorem isSylowOf_inf_subgroupOf_sup {G : Type} [Group G] [Finite G] {M K S : Subgroup G}
    {p : ℕ} (C : ComponentSup G M K S p) (hS3 : IsPGroup 3 S)
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 3 (S ⊓ K) K) :
    CFSG.ABGLocalTools.IsSylowOf 3 (S.subgroupOf C.X ⊓ K.subgroupOf C.X)
      (K.subgroupOf C.X) := by
  have h1 : CFSG.ABGLocalTools.IsSylowOf 3
      (((S ⊓ K).subgroupOf C.X).map C.X.subtype) ((K.subgroupOf C.X).map C.X.subtype) := by
    rwa [Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans C.hSX),
      Subgroup.map_subgroupOf_eq_of_le C.hKX]
  have h2 := (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff C.X).mp h1
  rwa [show (S ⊓ K).subgroupOf C.X = S.subgroupOf C.X ⊓ K.subgroupOf C.X from by
    rw [Subgroup.subgroupOf, Subgroup.subgroupOf, Subgroup.subgroupOf, Subgroup.comap_inf]] at h2

private theorem out_of_componentSup {G : Type} [Group G] [Finite G] {M K S : Subgroup G}
    {p : ℕ} (C : ComponentSup G M K S p) {a : G} (haS : a ∈ S)
    (hout : a ∉ K ⊔ CFSG.GH74.GLS.centralizerSection K
      ((CFSG.pPrimeCore p ↥K).map K.subtype)) :
    (⟨a, C.hSX haS⟩ : C.X) ∉ K.subgroupOf C.X ⊔
      CFSG.GH74.GLS.centralizerSection (K.subgroupOf C.X)
        ((CFSG.pPrimeCore p ↥(K.subgroupOf C.X)).map (K.subgroupOf C.X).subtype) := by
  intro hmem
  apply hout
  have hle : (K.subgroupOf C.X ⊔ CFSG.GH74.GLS.centralizerSection (K.subgroupOf C.X)
      ((CFSG.pPrimeCore p ↥(K.subgroupOf C.X)).map (K.subgroupOf C.X).subtype)).map
        C.X.subtype ≤ K ⊔ CFSG.GH74.GLS.centralizerSection K
          ((CFSG.pPrimeCore p ↥K).map K.subtype) := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [Subgroup.map_subgroupOf_eq_of_le C.hKX]
      exact le_sup_left
    · exact (map_centralizerSection_core_subgroupOf_le C.hKX p).trans le_sup_right
  exact hle (Subgroup.mem_map.mpr ⟨⟨a, C.hSX haS⟩, hmem, rfl⟩)

private theorem exists_mem_inf_conj_mul_inv_mem_of_le (hFA : KFactFieldAutThree)
    {G : Type} [Group G] [Finite G] {M K S A : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hM : CFSG.Open.IsKGroup ↥M) (hKM : K ≤ M) (hSM : S ≤ M)
    (hK : CFSG.IsPComponent p (K.subgroupOf M)) (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hr : CFSG.Open.pRank 3 K = 1) (hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K))
    (hS3 : IsPGroup 3 S) (hSyl : CFSG.ABGLocalTools.IsSylowOf 3 (S ⊓ K) K)
    (hAK : A ≤ K) (hAS : A ≤ S) (hA3 : Nat.card A = 3)
    {a : G} (haS : a ∈ S) (ha3 : a ^ 3 = 1)
    (hout : a ∉ K ⊔ CFSG.GH74.GLS.centralizerSection K ((CFSG.pPrimeCore p ↥K).map K.subtype)) :
    ∃ y ∈ S ⊓ K, y * a * y⁻¹ * a⁻¹ ∈ A ∧ y * a * y⁻¹ ≠ a := by
  let C := componentSup_of_le hp hM hKM hSM hK hSK hr hcop
  have hSylX := isSylowOf_inf_subgroupOf_sup C hS3 hSyl
  have hAX : A.subgroupOf C.X ≤ K.subgroupOf C.X := Subgroup.subgroupOf_mono C.X hAK
  have hASX : A.subgroupOf C.X ≤ S.subgroupOf C.X := Subgroup.subgroupOf_mono C.X hAS
  have hA3X : Nat.card (A.subgroupOf C.X) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hAK.trans C.hKX)).toEquiv).trans hA3
  let aX : C.X := ⟨a, C.hSX haS⟩
  have haSX : aX ∈ S.subgroupOf C.X := Subgroup.mem_subgroupOf.mpr haS
  have ha3X : aX ^ 3 = 1 := by
    apply Subtype.ext
    simpa [aX] using ha3
  have houtX := out_of_componentSup C haS hout
  obtain ⟨yX, hyX, hzX, hneX⟩ :=
    exists_mem_inf_conj_mul_inv_mem_of_not_mem_sup hFA hp C.hX C.hKXcomp C.hKXn C.hrX
      C.hcopX (hS3.comap_subtype) hSylX hAX hASX hA3X haSX ha3X houtX
  have hyS : (yX : G) ∈ S := Subgroup.mem_subgroupOf.mp hyX.1
  have hyK : (yX : G) ∈ K := Subgroup.mem_subgroupOf.mp hyX.2
  have hzA : (yX : G) * a * (yX : G)⁻¹ * a⁻¹ ∈ A := by
    have h := Subgroup.mem_subgroupOf.mp hzX
    simpa [aX, Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hne : (yX : G) * a * (yX : G)⁻¹ ≠ a := by
    intro h
    apply hneX
    apply Subtype.ext
    simpa [aX] using h
  exact ⟨(yX : G), ⟨hyS, hyK⟩, hzA, hne⟩

private theorem exists_inv_mem_centralizer_of_le (hFI : KFactFieldAutInvert)
    {G : Type} [Group G] [Finite G] {M K S A B : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hM : CFSG.Open.IsKGroup ↥M) (hKM : K ≤ M) (hSM : S ≤ M)
    (hK : CFSG.IsPComponent p (K.subgroupOf M)) (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hr : CFSG.Open.pRank 3 K = 1) (hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K))
    (hAK : A ≤ K) (hA3 : Nat.card A = 3)
    (hB3 : IsPGroup 3 B) (hBS : B ≤ S)
    (hBK : ⁅B, K⁆ ≤ (CFSG.pPrimeCore p ↥K).map K.subtype)
    (hAB : ∀ z ∈ A, ∀ b ∈ B, z * b = b * z)
    {a : G} (haS : a ∈ S) (ha3 : a ^ 3 = 1)
    (hout : a ∉ K ⊔ CFSG.GH74.GLS.centralizerSection K ((CFSG.pPrimeCore p ↥K).map K.subtype))
    (haA : ∀ z ∈ A, a * z = z * a) (haB : ∀ b ∈ B, a * b = b * a) :
    ∃ t ∈ K, t * a = a * t ∧ (∀ b ∈ B, t * b = b * t) ∧ ∀ z ∈ A, t * z * t⁻¹ = z⁻¹ := by
  let C := componentSup_of_le hp hM hKM hSM hK hSK hr hcop
  have hAX : A.subgroupOf C.X ≤ K.subgroupOf C.X := Subgroup.subgroupOf_mono C.X hAK
  have hA3X : Nat.card (A.subgroupOf C.X) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hAK.trans C.hKX)).toEquiv).trans hA3
  have hBX : B.subgroupOf C.X ≤ S.subgroupOf C.X := Subgroup.subgroupOf_mono C.X hBS
  have hBX3 : IsPGroup 3 (B.subgroupOf C.X) := hB3.comap_subtype
  have hBKX : ⁅B.subgroupOf C.X, K.subgroupOf C.X⁆ ≤
      (CFSG.pPrimeCore p ↥(K.subgroupOf C.X)).map (K.subgroupOf C.X).subtype :=
    commutator_subgroupOf_le_pPrimeCore (hBS.trans C.hSX) C.hKX hBK
  let aX : C.X := ⟨a, C.hSX haS⟩
  have ha3X : aX ^ 3 = 1 := by
    apply Subtype.ext
    simpa [aX] using ha3
  have houtX := out_of_componentSup C haS hout
  have hABX : ∀ z ∈ A.subgroupOf C.X, ∀ b ∈ B.subgroupOf C.X, z * b = b * z := by
    intro z hz b hb
    apply Subtype.ext
    simpa using hAB (z : G) (Subgroup.mem_subgroupOf.mp hz) (b : G)
      (Subgroup.mem_subgroupOf.mp hb)
  have haAX : ∀ z ∈ A.subgroupOf C.X, aX * z = z * aX := by
    intro z hz
    apply Subtype.ext
    simpa [aX] using haA (z : G) (Subgroup.mem_subgroupOf.mp hz)
  have haBX : ∀ b ∈ B.subgroupOf C.X, aX * b = b * aX := by
    intro b hb
    apply Subtype.ext
    simpa [aX] using haB (b : G) (Subgroup.mem_subgroupOf.mp hb)
  obtain ⟨tX, htX, htaX, htBX, htinX⟩ :=
    exists_inv_mem_centralizer_of_not_mem_sup hFI hp C.hX C.hKXcomp C.hKXn C.hrX C.hcopX
      hAX hA3X hBX3 hBKX hABX ha3X houtX haAX haBX
  have htK : (tX : G) ∈ K := Subgroup.mem_subgroupOf.mp htX
  have hta : (tX : G) * a = a * (tX : G) := by
    simpa [aX] using congrArg Subtype.val htaX
  have htB : ∀ b ∈ B, (tX : G) * b = b * (tX : G) := by
    intro b hb
    have := htBX ⟨b, C.hSX (hBS hb)⟩ (Subgroup.mem_subgroupOf.mpr hb)
    simpa using congrArg Subtype.val this
  have htinA : ∀ z ∈ A, (tX : G) * z * (tX : G)⁻¹ = z⁻¹ := by
    intro z hz
    have hzX : (⟨z, C.hKX (hAK hz)⟩ : C.X) ∈ A.subgroupOf C.X :=
      Subgroup.mem_subgroupOf.mpr hz
    have := htinX ⟨z, C.hKX (hAK hz)⟩ hzX
    simpa using congrArg Subtype.val this
  exact ⟨(tX : G), htK, hta, htB, htinA⟩

namespace P812Hyp

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {L₁ L₂ : Subgroup G}

theorem exists_mem_inf_conj_mul_inv_mem₁ (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    (hK : CFSG.Open.IsKGroup ↥M) (hFA : KFactFieldAutThree)
    {S A₁ : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 3 S M) (hA₁ : A₁ ≤ L₁)
    (hA₁S : A₁ ≤ S) (hA₁3 : Nat.card A₁ = 3) {a : G} (haS : a ∈ S) (ha3 : a ^ 3 = 1)
    (hout : a ∉ L₁ ⊔ CFSG.GH74.GLS.centralizerSection L₁
      ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype)) :
    ∃ y ∈ S ⊓ L₁, y * a * y⁻¹ * a⁻¹ ∈ A₁ ∧ y * a * y⁻¹ ≠ a := by
  have hSL : S ≤ Subgroup.normalizer (L₁ : Set G) :=
    hS.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer h.le₁).mp h.normal₁)
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 (S ⊓ L₁) L₁ :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hS h.le₁
      ((Subgroup.normal_subgroupOf_iff_le_normalizer h.le₁).mp h.normal₁)
  exact exists_mem_inf_conj_mul_inv_mem_of_le hFA h.prime hK h.le₁ hS.le h.comp₁ hSL
    h.rank_three₁ (h.not_three_dvd_card_pPrimeCore₁ hSch) hS.isPGroup hSyl hA₁ hA₁S hA₁3
    haS ha3 hout

theorem exists_mem_inf_conj_mul_inv_mem₂ (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    (hK : CFSG.Open.IsKGroup ↥M) (hFA : KFactFieldAutThree)
    {S A₂ : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 3 S M) (hA₂ : A₂ ≤ L₂)
    (hA₂S : A₂ ≤ S) (hA₂3 : Nat.card A₂ = 3) {a : G} (haS : a ∈ S) (ha3 : a ^ 3 = 1)
    (hout : a ∉ L₂ ⊔ CFSG.GH74.GLS.centralizerSection L₂
      ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype)) :
    ∃ y ∈ S ⊓ L₂, y * a * y⁻¹ * a⁻¹ ∈ A₂ ∧ y * a * y⁻¹ ≠ a := by
  have hSL : S ≤ Subgroup.normalizer (L₂ : Set G) := by
    intro s hs
    exact h.mem_normalizer_two_of_odd hSch (hS.le hs)
      (CFSG.Quasithin.B1Red.odd_orderOf_of_isPGroup_three hS.isPGroup hs)
  have hS_NM : S ≤ M ⊓ Subgroup.normalizer (L₂ : Set G) := le_inf hS.le hSL
  have hS_syl : CFSG.ABGLocalTools.IsSylowOf 3 S
      (M ⊓ Subgroup.normalizer (L₂ : Set G)) :=
    hS.of_le hS_NM inf_le_left
  have hL₂_le : L₂ ≤ M ⊓ Subgroup.normalizer (L₂ : Set G) :=
    le_inf h.le₂ Subgroup.le_normalizer
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 (S ⊓ L₂) L₂ :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hS_syl hL₂_le inf_le_right
  exact exists_mem_inf_conj_mul_inv_mem_of_le hFA h.prime hK h.le₂ hS.le h.comp₂ hSL
    h.rank_three₂ (h.not_three_dvd_card_pPrimeCore₂ hSch) hS.isPGroup hSyl hA₂ hA₂S hA₂3
    haS ha3 hout

theorem exists_inv_mem_centralizer₁ (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    (hK : CFSG.Open.IsKGroup ↥M) (hFI : KFactFieldAutInvert)
    {S A₁ B : Subgroup G} (hSM : S ≤ M) (hS3 : IsPGroup 3 S) (hA₁ : A₁ ≤ L₁)
    (hA₁S : A₁ ≤ S) (hA₁3 : Nat.card A₁ = 3) (hBS : B ≤ S)
    (hBL : ⁅B, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype)
    (hAB : ∀ z ∈ A₁, ∀ b ∈ B, z * b = b * z) {a : G} (haS : a ∈ S) (ha3 : a ^ 3 = 1)
    (hout : a ∉ L₁ ⊔ CFSG.GH74.GLS.centralizerSection L₁
      ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype))
    (haA : ∀ z ∈ A₁, a * z = z * a) (haB : ∀ b ∈ B, a * b = b * a) :
    ∃ t ∈ L₁, t * a = a * t ∧ (∀ b ∈ B, t * b = b * t) ∧
      ∀ z ∈ A₁, t * z * t⁻¹ = z⁻¹ := by
  have hSL : S ≤ Subgroup.normalizer (L₁ : Set G) :=
    hSM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer h.le₁).mp h.normal₁)
  exact exists_inv_mem_centralizer_of_le hFI h.prime hK h.le₁ hSM h.comp₁ hSL h.rank_three₁
    (h.not_three_dvd_card_pPrimeCore₁ hSch) hA₁ hA₁3 (hS3.to_le hBS) hBS hBL hAB haS ha3
    hout haA haB

theorem exists_inv_mem_centralizer₂ (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    (hK : CFSG.Open.IsKGroup ↥M) (hFI : KFactFieldAutInvert)
    {S A₂ B : Subgroup G} (hSM : S ≤ M) (hS3 : IsPGroup 3 S) (hA₂ : A₂ ≤ L₂)
    (hA₂S : A₂ ≤ S) (hA₂3 : Nat.card A₂ = 3) (hBS : B ≤ S)
    (hBL : ⁅B, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype)
    (hAB : ∀ z ∈ A₂, ∀ b ∈ B, z * b = b * z) {a : G} (haS : a ∈ S) (ha3 : a ^ 3 = 1)
    (hout : a ∉ L₂ ⊔ CFSG.GH74.GLS.centralizerSection L₂
      ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype))
    (haA : ∀ z ∈ A₂, a * z = z * a) (haB : ∀ b ∈ B, a * b = b * a) :
    ∃ t ∈ L₂, t * a = a * t ∧ (∀ b ∈ B, t * b = b * t) ∧
      ∀ z ∈ A₂, t * z * t⁻¹ = z⁻¹ := by
  have hSL : S ≤ Subgroup.normalizer (L₂ : Set G) := by
    intro s hs
    exact h.mem_normalizer_two_of_odd hSch (hSM hs)
      (CFSG.Quasithin.B1Red.odd_orderOf_of_isPGroup_three hS3 hs)
  exact exists_inv_mem_centralizer_of_le hFI h.prime hK h.le₂ hSM h.comp₂ hSL h.rank_three₂
    (h.not_three_dvd_card_pPrimeCore₂ hSch) hA₂ hA₂3 (hS3.to_le hBS) hBS hBL hAB haS ha3
    hout haA haB

end P812Hyp


end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
