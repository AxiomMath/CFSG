module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

section Abstract

variable {G : Type} [Group G] [Finite G]

private theorem exists_pPart_mul {p : ℕ} (hp : p.Prime) (c : G) :
    ∃ a ∈ Subgroup.zpowers c, ∃ b ∈ Subgroup.zpowers c, c = a * b ∧
      (∃ k : ℕ, a ^ p ^ k = 1) ∧ Nat.Coprime p (orderOf b) := by
  obtain ⟨k, m, hpm, hkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos c).ne' p hp.ne_one
  have hpm' : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
  have hcop : Nat.Coprime (p ^ k) m := Nat.Coprime.pow_left k hpm'
  have hbez := Nat.gcd_eq_gcd_ab (p ^ k) m
  rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
  set x := Nat.gcdA (p ^ k) m
  set y := Nat.gcdB (p ^ k) m
  refine ⟨c ^ ((m : ℤ) * y), ⟨_, rfl⟩, c ^ ((p ^ k : ℕ) * x : ℤ), ⟨_, rfl⟩, ?_, ⟨k, ?_⟩, ?_⟩
  · rw [← _root_.zpow_add, add_comm, ← hbez, zpow_one]
  · rw [← zpow_natCast, ← _root_.zpow_mul, show ((m : ℤ) * y) * ((p ^ k : ℕ) : ℤ) =
        ((orderOf c : ℕ) : ℤ) * y by rw [hkm]; push_cast; ring, _root_.zpow_mul, zpow_natCast,
      pow_orderOf_eq_one, _root_.one_zpow]
  · have h1 : orderOf (c ^ ((p ^ k : ℕ) * x : ℤ)) ∣ m := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← zpow_natCast, ← _root_.zpow_mul, show ((p ^ k : ℕ) * x : ℤ) * (m : ℤ) =
        ((orderOf c : ℕ) : ℤ) * x by rw [hkm]; push_cast; ring, _root_.zpow_mul, zpow_natCast,
        pow_orderOf_eq_one, _root_.one_zpow]
    exact Nat.Coprime.of_dvd_right h1 hpm'

private theorem relPPrimeCore_eq_map_self {p : ℕ} (hp : p.Prime) (C : Subgroup G) :
    CFSG.Open.relPPrimeCore p C =
      (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥C) p).map C.subtype := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply le_antisymm
  · refine sSup_le fun N hN => ?_
    obtain ⟨hNC, hNn, hNc⟩ := hN
    have h1 : N.subgroupOf C ≤
        CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥C) p := by
      refine le_sSup ⟨hNn, ?_⟩
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv]
      exact hNc
    calc N = (N.subgroupOf C).map C.subtype := (Subgroup.map_subgroupOf_eq_of_le hNC).symm
      _ ≤ _ := Subgroup.map_mono h1
  · refine le_sSup ⟨?_, ?_, ?_⟩
    · rintro _ ⟨y, -, rfl⟩
      exact y.2
    · show (Subgroup.comap C.subtype
        ((CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥C) p).map
          C.subtype)).Normal
      rw [Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
      infer_instance
    · rw [Subgroup.card_map_of_injective C.subtype_injective]
      exact CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore_coprime p

private theorem relPPrimeCore_le_self (p : ℕ) (C : Subgroup G) :
    CFSG.Open.relPPrimeCore p C ≤ C :=
  sSup_le fun _ hN => hN.1

private theorem coprime_card_relPPrimeCore_self {p : ℕ} (hp : p.Prime) (C : Subgroup G) :
    Nat.Coprime p (Nat.card (CFSG.Open.relPPrimeCore p C)) := by
  rw [relPPrimeCore_eq_map_self hp C, Subgroup.card_map_of_injective C.subtype_injective]
  exact CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore_coprime p

private theorem relPPrimeCore_normal_self {p : ℕ} (hp : p.Prime) (C : Subgroup G) :
    ((CFSG.Open.relPPrimeCore p C).subgroupOf C).Normal := by
  rw [relPPrimeCore_eq_map_self hp C]
  show (Subgroup.comap C.subtype
    ((CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥C) p).map
      C.subtype)).Normal
  rw [Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
  infer_instance

private theorem subgroupOf_inf_normal {H K N : Subgroup G} (hKH : K ≤ H)
    (hK : (K.subgroupOf H).Normal) (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal) :
    ((K ⊓ N).subgroupOf H).Normal := by
  have hHK : H ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hK
  have hHN : H ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp hN
  exact Subgroup.normal_subgroupOf_of_le_normalizer
    ((le_inf hHK hHN).trans Subgroup.inf_normalizer_le_normalizer_inf)

private theorem mem_map_conj_iff' {A : Subgroup G} {g z : G} :
    z ∈ A.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * z * g ∈ A := by
  constructor
  · rintro ⟨a, ha, haz⟩
    rw [← haz]
    change g⁻¹ * MulAut.conj g a * g ∈ A
    have hga : g⁻¹ * MulAut.conj g a * g = a := by
      rw [MulAut.conj_apply]
      group
    rwa [hga]
  · intro hz
    refine ⟨g⁻¹ * z * g, hz, ?_⟩
    change MulAut.conj g (g⁻¹ * z * g) = z
    rw [MulAut.conj_apply]
    group

private theorem mem_sup_of_le_normalizer {A B : Subgroup G}
    (h : B ≤ Subgroup.normalizer (A : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hAn : (A.subgroupOf (A ⊔ B)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer h)
  have htop : (A.subgroupOf (A ⊔ B)) ⊔ (B.subgroupOf (A ⊔ B)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (le_sup_left : A ≤ A ⊔ B) (le_sup_right : B ≤ A ⊔ B),
      Subgroup.subgroupOf_self]
  haveI := hAn
  have hz : (⟨x, hx⟩ : ↥(A ⊔ B)) ∈
      (A.subgroupOf (A ⊔ B)) ⊔ (B.subgroupOf (A ⊔ B)) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp hz
  refine ⟨(a : G), Subgroup.mem_subgroupOf.mp ha, (b : G), Subgroup.mem_subgroupOf.mp hb, ?_⟩
  simpa using congrArg Subtype.val hab

private theorem exists_mul_mem_normalizer_of_mem {q : ℕ} [Fact q.Prime] {H K N R : Subgroup G}
    (hKH : K ≤ H) (hK : (K.subgroupOf H).Normal) (hNH : N ≤ H)
    (hN : (N.subgroupOf H).Normal) (hR : CFSG.ABGLocalTools.IsSylowOf q R N)
    {x : G} (hx : x ∈ K) :
    ∃ y ∈ K ⊓ Subgroup.normalizer (R : Set G), ∃ k ∈ K ⊓ N, y * k = x := by
  classical
  have hK₀H : K ⊓ N ≤ H := inf_le_left.trans hKH
  have hK₀norm : ((K ⊓ N).subgroupOf H).Normal := subgroupOf_inf_normal hKH hK hNH hN
  have hHnormK₀ : H ≤ Subgroup.normalizer ((K ⊓ N : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK₀H).mp hK₀norm
  have hRK₀ : R ≤ Subgroup.normalizer ((K ⊓ N : Subgroup G) : Set G) :=
    hR.le.trans (hNH.trans hHnormK₀)
  have hB_le_N : (K ⊓ N) ⊔ R ≤ N := sup_le inf_le_right hR.le
  have hRsylowB : CFSG.ABGLocalTools.IsSylowOf q R ((K ⊓ N) ⊔ R) :=
    hR.of_le le_sup_right hB_le_N
  have hxR_le_B : Subgroup.map (MulAut.conj x).toMonoidHom R ≤ (K ⊓ N) ⊔ R := by
    intro z hz
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hz
    change x * r * x⁻¹ ∈ (K ⊓ N) ⊔ R
    have hHnormK : H ≤ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hK
    have hHnormN : H ≤ Subgroup.normalizer (N : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp hN
    have hcK : x * r * x⁻¹ * r⁻¹ ∈ K := by
      have hrK : r ∈ Subgroup.normalizer (K : Set G) := hHnormK (hNH (hR.le hr))
      have h1 : r * x⁻¹ * r⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hrK x⁻¹).1 (K.inv_mem hx)
      simpa only [mul_assoc] using K.mul_mem hx h1
    have hcN : x * r * x⁻¹ * r⁻¹ ∈ N := by
      have hxN : x ∈ Subgroup.normalizer (N : Set G) := hHnormN (hKH hx)
      have h1 : x * r * x⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hxN r).1 (hR.le hr)
      exact N.mul_mem h1 (N.inv_mem (hR.le hr))
    have heq : (x * r * x⁻¹ * r⁻¹) * r = x * r * x⁻¹ := by group
    rw [← heq]
    exact Subgroup.mul_mem_sup ⟨hcK, hcN⟩ hr
  have hxR_sylowB : CFSG.ABGLocalTools.IsSylowOf q
      (Subgroup.map (MulAut.conj x).toMonoidHom R) ((K ⊓ N) ⊔ R) :=
    CFSG.ABGLocalTools.isSylowOf_of_card hxR_le_B (by
      rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
      exact hRsylowB.card_eq)
  obtain ⟨k, hkB, hconj⟩ := hRsylowB.exists_mem_conj hxR_sylowB
  obtain ⟨k', hk'K₀, r', hr'R, hk'⟩ := mem_sup_of_le_normalizer hRK₀ hkB
  have hconj_k : Subgroup.map (MulAut.conj x).toMonoidHom R =
      Subgroup.map (MulAut.conj k).toMonoidHom R := by
    ext z
    exact (hconj z).trans (mem_map_conj_iff' (A := R) (g := k)).symm
  have hconj_k' : Subgroup.map (MulAut.conj x).toMonoidHom R =
      Subgroup.map (MulAut.conj k').toMonoidHom R := by
    rw [hconj_k, ← hk']
    ext z
    rw [mem_map_conj_iff', mem_map_conj_iff']
    have hr'mem : r'⁻¹ ∈ Subgroup.normalizer (R : Set G) :=
      (Subgroup.normalizer (R : Set G)).inv_mem (R.le_normalizer hr'R)
    constructor
    · intro hz
      refine (Subgroup.mem_normalizer_iff.mp hr'mem (k'⁻¹ * z * k')).2 ?_
      convert hz using 1
      group
    · intro hz
      convert (Subgroup.mem_normalizer_iff.mp hr'mem (k'⁻¹ * z * k')).1 hz using 1
      group
  have hiff : ∀ z : G, x⁻¹ * z * x ∈ R ↔ k'⁻¹ * z * k' ∈ R := by
    intro z
    have h : z ∈ Subgroup.map (MulAut.conj x).toMonoidHom R ↔
        z ∈ Subgroup.map (MulAut.conj k').toMonoidHom R :=
      (SetLike.ext_iff.mp hconj_k') z
    rwa [mem_map_conj_iff', mem_map_conj_iff'] at h
  have hy' : k'⁻¹ * x ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have h := hiff (x * u * x⁻¹)
    have hL : x⁻¹ * (x * u * x⁻¹) * x = u := by group
    have hR : k'⁻¹ * (x * u * x⁻¹) * k' = (k'⁻¹ * x) * u * (k'⁻¹ * x)⁻¹ := by group
    rwa [hL, hR] at h
  have hy'K : k'⁻¹ * x ∈ K := K.mul_mem (K.inv_mem hk'K₀.1) hx
  have hy'H : k'⁻¹ * x ∈ H := hKH hy'K
  have hy'norm : k'⁻¹ * x ∈ Subgroup.normalizer ((K ⊓ N : Subgroup G) : Set G) :=
    hHnormK₀ hy'H
  have hk''K₀ : (k'⁻¹ * x)⁻¹ * k' * (k'⁻¹ * x) ∈ K ⊓ N := by
    have h := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer ((K ⊓ N : Subgroup G) : Set G)).inv_mem hy'norm) k').1 hk'K₀
    simpa using h
  refine ⟨k'⁻¹ * x, ⟨hy'K, hy'⟩, (k'⁻¹ * x)⁻¹ * k' * (k'⁻¹ * x), hk''K₀, ?_⟩
  group

theorem le_closure_pElem_sup_inf {p q : ℕ} [Fact q.Prime] (hp : p.Prime)
    {H K N R : Subgroup G} (hKH : K ≤ H) (hK : (K.subgroupOf H).Normal) (hNH : N ≤ H)
    (hN : (N.subgroupOf H).Normal) (hR : CFSG.ABGLocalTools.IsSylowOf q R N)
    (hgen : K ≤ closure {x : G | x ∈ K ∧ ∃ n : ℕ, x ^ p ^ n = 1}) :
    K ≤ closure {y : G | y ∈ K ∧ y ∈ normalizer (R : Set G) ∧ ∃ n : ℕ, y ^ p ^ n = 1} ⊔
      (K ⊓ N) := by
  refine hgen.trans ?_
  rw [Subgroup.closure_le]
  rintro x ⟨hxK, hxp⟩
  obtain ⟨np, hnp⟩ := hxp
  obtain ⟨y, hy, k, hk, hyk⟩ := exists_mul_mem_normalizer_of_mem hKH hK hNH hN hR hxK
  obtain ⟨a, ha_zpow, b, hb_zpow, hyab, ha_p, hbcop⟩ := exists_pPart_mul hp y
  have haK : a ∈ K := (Subgroup.zpowers_le.mpr hy.1) ha_zpow
  have haS : a ∈ {y : G | y ∈ K ∧ y ∈ normalizer (R : Set G) ∧
      ∃ n : ℕ, y ^ p ^ n = 1} :=
    ⟨haK, (Subgroup.zpowers_le.mpr hy.2) ha_zpow, ha_p⟩
  have hbK : b ∈ K := (Subgroup.zpowers_le.mpr hy.1) hb_zpow
  have hbN : b ∈ N := by
    have hK₀H : K ⊓ N ≤ H := inf_le_left.trans hKH
    have hK₀norm : ((K ⊓ N).subgroupOf H).Normal := subgroupOf_inf_normal hKH hK hNH hN
    have hHnormK₀ : H ≤ Subgroup.normalizer ((K ⊓ N : Subgroup G) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hK₀H).mp hK₀norm
    have hKnormK₀ : K ≤ Subgroup.normalizer ((K ⊓ N : Subgroup G) : Set G) :=
      hKH.trans hHnormK₀
    let K₀' : Subgroup ↥K := (K ⊓ N).subgroupOf K
    haveI : K₀'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKnormK₀
    let ν : ↥K →* ↥K ⧸ K₀' := QuotientGroup.mk' K₀'
    have hkK : k ∈ K := hk.1
    have hkK₀' : (⟨k, hkK⟩ : ↥K) ∈ K₀' := Subgroup.mem_subgroupOf.mpr hk
    have hνk : ν ⟨k, hkK⟩ = 1 := (QuotientGroup.eq_one_iff (N := K₀') _).mpr hkK₀'
    have hνy_eq : ν ⟨y, hy.1⟩ = ν ⟨x, hxK⟩ := by
      have h : (⟨x, hxK⟩ : ↥K) = ⟨y, hy.1⟩ * ⟨k, hkK⟩ := Subtype.ext (by simpa using hyk.symm)
      rw [h, map_mul, hνk, mul_one]
    have hνx_pow : (ν ⟨x, hxK⟩) ^ p ^ np = 1 := by
      have h : (⟨x, hxK⟩ : ↥K) ^ p ^ np = 1 := Subtype.ext (by simpa using hnp)
      rw [← map_pow, h, map_one]
    have hνy_pow : (ν ⟨y, hy.1⟩) ^ p ^ np = 1 := by rw [hνy_eq, hνx_pow]
    have hzb : (⟨b, hbK⟩ : ↥K) ∈ Subgroup.zpowers (⟨y, hy.1⟩ : ↥K) := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hb_zpow
      exact Subgroup.mem_zpowers_iff.mpr ⟨m, Subtype.ext (by simpa using hm)⟩
    have hνb_zpow : ν ⟨b, hbK⟩ ∈ Subgroup.zpowers (ν ⟨y, hy.1⟩) := by
      have h := Subgroup.mem_map_of_mem ν hzb
      rwa [MonoidHom.map_zpowers] at h
    have h1 : orderOf (ν ⟨b, hbK⟩) ∣ p ^ np :=
      (orderOf_dvd_of_mem_zpowers hνb_zpow).trans (orderOf_dvd_of_pow_eq_one hνy_pow)
    have h2 : orderOf (ν ⟨b, hbK⟩) ∣ orderOf b := by
      have h := orderOf_map_dvd ν ⟨b, hbK⟩
      simpa [orderOf_mk] using h
    have hone : orderOf (ν ⟨b, hbK⟩) = 1 :=
      Nat.eq_one_of_dvd_coprimes (hbcop.pow_left np) h1 h2
    have hνb : ν ⟨b, hbK⟩ = 1 := orderOf_eq_one_iff.mp hone
    have hbK₀ : (⟨b, hbK⟩ : ↥K) ∈ K₀' := (QuotientGroup.eq_one_iff (N := K₀') _).mp hνb
    exact (Subgroup.mem_subgroupOf.mp hbK₀).2
  have hbk : b * k ∈ K ⊓ N :=
    (K ⊓ N).mul_mem (Subgroup.mem_inf.mpr ⟨hbK, hbN⟩) hk
  rw [← hyk, hyab, mul_assoc]
  exact Subgroup.mul_mem_sup (Subgroup.subset_closure haS) hbk

theorem le_inf_centralizer_sup_inf {p q : ℕ} [Fact q.Prime] (hp : p.Prime)
    {H K N R : Subgroup G} (hKH : K ≤ H) (hK : (K.subgroupOf H).Normal) (hNH : N ≤ H)
    (hN : (N.subgroupOf H).Normal) (hR : CFSG.ABGLocalTools.IsSylowOf q R N)
    (hgen : K ≤ closure {x : G | x ∈ K ∧ ∃ n : ℕ, x ^ p ^ n = 1})
    (hcent : ∀ y ∈ K, y ∈ normalizer (R : Set G) → (∃ n : ℕ, y ^ p ^ n = 1) →
      y ∈ centralizer (R : Set G)) :
    K ≤ (K ⊓ centralizer (R : Set G)) ⊔ (K ⊓ N) := by
  have h1 := le_closure_pElem_sup_inf (p := p) (q := q) hp hKH hK hNH hN hR hgen
  have hcl : closure {y : G | y ∈ K ∧ y ∈ normalizer (R : Set G) ∧
      ∃ n : ℕ, y ^ p ^ n = 1} ≤ K ⊓ centralizer (R : Set G) := by
    rw [Subgroup.closure_le]
    rintro y ⟨hyK, hyN, hyp⟩
    exact ⟨hyK, hcent y hyK hyN hyp⟩
  exact h1.trans (sup_le_sup_right hcl _)

theorem inf_relPPrimeCore_le_relPPrimeCore {p : ℕ} (hp : p.Prime) {H K : Subgroup G} (hKH : K ≤ H)
    (hK : (K.subgroupOf H).Normal) :
    K ⊓ CFSG.Open.relPPrimeCore p H ≤ CFSG.Open.relPPrimeCore p K := by
  have hOH : CFSG.Open.relPPrimeCore p H ≤ H := relPPrimeCore_le_self p H
  have hHnorm : H ≤ Subgroup.normalizer ((CFSG.Open.relPPrimeCore p H : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOH).mp (relPPrimeCore_normal_self hp H)
  have hKnorm : K ≤ Subgroup.normalizer ((CFSG.Open.relPPrimeCore p H : Subgroup G) : Set G) :=
    hKH.trans hHnorm
  have hN : ((K ⊓ CFSG.Open.relPPrimeCore p H).subgroupOf K).Normal := by
    rw [inf_comm, Subgroup.inf_subgroupOf_right]
    exact Subgroup.normal_subgroupOf_of_le_normalizer hKnorm
  refine le_sSup (s := {N : Subgroup G | N ≤ K ∧ (N.subgroupOf K).Normal ∧
    Nat.Coprime p (Nat.card N)}) ⟨inf_le_left, hN, ?_⟩
  exact Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
    (coprime_card_relPPrimeCore_self hp H)

end Abstract

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
