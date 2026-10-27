module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma315Sz

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_conj_mem_of_finite {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g).injective])
  exact mem_normalizer_iff_map_conj_eq.mpr heq

omit [Finite G] in
theorem commutator_mem_of_sq_mem {H N : Subgroup G} (hHN : H ≤ normalizer (N : Set G))
    {x y : G} (hy : y ∈ H) (hx2 : x ^ 2 ∈ N) (hy2 : y ^ 2 ∈ N) (hxy2 : (x * y) ^ 2 ∈ N) :
    x * y * x⁻¹ * y⁻¹ ∈ N := by
  have e : x * y * x⁻¹ * y⁻¹ = (x * y) ^ 2 * (y⁻¹ * (x ^ 2)⁻¹ * y) * (y ^ 2)⁻¹ := by
    rw [sq, sq, sq]
    group
  rw [e]
  refine mul_mem (mul_mem hxy2 ?_) (inv_mem hy2)
  have := (mem_normalizer_iff.mp (inv_mem (hHN hy)) _).mp (inv_mem hx2)
  simpa using this

@[expose] def NoStronglyClosedAbelian (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (S : Sylow 2 G) (A : Subgroup G), A ≤ S → IsMulCommutative A → A ≠ ⊥ →
    (∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g ∈ A) → False

namespace Sec3

variable {L T R : Subgroup G} {a : ℕ} {y d : G}

structure SzR (G : Type) [Group G] [Finite G] (L T R : Subgroup G) (a : ℕ) (y d : G) : Prop where
  sec3 : Sec3 G L T
  foundation : Foundation
  oddCenter : Odd (Nat.card (center L))
  one_le : 1 ≤ a
  iso : Nonempty (rankTwoQuot L ≃* Sz a)
  isR : IsR L T R
  trans : ∀ Q ∈ gmsDelta L T, ∃ u ∈ gmsTrans L T,
    rightConjugate (T ⊓ centralizer (L : Set G)) u⁻¹ = Q
  torus : IsTorus L T y
  mem_normalizer : d ∈ normalizer (R : Set G)
  mem_normalizer_gmsW : d ∈ normalizer (gmsW L T : Set G)
  odd : Odd (orderOf d)
  conj_eq : ∀ w ∈ gmsW L T, d * w * d⁻¹ = y * w * y⁻¹

theorem exists_szR
    (h : Sec3 G L T) (hF : Foundation) (hZ : Odd (Nat.card (center L))) (ha : 1 ≤ a)
    (e : rankTwoQuot L ≃* Sz a)
    (htr : ∀ Q ∈ gmsDelta L T, ∃ u ∈ gmsTrans L T,
      rightConjugate (T ⊓ centralizer (L : Set G)) u⁻¹ = Q) :
    ∃ R y d, SzR G L T R a y d := by
  have hX := h.facts_of_sz hF hZ ha e
  have h313 := h.lemma313_of_sz_of_odd hF hZ ha e
  obtain ⟨R, hR⟩ := exists_isR h313 hX h hF
  obtain ⟨y, hy⟩ := hX.exists_isTorus h
  have hTW : T = gmsW L T := h.eq_sup_of_sz ha e
  obtain ⟨-, -, -, hVW, -⟩ := hX.vFacts h hF
  have hTC : T ≤ centralizer (gmsV L T : Set G) := fun t ht =>
    le_centralizer_iff.mp hVW (by rw [hTW] at ht; exact ht)
  have hW : T ⊓ centralizer (gmsV L T : Set G) = gmsW L T := (inf_eq_left.mpr hTC).trans hTW
  obtain ⟨d, hdR, hdW, hdo, hdy⟩ := hR.exists_torus h313 h hW hy
    (commute_of_odd_of_mem_gmsTrans_of_sz h hF hZ ha e)
  exact ⟨R, y, d, h, hF, hZ, ha, ⟨e⟩, hR, htr, hy, hdR, hdW, hdo, hdy⟩

omit [Finite G] in
theorem inf_le_normalizer_T₀ :
    T ⊓ L ≤ normalizer ((T ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := fun x hx =>
  Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun _ hs =>
    (mem_centralizer_iff.mp (mem_inf.mp hs).2 x (mem_inf.mp hx).2).symm)

namespace SzR

variable (hS : SzR G L T R a y d)
include hS

theorem facts :
    Facts L T (2 ^ (2 * a + 1)) :=
  hS.sec3.facts_of_sz hS.foundation hS.oddCenter hS.one_le hS.iso.some

theorem lemma313 :
    Lemma313 L T (2 ^ (2 * a + 1)) :=
  hS.sec3.lemma313_of_sz_of_odd hS.foundation hS.oddCenter hS.one_le hS.iso.some

theorem eq_gmsW : T = gmsW L T :=
  hS.sec3.eq_sup_of_sz hS.one_le hS.iso.some

theorem gmsV_le :
    gmsV L T ≤ gmsW L T :=
  (hS.facts.vFacts hS.sec3 hS.foundation).2.2.1

theorem inf_centralizer :
    T ⊓ centralizer (gmsV L T : Set G) = gmsW L T := by
  obtain ⟨-, -, -, hVW, -⟩ := hS.facts.vFacts hS.sec3 hS.foundation
  have hTC : T ≤ centralizer (gmsV L T : Set G) := fun t ht =>
    le_centralizer_iff.mp hVW (by rw [hS.eq_gmsW] at ht; exact ht)
  exact (inf_eq_left.mpr hTC).trans hS.eq_gmsW

theorem T_le : T ≤ R := fun t ht =>
  hS.isR.gmsW_le (by rw [hS.eq_gmsW] at ht; exact ht)

theorem gmsV_le_R : gmsV L T ≤ R :=
  hS.gmsV_le.trans hS.isR.gmsW_le

theorem inf_centralizer_R :
    R ⊓ centralizer (gmsV L T : Set G) = T := by
  rw [hS.isR.inf_centralizer_eq hS.sec3 hS.inf_centralizer, ← hS.eq_gmsW]

theorem le_normalizer_T :
    R ≤ normalizer (T : Set G) := by
  rw [hS.eq_gmsW]
  exact hS.isR.le_normalizer_gmsW hS.sec3 hS.inf_centralizer

theorem normalizer_T₀_le :
    normalizer ((T ⊓ centralizer (L : Set G) : Subgroup G) : Set G) ≤
      normalizer (L : Set G) := by
  have hN := AS76b.Lemma36.normalizer_le hS.sec3.hyp.hyp31 hS.sec3.isSylowOf_T₀ 1
  rwa [rightConjugate_one, rightConjugate_one] at hN

theorem mem_normalizer_gmsV :
    d ∈ normalizer (gmsV L T : Set G) := by
  refine mem_normalizer_of_conj_mem_of_finite fun v hv => ?_
  rw [hS.conj_eq v (hS.gmsV_le hv)]
  exact (mem_normalizer_iff.mp hS.torus.mem_normalizer v).mp hv

theorem conj_mul_inv_mem_gmsA {v : G}
    (hv : v ∈ gmsV L T) : d * v * d⁻¹ * v⁻¹ ∈ gmsA L T := by
  rw [hS.conj_eq v (hS.gmsV_le hv)]
  exact (mem_gmsN₁.mp hS.torus.mem_gmsN₁).2.2 v hv

theorem commute_T₀ {t : G}
    (ht : t ∈ T ⊓ centralizer (L : Set G)) : d * t * d⁻¹ = t := by
  rw [hS.conj_eq t (mem_sup_right ht), hS.torus.commute ht]
  group

theorem isSylowOf_normalizer :
    IsSylowOf 2 R (normalizer (gmsV L T : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS', hRS⟩ := AS76b.exists_isSylowOf_le hS.isR.le_normalizer_gmsV hS.isR.isPGroup
  have hSR : S ≤ R := by
    intro s hs
    have hsV := hS'.le hs
    obtain ⟨r, hr, hrQ⟩ := hS.isR.exists_conj_eq hS.facts hS.sec3 hS.trans
      (rightConjugate_mem_delta mem_delta_T₀ (inv_mem hsV))
    have hN : r⁻¹ * s ∈ normalizer ((T ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := by
      have h1 : rightConjugate (T ⊓ centralizer (L : Set G)) (s⁻¹ * r) =
          T ⊓ centralizer (L : Set G) := by
        rw [← rightConjugate_mul, ← hrQ, rightConjugate_mul, inv_mul_cancel, rightConjugate_one]
      have := inv_mem ((rightConjugate_eq_self_iff _ _).mp h1)
      simpa using this
    have hmem : r⁻¹ * s ∈ T := hS.sec3.mem_of_mem_normalizer hS'.isPGroup
      (hS.T_le.trans hRS) (mul_mem (inv_mem (hRS hr)) hs) (hS.normalizer_T₀_le hN)
    have := mul_mem hr (hS.T_le hmem)
    simpa using this
  rwa [le_antisymm hSR hRS] at hS'

theorem exists_mul_of_mem_T {t : G} (ht : t ∈ T) :
    ∃ t₁ ∈ T ⊓ L, ∃ s ∈ T ⊓ centralizer (L : Set G), t₁ * s = t := by
  rw [hS.eq_gmsW] at ht
  exact CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer inf_le_normalizer_T₀ ht

theorem sq_mem_gmsA_of_mem_T {t : G}
    (ht : t ∈ T) : t ^ 2 ∈ gmsA L T := by
  obtain ⟨t₁, ht₁, s, hs, rfl⟩ := hS.exists_mul_of_mem_T ht
  have hcomm : t₁ * s = s * t₁ := mem_centralizer_iff.mp (mem_inf.mp hs).2 t₁ (mem_inf.mp ht₁).2
  have hs2 : s ^ 2 = 1 := (hS.sec3.isElemAbelian_T₀ hS.foundation).2 s hs
  have e : (t₁ * s) ^ 2 = t₁ ^ 2 := by
    calc (t₁ * s) ^ 2 = t₁ * (s * t₁) * s := by rw [sq]; group
      _ = t₁ * (t₁ * s) * s := by rw [← hcomm]
      _ = t₁ ^ 2 * s ^ 2 := by rw [sq, sq]; group
      _ = t₁ ^ 2 := by rw [hs2, mul_one]
  rw [e]
  exact hS.facts.sq_mem t₁ ht₁

theorem exists_mem_T₁_not_mem_gmsA :
    ∃ t ∈ T ⊓ L, t ∉ gmsA L T := by
  by_contra hcon
  push Not at hcon
  have hq : 8 ≤ 2 ^ (2 * a + 1) :=
    (show 8 = 2 ^ 3 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) (by have := hS.one_le; omega)
  obtain ⟨hT₁, hA₁, -⟩ := sylow_of_benderBorel hS.oddCenter (by omega)
    (Asc76X.fusionBenderBorel_of_mulEquiv_sz hS.one_le hS.iso.some) hS.sec3.isSylowOf_T₁
  have hle : Nat.card (T ⊓ L : Subgroup G) ≤ Nat.card (gmsA L T) := card_le_of_le hcon
  rw [hT₁, hA₁, sq] at hle
  nlinarith

theorem exists_central :
    ∃ t ∈ T, t ∉ gmsV L T ∧ ∀ r ∈ R, r * t * r⁻¹ * t⁻¹ ∈ gmsV L T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVR := hS.gmsV_le_R
  have hTR := hS.T_le
  set N := (gmsV L T).subgroupOf R with hN
  have : N.Normal := (normal_subgroupOf_iff_le_normalizer hVR).mpr hS.isR.le_normalizer_gmsV
  have hQ : IsPGroup 2 (R ⧸ N) := hS.isR.isPGroup.to_quotient N
  have : Group.IsNilpotent (R ⧸ N) := hQ.isNilpotent
  have hTn : (T.subgroupOf R).Normal :=
    (normal_subgroupOf_iff_le_normalizer hTR).mpr hS.le_normalizer_T
  set H := (T.subgroupOf R).map (QuotientGroup.mk' N) with hH
  have : H.Normal := hTn.map _ (QuotientGroup.mk'_surjective N)
  obtain ⟨t₀, ht₀, ht₀A⟩ := hS.exists_mem_T₁_not_mem_gmsA
  have hH1 : H ≠ ⊥ := by
    intro hb
    have hmem : QuotientGroup.mk' N ⟨t₀, hTR (mem_inf.mp ht₀).1⟩ ∈ H :=
      mem_map_of_mem _ (mem_subgroupOf.mpr (mem_inf.mp ht₀).1)
    rw [hb, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at hmem
    apply ht₀A
    rw [← hS.sec3.gmsV_inf_eq hS.oddCenter]
    exact mem_inf.mpr ⟨hmem, (mem_inf.mp ht₀).2⟩
  obtain ⟨⟨z, hz⟩, hz1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hH1)
  obtain ⟨hzH, hzc⟩ := mem_inf.mp hz
  obtain ⟨⟨t, htR⟩, htT, rfl⟩ := mem_map.mp hzH
  refine ⟨t, mem_subgroupOf.mp htT, fun htV => hz1 ?_, fun r hr => ?_⟩
  · exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr htV))
  · have hc := mem_center_iff.mp hzc (QuotientGroup.mk' N ⟨r, hr⟩)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, mem_subgroupOf] at hc
    have hc' : t⁻¹ * r⁻¹ * (t * r) ∈ gmsV L T := by simpa [mul_assoc] using hc
    have e : r * t * r⁻¹ * t⁻¹ = (t * r) * (t⁻¹ * r⁻¹ * (t * r))⁻¹ * (t * r)⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.mp (hS.isR.le_normalizer_gmsV (mul_mem (hTR htT) hr)) _).mp
      (inv_mem hc')

theorem conj_mul_inv_mem_of_mem_T
    {t : G} (ht : t ∈ T) {r : G} (hr : r ∈ R) : r * t * r⁻¹ * t⁻¹ ∈ gmsV L T := by
  by_cases htV : t ∈ gmsV L T
  · exact mem_sup_left (conj_mul_inv_mem (hS.isR.le_gmsTrans hr) htV)
  obtain ⟨t₀, ht₀T, ht₀V, ht₀c⟩ := hS.exists_central
  obtain ⟨t₁, ht₁, s, hs, rfl⟩ := hS.exists_mul_of_mem_T ht
  obtain ⟨u₁, hu₁, s₀, hs₀, rfl⟩ := hS.exists_mul_of_mem_T ht₀T
  have hnotA : ∀ x ∈ T ⊓ L, ∀ w ∈ T ⊓ centralizer (L : Set G), x * w ∉ gmsV L T →
      x ∉ gmsA L T := fun x _ w hw hxw hx => hxw (mul_mem (mem_sup_left hx) (mem_sup_right hw))
  obtain ⟨k, hk⟩ := hS.sec3.exists_pow_conj_mem_of_sz hS.foundation hS.oddCenter hS.one_le
    hS.iso.some hS.torus hS.mem_normalizer_gmsW hS.conj_eq hu₁ (hnotA _ hu₁ _ hs₀ ht₀V) ht₁
    (hnotA _ ht₁ _ hs htV)
  set c := (d ^ k)⁻¹ * (u₁ * s₀) * d ^ k with hc
  have hdk : ∀ g ∈ R, (d ^ k) * g * (d ^ k)⁻¹ ∈ R := fun g hg =>
    (mem_normalizer_iff.mp (pow_mem hS.mem_normalizer k) g).mp hg
  have hdkV : ∀ v ∈ gmsV L T, (d ^ k)⁻¹ * v * d ^ k ∈ gmsV L T := fun v hv => by
    have := (mem_normalizer_iff.mp (inv_mem (pow_mem hS.mem_normalizer_gmsV k)) v).mp hv
    simpa using this
  have hcc : ∀ r ∈ R, r * c * r⁻¹ * c⁻¹ ∈ gmsV L T := by
    intro r hr
    have e : r * c * r⁻¹ * c⁻¹ = (d ^ k)⁻¹ * ((d ^ k * r * (d ^ k)⁻¹) * (u₁ * s₀) *
        (d ^ k * r * (d ^ k)⁻¹)⁻¹ * (u₁ * s₀)⁻¹) * d ^ k := by rw [hc]; group
    rw [e]
    exact hdkV _ (ht₀c _ (hdk r hr))
  have hs₀c : (d ^ k)⁻¹ * s₀ * d ^ k = s₀ := by
    have h1 : Commute d s₀ := by
      have := hS.commute_T₀ hs₀
      calc d * s₀ = d * s₀ * d⁻¹ * d := by group
        _ = s₀ * d := by rw [this]
    rw [mul_assoc, ← (h1.pow_left k).eq]
    group
  have hcv : c⁻¹ * (t₁ * s) ∈ gmsV L T := by
    have e : c = ((d ^ k)⁻¹ * u₁ * d ^ k) * ((d ^ k)⁻¹ * s₀ * d ^ k) := by rw [hc]; group
    rw [e, hs₀c]
    have e2 : ((d ^ k)⁻¹ * u₁ * d ^ k * s₀)⁻¹ * (t₁ * s) =
        s₀⁻¹ * (t₁⁻¹ * ((d ^ k)⁻¹ * u₁ * d ^ k))⁻¹ * s := by group
    rw [e2]
    exact mul_mem (mul_mem (inv_mem (mem_sup_right hs₀)) (inv_mem (mem_sup_left hk)))
      (mem_sup_right hs)
  set v := c⁻¹ * (t₁ * s) with hv
  have hcT : c ∈ T := by
    have h1 : (d ^ k)⁻¹ ∈ normalizer (T : Set G) := by
      rw [hS.eq_gmsW]
      exact inv_mem (pow_mem hS.mem_normalizer_gmsW k)
    have := (mem_normalizer_iff.mp h1 _).mp ht₀T
    simpa [hc] using this
  have e : r * (t₁ * s) * r⁻¹ * (t₁ * s)⁻¹ =
      (r * c * r⁻¹ * c⁻¹) * (c * (r * v * r⁻¹ * v⁻¹) * c⁻¹) := by rw [hv]; group
  rw [e]
  refine mul_mem (hcc r hr) ?_
  have hrv : r * v * r⁻¹ * v⁻¹ ∈ gmsV L T :=
    mem_sup_left (conj_mul_inv_mem (hS.isR.le_gmsTrans hr) hcv)
  exact (mem_normalizer_iff.mp ((hS.T_le.trans hS.isR.le_normalizer_gmsV) hcT) _).mp hrv

theorem sq_mem_gmsV
    (h34 : NoStronglyClosedAbelian G) {r : G} (hr : r ∈ R) : r ^ 2 ∈ gmsV L T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsq : ∀ t ∈ T, t ^ 2 ∈ gmsV L T := fun t ht => mem_sup_left (hS.sq_mem_gmsA_of_mem_T ht)
  have hnotW : ∀ x, x ∉ T → x ∉ gmsW L T := fun x hx hxW =>
    hx (by rw [hS.eq_gmsW]; exact hxW)
  by_cases hA : ∃ r₀ ∈ R, r₀ ∉ T ∧ r₀ ^ 2 ∈ gmsV L T
  · obtain ⟨r₀, hr₀, hr₀T, hr₀V⟩ := hA
    by_cases hrT : r ∈ T
    · exact hTsq r hrT
    obtain ⟨k, hk⟩ := hS.isR.exists_pow_conj_mem hS.lemma313 hS.facts hS.sec3 hS.foundation
      hS.inf_centralizer hS.torus hS.mem_normalizer hS.mem_normalizer_gmsW hS.conj_eq hr₀
      (hnotW r₀ hr₀T) hr (hnotW r hrT)
    set c := (d ^ k)⁻¹ * r₀ * d ^ k with hc
    have hwT : r⁻¹ * c ∈ T := by rw [hS.eq_gmsW]; exact hk
    have hc2 : c ^ 2 ∈ gmsV L T := by
      have e : c ^ 2 = (d ^ k)⁻¹ * r₀ ^ 2 * d ^ k := by rw [hc, sq, sq]; group
      rw [e]
      have := (mem_normalizer_iff.mp (inv_mem (pow_mem hS.mem_normalizer_gmsV k)) _).mp hr₀V
      simpa using this
    have hv₁ := hS.conj_mul_inv_mem_of_mem_T hwT (inv_mem hr)
    have hw2 := hTsq _ hwT
    have e : r ^ 2 = c * c * (r⁻¹ * c * (r⁻¹ * c))⁻¹ *
        (r⁻¹ * (r⁻¹ * c) * r⁻¹⁻¹ * (r⁻¹ * c)⁻¹)⁻¹ := by group
    rw [e]
    rw [sq] at hc2 hw2
    exact mul_mem (mul_mem hc2 (inv_mem hw2)) (inv_mem hv₁)
  · exfalso
    push Not at hA
    obtain ⟨-, hVel, -, -, hΩ⟩ := hS.facts.vFacts hS.sec3 hS.foundation
    have hinv : ∀ x ∈ R, x ^ 2 = 1 → x ∈ gmsV L T := by
      intro x hx hx2
      by_cases hxT : x ∈ T
      · exact hΩ x (by rw [hS.eq_gmsW] at hxT; exact hxT) hx2
      · exact absurd (hx2 ▸ one_mem _) (hA x hx hxT)
    have hVsq : ∀ v ∈ gmsV L T, v ^ 2 = 1 := hVel.2
    have hconj : ∀ v ∈ gmsV L T, ∀ g : G, (g * v * g⁻¹) ^ 2 = 1 := fun v hv g => by
      have : (g * v * g⁻¹) ^ 2 = g * v ^ 2 * g⁻¹ := by rw [sq, sq]; group
      rw [this, hVsq v hv]
      group
    have hNR : normalizer (R : Set G) ≤ normalizer (gmsV L T : Set G) := fun g hg =>
      mem_normalizer_of_conj_mem_of_finite fun v hv =>
        hinv _ ((mem_normalizer_iff.mp hg v).mp (hS.gmsV_le_R hv)) (hconj v hv g)
    have hRG : IsSylowOf 2 R ⊤ := by
      by_contra hnot
      obtain ⟨S, hRS, z, hzS, hzN, hzR⟩ :=
        exists_mem_normalizer_of_not_isSylowOf hS.isR.isPGroup hnot
      have hP : IsPGroup 2 (R ⊔ zpowers z : Subgroup G) :=
        S.isPGroup'.to_le (sup_le hRS (zpowers_le.mpr hzS))
      have heq := hS.isSylowOf_normalizer.eq_of_le le_sup_left
        (sup_le hS.isR.le_normalizer_gmsV (zpowers_le.mpr (hNR hzN))) hP
      exact hzR (heq ▸ mem_sup_right (mem_zpowers z))
    obtain ⟨-, hR2, hRidx⟩ := isSylowOf_iff.mp hRG
    rw [relIndex_top_right] at hRidx
    let S : Sylow 2 G := hR2.toSylow hRidx
    have hSc : (S : Subgroup G) = R := IsPGroup.toSylow_coe hR2 hRidx
    have hV1 : gmsV L T ≠ ⊥ := fun hb =>
      hS.sec3.T₀_ne_bot (le_bot_iff.mp (hb ▸ le_sup_right))
    refine h34 S (gmsV L T) (hSc ▸ hS.gmsV_le_R) hVel.1 hV1 fun v hv g hg => ?_
    have h2 : (g⁻¹ * v * g) ^ 2 = 1 := by simpa using hconj v hv g⁻¹
    exact hinv _ (hSc ▸ hg) h2

theorem commutator_mem_gmsV
    (h34 : NoStronglyClosedAbelian G) {x y : G} (hx : x ∈ R) (hy : y ∈ R) :
    x * y * x⁻¹ * y⁻¹ ∈ gmsV L T :=
  commutator_mem_of_sq_mem hS.isR.le_normalizer_gmsV hy (hS.sq_mem_gmsV h34 hx)
    (hS.sq_mem_gmsV h34 hy) (hS.sq_mem_gmsV h34 (mul_mem hx hy))

end SzR

end Sec3

end CFSG.ComponentClassification.GMS78
