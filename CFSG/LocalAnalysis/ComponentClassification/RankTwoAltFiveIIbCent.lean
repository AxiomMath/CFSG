module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveEps
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbIso

public section

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

namespace CFSG.ComponentClassification.RankTwoAltFive

namespace IIbSyl

@[expose] def g1 : IIbSyl :=
  SemidirectProduct.inl (SemidirectProduct.inl (Multiplicative.ofAdd (1, 0)))

@[expose] def g2 : IIbSyl :=
  SemidirectProduct.inl (SemidirectProduct.inl (Multiplicative.ofAdd (0, 1)))

@[expose] def c2 : IIbSyl := g2 * a

@[expose] def c3 : IIbSyl := g1 * g2 * a

theorem sigma_mem_R : sigma ∈ R := ⟨Multiplicative.ofAdd (0, 1), rfl⟩

theorem sigma_ne_one : sigma ≠ 1 := by decide

theorem sigma_ne_a : sigma ≠ a := by decide

theorem chi_sigma : chi sigma ≠ 1 := by decide

theorem chi_a : chi a = 1 := by decide

theorem chi_v0Hom : ∀ w, chi (v0Hom w) = 1 := by decide

theorem chi_mul_sigma : ∀ s, chi s ≠ 1 → chi (s * sigma) = 1 := by decide +kernel

theorem inr_eq_pow : ∀ e : Multiplicative (ZMod 2),
    (SemidirectProduct.inr e : IIbSyl) = t ^ (Multiplicative.toAdd e).val := by decide

theorem eq_mul_pow (s : IIbSyl) : s = g1 ^ (Multiplicative.toAdd s.left.left).1.val *
    g2 ^ (Multiplicative.toAdd s.left.left).2.val * a ^ (Multiplicative.toAdd s.left.right).1.val *
    sigma ^ (Multiplicative.toAdd s.left.right).2.val * t ^ (Multiplicative.toAdd s.right).val := by
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right s,
    ← SemidirectProduct.inl_left_mul_inr_right s.left, C0_eq_mul s.left.left,
    R0_eq_mul s.left.right, inr_eq_pow]
  rw [a_eq_inl, sigma_eq_inl, g1, g2]
  simp only [map_mul, map_pow, mul_assoc]

theorem chi_eq_one_iff : ∀ s : IIbSyl, chi s = 1 ↔ (Multiplicative.toAdd s.left.right).2 = 0 := by
  decide +kernel

theorem c2_conj_t : c2⁻¹ * (t * c2 * t⁻¹) = g1 := by decide

theorem c1_eq_g1_mul : c1 = g1 * a := by decide

theorem c1_sq : c1 * c1 = 1 := by decide

theorem c2_sq : c2 * c2 = 1 := by decide

theorem c3_sq : c3 * c3 = 1 := by decide

theorem mem_P_c1 : c1 ∈ P := ⟨⟨Multiplicative.ofAdd (1, 0), Multiplicative.ofAdd (1, 0)⟩, rfl⟩

theorem mem_P_c2 : c2 ∈ P := ⟨⟨Multiplicative.ofAdd (0, 1), Multiplicative.ofAdd (1, 0)⟩, by
  decide⟩

theorem mem_P_c3 : c3 ∈ P := ⟨⟨Multiplicative.ofAdd (1, 1), Multiplicative.ofAdd (1, 0)⟩, by
  decide⟩

theorem c1_not_mem_V : c1 ∉ V := by
  change c1 ∉ vHom.range
  decide

theorem c2_not_mem_V : c2 ∉ V := by
  change c2 ∉ vHom.range
  decide

theorem c3_not_mem_V : c3 ∉ V := by
  change c3 ∉ vHom.range
  decide

theorem c1_inv_mul_c2_not_mem_V : c1⁻¹ * c2 ∉ V := by
  change c1⁻¹ * c2 ∉ vHom.range
  decide

theorem c3_inv_mul_mem_V : c3⁻¹ * (c1 * c2) ∈ V := by
  change c3⁻¹ * (c1 * c2) ∈ vHom.range
  decide

theorem mem_V_of_cent : ∀ s : IIbSyl, s * s = 1 →
    (∀ u ∈ [(⟨⟨Multiplicative.ofAdd (0, 1), Multiplicative.ofAdd (0, 1)⟩, 1⟩ : IIbSyl),
      ⟨⟨Multiplicative.ofAdd (0, 1), Multiplicative.ofAdd (1, 1)⟩, 1⟩,
      ⟨⟨Multiplicative.ofAdd (0, 2), 1⟩, Multiplicative.ofAdd 1⟩,
      ⟨⟨Multiplicative.ofAdd (1, 0), 1⟩, 1⟩,
      ⟨⟨Multiplicative.ofAdd (1, 0), Multiplicative.ofAdd (1, 1)⟩, 1⟩,
      ⟨⟨Multiplicative.ofAdd (1, 2), 1⟩, Multiplicative.ofAdd 1⟩], u * s = s * u → u * u = 1) →
    s ∈ vHom.range ∧ chi s ≠ 1 := by
  decide +kernel

theorem index_S0 : S0.index = 2 := by
  have hsurj : Function.Surjective chi := fun e => by
    have hcases : ∀ e : Multiplicative (ZMod 2), e = 1 ∨ e = Multiplicative.ofAdd 1 := by decide
    rcases hcases e with rfl | rfl
    · exact ⟨1, map_one _⟩
    · exact ⟨sigma, by decide⟩
  rw [S0, index_ker, MonoidHom.range_eq_top.mpr hsurj, card_top, Nat.card_eq_fintype_card]
  rfl

theorem V0_le_S0 : V0 ≤ S0 := by
  rintro _ ⟨w, rfl⟩
  exact chi_v0Hom w

theorem pow_128 (s : IIbSyl) : s ^ 2 ^ 7 = 1 := by
  have h := pow_card_eq_one (G := IIbSyl) (x := s)
  rwa [show Fintype.card IIbSyl = 2 ^ 7 by
    rw [← Nat.card_eq_fintype_card, card_IIbSyl]; rfl] at h

end IIbSyl

namespace Setting310

variable {G : Type} [Group G] [Finite G] {A R T V₀ : Subgroup G} {g : G}
  (h : Setting310 A R g T V₀)
include h

theorem mem_normalizer_R_of_le {q : G} (hqV : q ∈ normalizer ((R ⊔ T : Subgroup G) : Set G))
    (hqK : q ∈ normalizer (centralizer (A : Set G) : Set G)) : q ∈ normalizer (R : Set G) := by
  have hmem : ∀ {u : G}, u ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) →
      u ∈ normalizer (centralizer (A : Set G) : Set G) → ∀ r ∈ R, u * r * u⁻¹ ∈ R := by
    intro u huV huK r hr
    have h1 : u * r * u⁻¹ ∈ (R ⊔ T) ⊓ centralizer (A : Set G) :=
      mem_inf.mpr ⟨(mem_normalizer_iff.mp huV r).mp (mem_sup_left hr),
        (mem_normalizer_iff.mp huK r).mp (h.sylowR.le hr)⟩
    rwa [h.inf_K] at h1
  rw [mem_normalizer_iff]
  intro r
  constructor
  · exact hmem hqV hqK r
  · intro hr
    have := hmem (inv_mem hqV) (inv_mem hqK) _ hr
    rwa [show q⁻¹ * (q * r * q⁻¹) * q⁻¹⁻¹ = r by group] at this

section IIb

variable (hIIb : centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
include hIIb

theorem inf_sup_eq_of_le_centralizer {σ : G} (hσ : σ ∈ R) (hσ1 : σ ≠ 1) {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (hQC : Q ≤ centralizer ({σ} : Set G)) (hVQ : R ⊔ T ≤ Q) :
    Q ⊓ (A ⊔ centralizer (A : Set G)) = R ⊔ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eA⟩ := h.equiv
  have hσK : σ ∈ centralizer (A : Set G) := h.sylowR.le hσ
  have hσ2 : σ * σ = 1 := h.mul_self (mem_sup_left hσ)
  have hCN : centralizer ({σ} : Set G) ≤ normalizer (A : Set G) := by
    have := centralizer_le_normalizer_conj h.hyp.standard 1
      (by rw [rightConjugate_one]; exact hσK) hσ1 hσ2
    rwa [rightConjugate_one] at this
  have hQN : Q ≤ normalizer (A : Set G) := hQC.trans hCN
  have hQK : Q ≤ normalizer (centralizer (A : Set G) : Set G) := by
    rw [normalizer_centralizer_eq h.hyp.standard]
    exact hQN
  have hVAK : R ⊔ T ≤ A ⊔ centralizer (A : Set G) := by
    rw [← h.sup_R_V₀]
    exact sup_le (h.sylowR.le.trans le_sup_right) (h.V₀_le_A.trans le_sup_left)
  have hNR : ∀ {q : G}, q ∈ Q → q ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) →
      q ∈ normalizer (R : Set G) := fun hq hqV => h.mem_normalizer_R_of_le hqV (hQK hq)
  by_contra hne
  have hlt : R ⊔ T < Q ⊓ (A ⊔ centralizer (A : Set G)) :=
    lt_of_le_of_ne (le_inf hVQ hVAK) (Ne.symm hne)
  obtain ⟨q, hq, hqV⟩ :=
    IsConcreteLE.exists_of_lt (lt_inf_normalizer (hQ.to_le inf_le_left) hlt)
  obtain ⟨hq₀, hqN⟩ := mem_inf.mp hq
  obtain ⟨hqQ, hqAK⟩ := mem_inf.mp hq₀
  obtain ⟨a, ha, k, hk, hak⟩ := exists_mul_of_mem_sup hqAK
  apply hqV
  rw [← hak] at hqQ hqN ⊢
  obtain ⟨n, hn⟩ := hQ ⟨a * k, hqQ⟩
  have hn' : (a * k) ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hcomm : Commute a k := mem_centralizer_iff.mp hk a ha
  have hpow : a ^ 2 ^ n * k ^ 2 ^ n = 1 := by rw [← hcomm.mul_pow, hn']
  have ha1 : a ^ 2 ^ n = 1 := by
    have hmem : a ^ 2 ^ n ∈ A ⊓ centralizer (A : Set G) := by
      refine mem_inf.mpr ⟨pow_mem ha _, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hpow]
      exact inv_mem (pow_mem hk _)
    rw [inf_centralizer_eq_bot eA] at hmem
    exact mem_bot.mp hmem
  have hk1 : k ^ 2 ^ n = 1 := by
    rw [ha1, one_mul] at hpow
    exact hpow
  have hqV₀ : a * k ∈ normalizer (V₀ : Set G) := h.normalizer_le_normalizer_V₀ hqN
  have haN : a ∈ normalizer (V₀ : Set G) := by
    have hkV₀ : k ∈ normalizer (V₀ : Set G) :=
      centralizer_le_normalizer _ (centralizer_le h.V₀_le_A hk)
    have := mul_mem hqV₀ (inv_mem hkV₀)
    rwa [mul_inv_cancel_right] at this
  have haV₀ : a ∈ V₀ := by
    have hp : IsPGroup 2 (zpowers a ⊔ V₀ : Subgroup G) :=
      (isPGroup_zpowers_of_pow_eq_one ha1).to_sup_of_normal_right' h.loc.sylowV₀.isPGroup
        (zpowers_le.mpr haN)
    have heq := h.loc.sylowV₀.eq_of_le le_sup_right
      (sup_le (zpowers_le.mpr ha) h.loc.sylowV₀.le) hp
    exact heq ▸ mem_sup_left (mem_zpowers a)
  have haR : a ∈ centralizer (R : Set G) := le_centralizer_iff.mp h.sylowR.le ha
  have hkN : k ∈ normalizer (R : Set G) := by
    have := mul_mem (inv_mem (centralizer_le_normalizer _ haR)) (hNR hqQ hqN)
    rwa [inv_mul_cancel_left] at this
  have hkC : k ∈ centralizer (R : Set G) := hIIb (mem_inf.mpr ⟨hk, hkN⟩)
  have hkR : k ∈ R := by
    have hp : IsPGroup 2 (R ⊔ zpowers k : Subgroup G) :=
      h.sylowR.isPGroup.to_sup_of_normal_left' (isPGroup_zpowers_of_pow_eq_one hk1)
        (zpowers_le.mpr (centralizer_le_normalizer _ hkC))
    have heq := h.sylowR.eq_of_le le_sup_left (sup_le h.sylowR.le (zpowers_le.mpr hk)) hp
    exact heq ▸ mem_sup_right (mem_zpowers k)
  exact mul_mem (h.V₀_le haV₀) (mem_sup_left hkR)

end IIb

section Outer

variable {P : Subgroup G} {x z r₁ : G} (hx : OuterInvol R T V₀ P x z r₁)
include hx

theorem outer_not_mem_sup : x ∉ A ⊔ centralizer (A : Set G) := by
  intro hxA
  obtain ⟨a, ha, k, hk, hak⟩ := exists_mul_of_mem_sup hxA
  apply h.outer_not_inner hx
  refine ⟨a, ha, fun y hy => ?_⟩
  have hky : k * y = y * k := (mem_centralizer_iff.mp hk y hy).symm
  rw [← hak]
  calc a * k * y * (a * k)⁻¹ = a * (k * y) * k⁻¹ * a⁻¹ := by group
    _ = a * (y * k) * k⁻¹ * a⁻¹ := by rw [hky]
    _ = a * y * a⁻¹ := by group

variable (hIIb : centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
include hIIb

theorem eq_of_le_centralizer_sigma {σ : G} (hσ : σ ∈ R) (hσ1 : σ ≠ 1) (hσr : σ ≠ r₁)
    {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQC : Q ≤ centralizer ({σ} : Set G))
    (hVQ : R ⊔ T ≤ Q) : Q = R ⊔ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσK : σ ∈ centralizer (A : Set G) := h.sylowR.le hσ
  have hσ2 : σ * σ = 1 := h.mul_self (mem_sup_left hσ)
  have hCN : centralizer ({σ} : Set G) ≤ normalizer (A : Set G) := by
    have := centralizer_le_normalizer_conj h.hyp.standard 1
      (by rw [rightConjugate_one]; exact hσK) hσ1 hσ2
    rwa [rightConjugate_one] at this
  have hQK : Q ≤ normalizer (centralizer (A : Set G) : Set G) := by
    rw [normalizer_centralizer_eq h.hyp.standard]
    exact hQC.trans hCN
  have hQ₀ := h.inf_sup_eq_of_le_centralizer hIIb hσ hσ1 hQ hQC hVQ
  by_contra hne
  have hlt : R ⊔ T < Q := lt_of_le_of_ne hVQ (Ne.symm hne)
  obtain ⟨q, hq, hqV⟩ := IsConcreteLE.exists_of_lt (lt_inf_normalizer hQ hlt)
  obtain ⟨hqQ, hqN⟩ := mem_inf.mp hq
  have hqA : q ∉ A ⊔ centralizer (A : Set G) := fun h1 =>
    hqV (hQ₀ ▸ mem_inf.mpr ⟨hqQ, h1⟩)
  have h1 := h.conj_eq_of_not_mem_sup hIIb (h.mem_normalizer_R_of_le hqN (hQK hqQ)) hx.normR hqA
    (h.outer_not_mem_sup hx) hσ
  rw [h.outer_conj_R_of_ne hx hσ hσ1 hσr] at h1
  have h2 : q * σ * q⁻¹ = σ := by
    rw [mem_centralizer_singleton_iff.mp (hQC hqQ)]
    group
  rw [h2] at h1
  apply hx.r_ne
  calc r₁ = σ⁻¹ * (σ * r₁) := by group
    _ = 1 := by rw [← h1]; group

theorem isSylowOf_centralizer_sigma {σ : G} (hσ : σ ∈ R) (hσ1 : σ ≠ 1) (hσr : σ ≠ r₁) :
    IsSylowOf 2 (R ⊔ T) (centralizer ({σ} : Set G)) := by
  have hVC : R ⊔ T ≤ centralizer ({σ} : Set G) := fun v hv =>
    mem_centralizer_singleton_iff.mpr (h.comm hv (mem_sup_left hσ))
  have hV2 : IsPGroup 2 (R ⊔ T : Subgroup G) := IsPGroup.of_card (n := 4) (by rw [h.loc.card]; rfl)
  obtain ⟨S, hS, hVS⟩ := exists_isSylowOf_le hVC hV2
  rwa [← h.eq_of_le_centralizer_sigma hx hIIb hσ hσ1 hσr hS.isPGroup hS.le hVS]

theorem mul_self_eq_one_of_conj {σ : G} (hσ : σ ∈ R) (hσ1 : σ ≠ 1) (hσr : σ ≠ r₁) (y : G)
    {u : G} (hu : u ∈ centralizer ({y⁻¹ * σ * y} : Set G)) (hu2 : IsPGroup 2 (zpowers u)) :
    u * u = 1 := by
  obtain ⟨n, hn⟩ := hu2 ⟨u, mem_zpowers u⟩
  have hn' : u ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hu' : y * u * y⁻¹ ∈ centralizer ({σ} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h1 := mem_centralizer_singleton_iff.mp hu
    calc y * u * y⁻¹ * σ = y * (u * (y⁻¹ * σ * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * σ * y) * u) * y⁻¹ := by rw [h1]
      _ = σ * (y * u * y⁻¹) := by group
  have hu'2 : IsPGroup 2 (zpowers (y * u * y⁻¹)) := by
    apply isPGroup_zpowers_of_pow_eq_one (n := n)
    rw [conj_pow, hn']
    group
  have h1 := mul_self_eq_one_of_isSylowOf (h.isSylowOf_centralizer_sigma hx hIIb hσ hσ1 hσr)
    (fun e he => h.mul_self he) hu' hu'2
  calc u * u = y⁻¹ * (y * u * y⁻¹ * (y * u * y⁻¹)) * y := by group
    _ = 1 := by rw [h1]; group

theorem sigma_conj_of_hom {f : IIbSyl →* G} (hfinj : Function.Injective f)
    (hfrange : f.range = P ⊔ zpowers x) (hfV : IIbSyl.V.map f = R ⊔ T) (hσ : f IIbSyl.sigma ∈ R)
    (hσ1 : f IIbSyl.sigma ≠ 1) (hσr : f IIbSyl.sigma ≠ r₁) (y : G)
    (hy : y⁻¹ * f IIbSyl.sigma * y ∈ P ⊔ zpowers x) :
    y⁻¹ * f IIbSyl.sigma * y ∈ R ⊔ T ∧ y⁻¹ * f IIbSyl.sigma * y ∉ IIbSyl.S0.map f := by
  rw [← hfrange] at hy
  obtain ⟨s, hs⟩ := hy
  have hσ2 : f IIbSyl.sigma * f IIbSyl.sigma = 1 := h.mul_self (mem_sup_left hσ)
  have hs2 : s * s = 1 := by
    apply hfinj
    rw [map_mul, hs, map_one]
    calc y⁻¹ * f IIbSyl.sigma * y * (y⁻¹ * f IIbSyl.sigma * y) =
        y⁻¹ * (f IIbSyl.sigma * f IIbSyl.sigma) * y := by group
      _ = 1 := by rw [hσ2]; group
  have hcent : ∀ u : IIbSyl, u * s = s * u → u * u = 1 := by
    intro u hus
    apply hfinj
    rw [map_mul, map_one]
    refine h.mul_self_eq_one_of_conj hx hIIb hσ hσ1 hσr y ?_ ?_
    · rw [mem_centralizer_singleton_iff, ← hs, ← map_mul, ← map_mul, hus]
    · apply isPGroup_zpowers_of_pow_eq_one (n := 7)
      rw [← map_pow, IIbSyl.pow_128, map_one]
  obtain ⟨hsV, hsχ⟩ := IIbSyl.mem_V_of_cent s hs2 (fun u _ => hcent u)
  rw [← hs]
  exact ⟨hfV ▸ mem_map_of_mem f hsV, fun hmem => hsχ ((mem_map_iff_mem hfinj).mp hmem)⟩

theorem sigma_conj_of_hom' {f : IIbSyl →* G} (hfinj : Function.Injective f)
    (hfrange : f.range = P ⊔ zpowers x) (hfV0 : IIbSyl.V0.map f = V₀)
    (hfV : IIbSyl.V.map f = R ⊔ T) (hfa : f IIbSyl.a = r₁) (hσ : f IIbSyl.sigma ∈ R)
    (hσ1 : f IIbSyl.sigma ≠ 1) (hσr : f IIbSyl.sigma ≠ r₁) (y : G)
    (hy : y⁻¹ * f IIbSyl.sigma * y ∈ P ⊔ zpowers x) :
    y⁻¹ * f IIbSyl.sigma * y ∈ R ⊔ T ∧ y⁻¹ * f IIbSyl.sigma * y ∉ V₀ ⊔ zpowers r₁ := by
  obtain ⟨h1, h2⟩ := h.sigma_conj_of_hom hx hIIb hfinj hfrange hfV hσ hσ1 hσr y hy
  refine ⟨h1, fun hmem => h2 ?_⟩
  have hle : V₀ ⊔ zpowers r₁ ≤ IIbSyl.S0.map f := by
    rw [← hfV0, ← hfa, ← MonoidHom.map_zpowers, ← Subgroup.map_sup]
    exact map_mono (sup_le IIbSyl.V0_le_S0 (zpowers_le.mpr IIbSyl.chi_a))
  exact hle hmem

end Outer

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
