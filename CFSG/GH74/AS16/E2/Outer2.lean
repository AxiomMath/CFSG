module

public import CFSG.GH74.AS16.E2.Outer1
public import CFSG.GH74.AS16.E2.Delta3

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.LiteratureLocal.TightCommuting CFSG.ABGLocalTools
open CFSG.GH74.E2 hiding Hyp
open CFSG.GH74.AS16 (Pair LNormal InDelta lemma1642_one lemma1642_three lemma1642_four
  lemma1652_one delta_nonempty inDelta_rightConjugate conjugate_centralizer
  conjugate_centralizer_singleton isCompIn_conj conjugate_eq_self_iff zpow_eq_one_or_self)
open CFSG.GH74.Uniqueness (S_CorZD)

section Interface

variable {G : Type*} [Group G]

structure OuterSub (L : Subgroup G) : Prop where
  outer_cent3 : ∀ r ∈ normalizer (L : Set G), r ^ 2 = 1 → ¬ InnerAt L r →
    ∀ y ∈ normalizer (L : Set G), (∀ c ∈ L, orderOf c = 3 → c * r = r * c → y * c = c * y) →
      y ∈ centralizer (L : Set G) ∨ r⁻¹ * y ∈ centralizer (L : Set G)
  bang : ∀ r ∈ normalizer (L : Set G), r ^ 2 = 1 → ¬ InnerAt L r →
    ∃ l ∈ L, ∃ c₁ ∈ L, ∃ c₂ ∈ L, orderOf c₁ = 3 ∧ orderOf c₂ = 3 ∧ c₁ * r = r * c₁ ∧
      c₂ * r = r * c₂ ∧ (c₁ * c₂) ^ 2 = 1 ∧ c₁ * c₂ ≠ 1 ∧ r⁻¹ * l * r * l⁻¹ = c₁ * c₂
  inner_sq : ∀ v ∈ L, orderOf v = 2 → ∀ y ∈ normalizer (L : Set G),
    (∀ c ∈ L, orderOf c = 3 → c * v = v * c → y * c = c * y) →
      (y ^ 2 ∈ centralizer (L : Set G) ∨ v⁻¹ * y ^ 2 ∈ centralizer (L : Set G)) ∧
      (InnerAt L y → y ^ 2 ∈ centralizer (L : Set G) →
        y ∈ centralizer (L : Set G) ∨ v⁻¹ * y ∈ centralizer (L : Set G))

structure OuterSylow (L Q : Subgroup G) : Prop where
  exists_s : ∃ s ∈ Q, s ≠ 1 ∧ s ^ 2 = 1 ∧ (∀ q ∈ Q, q * s = s * q) ∧
    (∀ a ∈ Q, (∀ q ∈ Q, q * a = a * q) → a ^ 2 = 1 → a = 1 ∨ a = s) ∧
    (∀ y ∈ normalizer (L : Set G), (∀ q ∈ Q, y * q = q * y) →
      ∃ a ∈ Q, (∀ q ∈ Q, q * a = a * q) ∧ a⁻¹ * y ∈ centralizer (L : Set G)) ∧
    (∃ a ∈ L, ∃ b ∈ L, orderOf a = 3 ∧ orderOf b = 3 ∧ a * s = s * a ∧ b * s = s * b ∧
      (a * b) ^ 3 = s)
  sq : ∀ y ∈ normalizer (L : Set G), ¬ InnerAt L y → (∀ q ∈ Q, y * q * y⁻¹ ∈ Q) →
    ∀ v ∈ Q, orderOf v = 2 → (∀ c ∈ L, orderOf c = 3 → c * v = v * c → y * c = c * y) →
    v⁻¹ * y ^ 2 ∈ centralizer (L : Set G) → ∀ q ∈ Q, q * v = v * q
  conj4 : ∀ a ∈ Q, orderOf a = 4 →
    (∀ c ∈ L, orderOf c = 3 → c * a ^ 2 = a ^ 2 * c → c * a = a * c) →
    ∃ k ∈ L, k⁻¹ * a * k ∈ Q ∧ ∀ y ∈ Q, y * (k⁻¹ * a * k) = (k⁻¹ * a * k) * y

end Interface

section PartA

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {z : G} {L : Subgroup G}

omit [Finite G] in
theorem mem_conj_centralizer {g x : G}
    (hx : x ∈ (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom) :
    g⁻¹ * x * g ∈ centralizer (L : Set G) := by
  obtain ⟨y, hy, rfl⟩ := hx
  have : g⁻¹ * ((MulAut.conj g).toMonoidHom y) * g = y := by
    show g⁻¹ * (g * y * g⁻¹) * g = y
    group
  rw [this]
  exact hy

theorem Cfg.R_le_of_outer (h : Cfg G T z L) (hterm : GLS.IsTerminalPair 2 z L)
    (hZ : center ↥L = ⊥) (hR3 : Rank3Sub L) (hO : OuterSub L)
    {K' R : Subgroup G} (hK' : InDelta (centralizer (L : Set G)) K')
    (hR : IsSylowOf 2 R (K' ⊓ normalizer (centralizer (L : Set G) : Set G)))
    (hRT : R ≤ (T : Subgroup G)) {r : G} (hrR : r ∈ R) (hr2 : orderOf r = 2)
    (hrout : ¬ InnerAt L r) : ∀ ρ ∈ R, ρ = 1 ∨ ρ = r := by
  have hstd := h.isStandard' hterm hZ hR3
  have hN := h.lNormal
  have hRD : R ⊓ centralizer (L : Set G) = ⊥ :=
    (lemma1642_one h.pair hN hstd hK' hR hRT).inf_eq_bot
  obtain ⟨⟨g, hg⟩, -, -⟩ := hK'
  have hRK' : R ≤ K' := hR.le.trans inf_le_left
  have hmemK : ∀ x ∈ R, g⁻¹ * x * g ∈ centralizer (L : Set G) := by
    intro x hx
    have hx' := hRK' hx
    rw [hg] at hx'
    exact mem_conj_centralizer hx'
  have hZ' := center_trivial hZ
  have hr2' : r ^ 2 = 1 := hr2 ▸ pow_orderOf_eq_one r
  have hrN : r ∈ normalizer (L : Set G) := h.le_normalizer (hRT hrR)
  intro ρ hρ
  have hρN : ρ ∈ normalizer (L : Set G) := h.le_normalizer (hRT hρ)
  have hfix : ∀ c ∈ L, orderOf c = 3 → c * r = r * c → ρ * c = c * ρ := by
    intro c _ hc3 hcr
    have hc' := h.three_mem_conj hterm hZ' hR3 hr2 (hmemK r hrR) hc3 hcr
    have hcomm := mem_centralizer_iff.1 (hmemK ρ hρ) _ hc'
    calc ρ * c = g * ((g⁻¹ * ρ * g) * (g⁻¹ * c * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * c * g) * (g⁻¹ * ρ * g)) * g⁻¹ := by rw [hcomm]
      _ = c * ρ := by group
  rcases hO.outer_cent3 r hrN hr2' hrout ρ hρN hfix with hD | hD
  · left
    have : ρ ∈ R ⊓ centralizer (L : Set G) := ⟨hρ, hD⟩
    rwa [hRD, mem_bot] at this
  · right
    have : r⁻¹ * ρ ∈ R ⊓ centralizer (L : Set G) := ⟨R.mul_mem (R.inv_mem hrR) hρ, hD⟩
    rw [hRD, mem_bot] at this
    exact (inv_mul_eq_one.1 this).symm

theorem Cfg.exists_inner_in_delta (h : Cfg G T z L) (hterm : GLS.IsTerminalPair 2 z L)
    (hZ : center ↥L = ⊥) (hR3 : Rank3Sub L) (hO : OuterSub L)
    {K' R : Subgroup G} (hK' : InDelta (centralizer (L : Set G)) K')
    (hR : IsSylowOf 2 R (K' ⊓ normalizer (centralizer (L : Set G) : Set G)))
    (hRT : R ≤ (T : Subgroup G)) {r : G} (hrR : r ∈ R) (hr2 : orderOf r = 2)
    (hrout : ¬ InnerAt L r) :
    ∃ K'' : Subgroup G, InDelta (centralizer (L : Set G)) K'' ∧
      ∃ x ∈ K'' ⊓ normalizer (centralizer (L : Set G) : Set G), orderOf x = 2 ∧ InnerAt L x := by
  have hstd := h.isStandard' hterm hZ hR3
  have hZ' := center_trivial hZ
  obtain ⟨⟨g, hg⟩, -, -⟩ := hK'
  have hRK' : R ≤ K' := hR.le.trans inf_le_left
  have hyD : g⁻¹ * r * g ∈ centralizer (L : Set G) := by
    have hr' := hRK' hrR
    rw [hg] at hr'
    exact mem_conj_centralizer hr'
  have hr2' : r ^ 2 = 1 := hr2 ▸ pow_orderOf_eq_one r
  have hrN : r ∈ normalizer (L : Set G) := h.le_normalizer (hRT hrR)
  obtain ⟨l, hl, c₁, hc₁, c₂, hc₂, hc₁3, hc₂3, hc₁r, hc₂r, hw2, hw1, hlr⟩ :=
    hO.bang r hrN hr2' hrout
  have hc₁' := h.three_mem_conj hterm hZ' hR3 hr2 hyD hc₁3 hc₁r
  have hc₂' := h.three_mem_conj hterm hZ' hR3 hr2 hyD hc₂3 hc₂r
  set m : G := g⁻¹ * l * g with hm
  set y : G := g⁻¹ * r * g with hy
  set w₁ : G := g⁻¹ * (c₁ * c₂) * g with hw₁
  have hw₁L : w₁ ∈ L := by
    have : w₁ = (g⁻¹ * c₁ * g) * (g⁻¹ * c₂ * g) := by rw [hw₁]; group
    rw [this]
    exact L.mul_mem hc₁' hc₂'
  have hw₁1 : w₁ ≠ 1 := by
    intro h1
    apply hw1
    have : c₁ * c₂ = g * w₁ * g⁻¹ := by rw [hw₁]; group
    rw [this, h1]
    group
  have hx : y * w₁ = m * y * m⁻¹ := by
    have h1 : l * r * l⁻¹ = r * (c₁ * c₂) := by rw [← hlr]; group
    calc y * w₁ = g⁻¹ * (r * (c₁ * c₂)) * g := by rw [hy, hw₁]; group
      _ = g⁻¹ * (l * r * l⁻¹) * g := by rw [h1]
      _ = m * y * m⁻¹ := by rw [hm, hy]; group
  have hy2 : orderOf y = 2 := by
    rw [hy]
    calc orderOf (g⁻¹ * r * g) = orderOf ((MulAut.conj g⁻¹) r) := by simp
      _ = orderOf r := (MulAut.conj g⁻¹).orderOf_eq r
      _ = 2 := hr2
  have hxo : orderOf (y * w₁) = 2 := by
    rw [hx]
    calc orderOf (m * y * m⁻¹) = orderOf ((MulAut.conj m) y) := by simp
      _ = orderOf y := (MulAut.conj m).orderOf_eq y
      _ = 2 := hy2
  have hxN : y * w₁ ∈ normalizer (L : Set G) :=
    (normalizer (L : Set G)).mul_mem (CFSG.GH74.AS16.centralizer_le_normalizer' L hyD)
      (Subgroup.le_normalizer hw₁L)
  have hxK : y * w₁ ∈ (centralizer (L : Set G)).map (MulAut.conj m).toMonoidHom :=
    ⟨y, hyD, by rw [hx]; rfl⟩
  have hxD : y * w₁ ∈ normalizer (centralizer (L : Set G) : Set G) := by
    rw [hstd.2.2.2.1]
    exact hxN
  refine ⟨(centralizer (L : Set G)).map (MulAut.conj m).toMonoidHom, ⟨⟨m, rfl⟩, ?_, ?_⟩,
    y * w₁, ⟨hxK, hxD⟩, hxo, ?_⟩
  · intro heq
    have hxC : y * w₁ ∈ centralizer (L : Set G) := by rw [← heq]; exact hxK
    apply hw₁1
    apply hZ' w₁ hw₁L
    have : w₁ = y⁻¹ * (y * w₁) := by group
    rw [this]
    exact (centralizer (L : Set G)).mul_mem ((centralizer (L : Set G)).inv_mem hyD) hxC
  · have := Subgroup.orderOf_dvd_natCard
      ((centralizer (L : Set G)).map (MulAut.conj m).toMonoidHom ⊓
        normalizer (centralizer (L : Set G) : Set G)) (show y * w₁ ∈ _ from ⟨hxK, hxD⟩)
    rw [hxo] at this
    exact even_iff_two_dvd.2 this
  · exact (InnerAt.of_centralizer hyD).mul (InnerAt.of_mem hw₁L)

theorem Cfg.exists_inner_delta (hZD : S_CorZD) (h : Cfg G T z L)
    (hterm : GLS.IsTerminalPair 2 z L) (hZ : center ↥L = ⊥) (hR3 : Rank3Sub L)
    (hO : OuterSub L) :
    ∃ K' R : Subgroup G, InDelta (centralizer (L : Set G)) K' ∧
      IsSylowOf 2 R (K' ⊓ normalizer (centralizer (L : Set G) : Set G)) ∧
      R ≤ (T : Subgroup G) ∧ ∀ x ∈ R, orderOf x = 2 → InnerAt L x := by
  classical
  have hstd := h.isStandard' hterm hZ hR3
  have hN := h.lNormal
  obtain ⟨K₀, hK₀⟩ := delta_nonempty hZD h.hyp.simple h.hyp.nonabelian hstd
  obtain ⟨K₁, R₁, hK₁, hR₁, hR₁T⟩ := exists_delta_sylow_le_T h.pair hN hstd hK₀
  by_cases hall : ∀ x ∈ R₁, orderOf x = 2 → InnerAt L x
  · exact ⟨K₁, R₁, hK₁, hR₁, hR₁T, hall⟩
  · push Not at hall
    obtain ⟨r, hrR, hr2, hrout⟩ := hall
    obtain ⟨J, hJ, x, hxJ, hx2, hxin⟩ :=
      h.exists_inner_in_delta hterm hZ hR3 hO hK₁ hR₁ hR₁T hrR hr2 hrout
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hXp : IsPGroup 2 (zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx2]; norm_num)
    obtain ⟨k, R₂, hk, hK₂, hR₂, hR₂T, hxR₂⟩ := exists_delta_sylow_le_T' (X := zpowers x)
      h.pair hN hstd hJ hXp (zpowers_le.2 hxJ)
    refine ⟨rightConjugate J k, R₂, hK₂, hR₂, hR₂T, fun ρ hρ hρ2 => ?_⟩
    by_contra hρout
    have hsub := h.R_le_of_outer hterm hZ hR3 hO hK₂ hR₂ hR₂T hρ hρ2 hρout
    have hx' : k⁻¹ * x * k ∈ R₂ := by
      refine hxR₂ ((mem_rightConjugate_iff _ k _).2 ?_)
      have : k * (k⁻¹ * x * k) * k⁻¹ = x := by group
      rw [this]
      exact mem_zpowers x
    have hxinv : InnerAt L (k⁻¹ * x * k) := by
      have hk' : k⁻¹ ∈ normalizer (L : Set G) := (normalizer (L : Set G)).inv_mem hk
      have := InnerAt.conj hk' hxin
      simpa using this
    rcases hsub _ hx' with h1 | h1
    · have hx1 : x = 1 := by
        calc x = k * (k⁻¹ * x * k) * k⁻¹ := by group
          _ = 1 := by rw [h1]; group
      rw [hx1, orderOf_one] at hx2
      omega
    · rw [h1] at hxinv
      exact hρout hxinv

end PartA

end CFSG.GH74.AS16.E2
