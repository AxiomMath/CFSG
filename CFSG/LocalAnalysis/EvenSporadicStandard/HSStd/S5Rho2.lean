module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Cent
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup

theorem mem_of_central_involution {G : Type} [Group G] [Finite G] {C S : Subgroup G} {t : G}
    (hSC : S ≤ C) (hS2 : IsPGroup 2 S) (hSidx : ¬ 2 ∣ S.relIndex C) (htC : t ∈ C)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (hcen : ∀ c ∈ C, c * t = t * c) : t ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : IsPGroup 2 (S.subgroupOf C) := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSC).symm
  let P : Sylow 2 C := hS'.toSylow hSidx
  have hord : orderOf t = 2 := orderOf_eq_prime (by rwa [pow_two]) ht1
  let N : Subgroup C := (zpowers t).subgroupOf C
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (mem_subgroupOf.1 hn)
    have hc : (g : G) * (n : G) = n * g := by
      rw [← hk]
      exact ((Commute.zpow_right (show Commute (g : G) t from hcen g g.2) k)).eq
    rw [mem_subgroupOf]
    show (g : G) * n * (g : G)⁻¹ ∈ zpowers t
    rw [hc, mul_inv_cancel_right]
    exact mem_subgroupOf.1 hn
  have hN2 : IsPGroup 2 N := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [pow_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (zpowers_le.2 htC)).toEquiv,
      Nat.card_zpowers, hord]
  have := hN2.le_sylow_of_normal P
  have h1 : (⟨t, htC⟩ : C) ∈ P := this (mem_subgroupOf.2 (mem_zpowers t))
  exact mem_subgroupOf.1 ((hS'.mem_toSylow hSidx).1 h1)


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}
  {W X : Type} [Group W] [Group X] [Finite W] (D : AutModelData L W X)

omit [Finite G] in
theorem sq_mem_of_mem_sup (hL : t ∈ centralizer (L : Set G)) (ht2 : t * t = 1)
    {x : G} (hx : x ∈ L ⊔ zpowers t) : ∃ l ∈ L, x * x = l := by
  have hcomm : ∀ β ∈ L, Commute β t := fun β hβ => mem_centralizer_iff.1 hL β hβ
  obtain ⟨β, hβ, j, rfl⟩ := (mem_sup_zpowers_iff hcomm).1 hx
  refine ⟨β * β, L.mul_mem hβ hβ, ?_⟩
  rcases zpow_eq_one_or_self ht2 j with h | h
  · rw [h]
    simp
  · rw [h]
    calc β * t * (β * t) = β * (t * β) * t := by group
      _ = β * (β * t) * t := by rw [(hcomm β hβ).eq.symm]
      _ = β * β * (t * t) := by group
      _ = β * β := by rw [ht2, mul_one]

omit [Finite G] in
theorem exists_outer (hidx : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 2) :
    ∃ y ∈ centralizer ({t} : Set G), y ∉ L ⊔ zpowers t := by
  by_contra h
  push Not at h
  have h1 : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 1 :=
    Subgroup.relIndex_eq_one.2 fun x hx => h x hx
  omega

omit [Finite G] in
theorem rhoC_surjective (hL : t ∈ centralizer (L : Set G))
    (hC : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hker : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hidx : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 2)
    (hW : Nat.card W = 2 * Nat.card X) : Function.Surjective (D.rhoC hC) := by
  classical
  set C : Subgroup G := centralizer ({t} : Set G) with hCdef
  set N' : Subgroup G := L ⊔ zpowers t with hN'def
  have hLC : L ≤ C := le_centralizer_of_mem_centralizer hL
  set ρ : C →* W := D.rhoC hC with hρdef
  have hρmem : ∀ x : C, ρ x ∈ D.ι.range ↔ (x : G) ∈ N' := rhoC_mem_range_iff D hC hL hker
  have hρL : ∀ l : L, ρ ⟨l, hLC l.2⟩ = D.ι (D.θ l) := rhoC_of_mem D hC hL
  obtain ⟨y₀, hy₀C, hy₀N⟩ := exists_outer hidx
  have hmrange : Nat.card D.ι.range = Nat.card X :=
    (Nat.card_congr (MonoidHom.ofInjective D.ι_injective).toEquiv).symm
  have hH : D.ι.range ≤ ρ.range := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨l, rfl⟩ := D.θ.surjective y
    exact ⟨⟨l, hLC l.2⟩, hρL l⟩
  have hne : ρ.range ≠ D.ι.range := by
    intro h
    have : ρ ⟨y₀, hy₀C⟩ ∈ D.ι.range := h ▸ ⟨_, rfl⟩
    exact hy₀N ((hρmem ⟨y₀, hy₀C⟩).1 this)
  obtain ⟨a, ha⟩ := Subgroup.card_dvd_of_le hH
  obtain ⟨b, hb⟩ := Subgroup.card_subgroup_dvd_card ρ.range
  have hm : 0 < Nat.card D.ι.range := Nat.card_pos
  have hab : a * b = 2 := by
    have h1 : Nat.card D.ι.range * (a * b) = Nat.card D.ι.range * 2 := by
      calc Nat.card D.ι.range * (a * b) = Nat.card ρ.range * b := by rw [ha]; ring
        _ = Nat.card W := hb.symm
        _ = Nat.card D.ι.range * 2 := by rw [hW, hmrange, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hm h1
  have ha2 : a = 1 ∨ a = 2 := (Nat.dvd_prime Nat.prime_two).1 ⟨b, hab.symm⟩
  rcases ha2 with rfl | rfl
  · exfalso
    refine hne (Subgroup.eq_of_le_of_card_ge hH ?_).symm
    rw [ha]
    simp
  · have : ρ.range = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top]
      have hb1 : b = 1 := by omega
      rw [hb, hb1, mul_one]
    exact MonoidHom.range_eq_top.1 this

omit [Finite G] in
theorem sq_mem_of_outer (hL : t ∈ centralizer (L : Set G)) (ht2 : t * t = 1)
    (hC : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hidx : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 2)
    {x₀ : G} (hx₀C : x₀ ∈ centralizer ({t} : Set G)) (hx₀N : x₀ ∉ L ⊔ zpowers t)
    (hx₀sq : x₀ * x₀ = t) {x : G} (hx : x ∈ centralizer ({t} : Set G))
    (hxN : x ∉ L ⊔ zpowers t) : ∃ l ∈ L, x * x = l * t := by
  have hcomm : ∀ β ∈ L, Commute β t := fun β hβ => mem_centralizer_iff.1 hL β hβ
  have hH2 : ((L ⊔ zpowers t).subgroupOf (centralizer ({t} : Set G))).index = 2 := hidx
  have hmem : (⟨x₀, hx₀C⟩⁻¹ * ⟨x, hx⟩ : centralizer ({t} : Set G)) ∈
      (L ⊔ zpowers t).subgroupOf (centralizer ({t} : Set G)) := by
    rw [Subgroup.mul_mem_iff_of_index_two hH2]
    simp only [mem_subgroupOf, Subgroup.inv_mem_iff]
    exact iff_of_false hx₀N hxN
  have ha1 : x₀⁻¹ * x ∈ L ⊔ zpowers t := by simpa using mem_subgroupOf.1 hmem
  obtain ⟨β, hβ, j, hj⟩ := (mem_sup_zpowers_iff hcomm).1 ha1
  have hx0t : x₀ * t = t * x₀ := mem_centralizer_singleton_iff.1 hx₀C
  have hxeq : x = x₀ * (β * t ^ j) := by rw [← hj]; group
  have hβ' : x₀⁻¹ * β * x₀ ∈ L := by
    have hx₀n : x₀ ∈ normalizer (L : Set G) := hC hx₀C
    have := (mem_normalizer_iff.1 ((normalizer (L : Set G)).inv_mem hx₀n) β).1 hβ
    simpa using this
  refine ⟨(x₀⁻¹ * β * x₀) * β, L.mul_mem hβ' hβ, ?_⟩
  have hcβ' : t * (x₀⁻¹ * β * x₀ * β) = (x₀⁻¹ * β * x₀ * β) * t :=
    (hcomm _ (L.mul_mem hβ' hβ)).eq.symm
  have key : x * x = x₀ * β * x₀ * β := by
    rw [hxeq]
    rcases zpow_eq_one_or_self ht2 j with h | h
    · rw [h]; group
    · rw [h]
      calc x₀ * (β * t) * (x₀ * (β * t)) = x₀ * β * (t * x₀) * (β * t) := by group
        _ = x₀ * β * (x₀ * t) * (β * t) := by rw [← hx0t]
        _ = x₀ * β * x₀ * (t * β) * t := by group
        _ = x₀ * β * x₀ * (β * t) * t := by rw [← (hcomm β hβ).eq]
        _ = x₀ * β * x₀ * β * (t * t) := by group
        _ = x₀ * β * x₀ * β := by rw [ht2, mul_one]
  rw [key]
  calc x₀ * β * x₀ * β = (x₀ * x₀) * (x₀⁻¹ * β * x₀ * β) := by group
    _ = t * (x₀⁻¹ * β * x₀ * β) := by rw [hx₀sq]
    _ = (x₀⁻¹ * β * x₀ * β) * t := hcβ'

omit [Finite G] [Finite W] in
theorem mul_self_eq_one_of_lift (hL : t ∈ centralizer (L : Set G)) (ht2 : t * t = 1)
    (htL : t ∉ L) (hC : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hker : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hidx : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 2)
    {v : G} (hvC : v ∈ centralizer ({t} : Set G)) (hvN : v ∉ L ⊔ zpowers t) (hv2 : v * v = 1)
    {x : G} (hx : x ∈ centralizer ({t} : Set G))
    (hρ : D.rhoC hC ⟨x, hx⟩ * D.rhoC hC ⟨x, hx⟩ = 1) : x * x = 1 := by
  have hzp : ∀ a : G, a ∈ zpowers t → a = 1 ∨ a = t := by
    intro a ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 ha
    exact zpow_eq_one_or_self ht2 j
  have h1 : D.rhoC hC (⟨x, hx⟩ * ⟨x, hx⟩) = 1 := by rw [map_mul]; exact hρ
  have h2 : x * x ∈ zpowers t := (rhoC_eq_one_iff D hC hker _).1 h1
  rcases hzp _ h2 with h | h
  · exact h
  · exfalso
    have hxN : x ∉ L ⊔ zpowers t := by
      intro hxs
      obtain ⟨l, hl, hl'⟩ := sq_mem_of_mem_sup hL ht2 hxs
      exact htL (h ▸ hl' ▸ hl)
    obtain ⟨l, hl, hl'⟩ := sq_mem_of_outer hL ht2 hC hidx hx hxN h hvC hvN
    apply htL
    have : t = l⁻¹ := by
      calc t = l⁻¹ * (l * t) := by group
        _ = l⁻¹ := by rw [← hl', hv2, mul_one]
    rw [this]
    exact L.inv_mem hl

theorem sylow_range_rhoC (hL : t ∈ centralizer (L : Set G)) (ht2 : t * t = 1) (htL : t ∉ L)
    (hC : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hker : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hidx : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 2)
    (hW : Nat.card W = 2 * Nat.card X) (S : Subgroup G)
    (hSC : S ≤ centralizer ({t} : Set G)) (hS2 : IsPGroup 2 S)
    (hSidx : ¬ 2 ∣ S.relIndex (centralizer ({t} : Set G))) :
    t ∈ S ∧ IsPGroup 2 ((D.rhoC hC).comp (Subgroup.inclusion hSC)).range ∧
      ¬ 2 ∣ ((D.rhoC hC).comp (Subgroup.inclusion hSC)).range.index := by
  classical
  set C : Subgroup G := centralizer ({t} : Set G) with hCdef
  have htC : t ∈ C := mem_centralizer_singleton_iff.2 rfl
  have ht1 : t ≠ 1 := fun h => htL (h ▸ L.one_mem)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf t = 2 := orderOf_eq_prime (by rwa [pow_two]) ht1
  have hzt : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, hord]
  set ρ : C →* W := D.rhoC hC with hρdef
  have hρker : ∀ x : C, ρ x = 1 ↔ (x : G) ∈ zpowers t := rhoC_eq_one_iff D hC hker
  have hsurj : Function.Surjective ρ := rhoC_surjective D hL hC hker hidx hW
  have htS : t ∈ S := mem_of_central_involution hSC hS2 hSidx htC ht2 ht1 fun c hc =>
    mem_centralizer_singleton_iff.1 hc
  set σ : S →* W := ρ.comp (Subgroup.inclusion hSC) with hσdef
  have hσker : ∀ x : S, σ x = 1 ↔ (x : G) ∈ zpowers t := fun x => hρker ⟨x, hSC x.2⟩
  have hker_eq : σ.ker = (zpowers t).subgroupOf S := by
    ext x
    rw [MonoidHom.mem_ker, hσker, mem_subgroupOf]
  have hzS' : zpowers t ≤ S := zpowers_le.2 htS
  have hker_card : Nat.card σ.ker = 2 := by
    rw [hker_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzS').toEquiv, hzt]
  refine ⟨htS, hS2.of_surjective σ.rangeRestrict σ.rangeRestrict_surjective, ?_⟩
  have hCS : Nat.card C = Nat.card S * S.relIndex C := by
    have h := Subgroup.card_mul_index (S.subgroupOf C)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv] at h
    exact h.symm
  have hCW : Nat.card C = 2 * Nat.card W := by
    have h := Subgroup.card_ker_mul_card_of_surjective hsurj
    have hkρ : Nat.card ρ.ker = 2 := by
      have : ρ.ker = (zpowers t).subgroupOf C := by
        ext x
        rw [MonoidHom.mem_ker, hρker, mem_subgroupOf]
      rw [this, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (zpowers_le.2 htC)).toEquiv, hzt]
    rw [hkρ] at h
    exact h.symm
  have hSS : Nat.card S = 2 * Nat.card σ.range := by
    have h := Subgroup.card_ker_mul_card_range σ
    rw [hker_card] at h
    exact h.symm
  have hWS := Subgroup.card_mul_index σ.range
  have hpos : 0 < Nat.card σ.range := Nat.card_pos
  have hidx' : σ.range.index = S.relIndex C := by
    have h1 : Nat.card σ.range * σ.range.index = Nat.card σ.range * S.relIndex C := by
      calc Nat.card σ.range * σ.range.index = Nat.card W := hWS
        _ = Nat.card σ.range * S.relIndex C := by
          have h2 : 2 * Nat.card W = 2 * (Nat.card σ.range * S.relIndex C) := by
            rw [← hCW, hCS, hSS]
            ring
          exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h2
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  rw [hidx']
  exact hSidx

omit [Finite G] [Finite W] in
theorem mem_range_inf_iff (hL : t ∈ centralizer (L : Set G))
    (hC : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hker : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (S : Subgroup G) (hSC : S ≤ centralizer ({t} : Set G)) (htS : t ∈ S) (y : W) :
    y ∈ ((D.rhoC hC).comp (Subgroup.inclusion hSC)).range ⊓ D.ι.range ↔
      ∃ l : L, (l : G) ∈ S ∧ y = D.ι.comp D.θ.toMonoidHom l := by
  have hLC : L ≤ centralizer ({t} : Set G) := le_centralizer_of_mem_centralizer hL
  have hρker : ∀ x : centralizer ({t} : Set G), D.rhoC hC x = 1 ↔ (x : G) ∈ zpowers t :=
    rhoC_eq_one_iff D hC hker
  have hρL : ∀ l : L, D.rhoC hC ⟨l, hLC l.2⟩ = D.ι (D.θ l) := rhoC_of_mem D hC hL
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨y', hy'⟩⟩
    obtain ⟨l₀, rfl⟩ := D.θ.surjective y'
    have hρs : D.rhoC hC ⟨s, hSC s.2⟩ = y := hs
    have h1 : D.rhoC hC ((⟨l₀, hLC l₀.2⟩ : centralizer ({t} : Set G))⁻¹ * ⟨s, hSC s.2⟩) = 1 := by
      rw [map_mul, map_inv, hρL l₀, hρs, ← hy', inv_mul_cancel]
    have h2 : (l₀ : G)⁻¹ * s ∈ zpowers t := (hρker _).1 h1
    have hl₀S : (l₀ : G) ∈ S := by
      obtain ⟨j, hj⟩ := mem_zpowers_iff.1 h2
      have : (l₀ : G) = s * t ^ (-j) := by
        rw [zpow_neg, hj]
        group
      rw [this]
      exact S.mul_mem s.2 (zpow_mem htS _)
    exact ⟨l₀, hl₀S, hy'.symm⟩
  · rintro ⟨l, hlS, rfl⟩
    exact ⟨⟨⟨l, hlS⟩, hρL l⟩, ⟨D.θ l, rfl⟩⟩

omit [Finite G] [Finite W] in
theorem centralizer_range_rhoS (hL : t ∈ centralizer (L : Set G))
    (hC : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hker : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (S : Subgroup G) (hSC : S ≤ centralizer ({t} : Set G)) (htS : t ∈ S) (z : G) (hzL : z ∈ L)
    (hzc : centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓ L = zpowers z) :
    centralizer ((((D.rhoC hC).comp (Subgroup.inclusion hSC)).range ⊓ D.ι.range : Subgroup W) :
        Set W) ⊓ D.ι.range = zpowers (D.ι (D.θ ⟨z, hzL⟩)) := by
  have hSwR := mem_range_inf_iff D hL hC hker S hSC htS
  have hΦinj : Function.Injective (D.ι.comp D.θ.toMonoidHom) := D.ι_injective.comp D.θ.injective
  have hzk : ∀ k : ℤ, (D.ι (D.θ ⟨z, hzL⟩)) ^ k =
      D.ι.comp D.θ.toMonoidHom ((⟨z, hzL⟩ : L) ^ k) := fun k => by
    rw [map_zpow]
    rfl
  ext w
  constructor
  · rintro ⟨hwc, ⟨y, rfl⟩⟩
    obtain ⟨l₀, rfl⟩ := D.θ.surjective y
    have hl₀ : (l₀ : G) ∈ centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓ L := by
      refine ⟨mem_centralizer_iff.2 fun g hg => ?_, l₀.2⟩
      have hgL : g ∈ L := hg.2
      have hgS : g ∈ S := hg.1
      have h3 := mem_centralizer_iff.1 hwc (D.ι.comp D.θ.toMonoidHom ⟨g, hgL⟩)
        ((hSwR _).2 ⟨⟨g, hgL⟩, hgS, rfl⟩)
      have h' : (D.ι.comp D.θ.toMonoidHom) (⟨g, hgL⟩ * l₀) =
          (D.ι.comp D.θ.toMonoidHom) (l₀ * ⟨g, hgL⟩) := by
        rw [map_mul, map_mul]
        exact h3
      exact congrArg Subtype.val (hΦinj h')
    rw [hzc] at hl₀
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hl₀
    refine ⟨k, ?_⟩
    have h4 : (⟨z, hzL⟩ : L) ^ k = l₀ := Subtype.ext (by simpa using hk)
    show (D.ι (D.θ ⟨z, hzL⟩)) ^ k = D.ι (D.θ l₀)
    rw [hzk, h4]
    rfl
  · intro hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
    refine ⟨mem_centralizer_iff.2 fun h hh => ?_, ?_⟩
    · obtain ⟨l, hlS, rfl⟩ := (hSwR h).1 hh
      have hz' : (z : G) ∈ centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓ L := by
        rw [hzc]
        exact mem_zpowers z
      have hc : (l : G) * z = z * l := mem_centralizer_iff.1 hz'.1 l ⟨hlS, l.2⟩
      have hcL : l * (⟨z, hzL⟩ : L) = ⟨z, hzL⟩ * l := Subtype.ext hc
      rw [hzk, ← map_mul, ← map_mul, (Commute.zpow_right hcL k).eq]
    · exact ⟨D.θ ((⟨z, hzL⟩ : L) ^ k), by rw [hzk]; rfl⟩

omit [Finite G] [Finite W] in
theorem comm_mem_of_mem_centralizer (hL : t ∈ centralizer (L : Set G))
    (hC : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hidx : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 2)
    {x y : G} (hx : x ∈ centralizer ({t} : Set G)) (hy : y ∈ centralizer ({t} : Set G)) :
    x * y * x⁻¹ * y⁻¹ ∈ L := by
  classical
  have hcomm : ∀ β ∈ L, Commute β t := fun β hβ => mem_centralizer_iff.1 hL β hβ
  have hnorm : ∀ g ∈ centralizer ({t} : Set G), ∀ l ∈ L, g * l * g⁻¹ ∈ L := fun g hg l hl =>
    (mem_normalizer_iff.1 (hC hg) l).1 hl
  have key : ∀ {a b : G}, a ∈ L ⊔ zpowers t → b ∈ centralizer ({t} : Set G) →
      a * b * a⁻¹ * b⁻¹ ∈ L := by
    intro a b ha hb
    obtain ⟨l, hl, j, rfl⟩ := (mem_sup_zpowers_iff hcomm).1 ha
    have htj : t ^ j * b = b * t ^ j := by
      have : Commute t b := (mem_centralizer_singleton_iff.1 hb).symm
      exact (this.zpow_left j).eq
    have hc : l * t ^ j * b * (l * t ^ j)⁻¹ * b⁻¹ = l * (b * l⁻¹ * b⁻¹) := by
      calc l * t ^ j * b * (l * t ^ j)⁻¹ * b⁻¹ = l * (t ^ j * b) * (t ^ j)⁻¹ * l⁻¹ * b⁻¹ := by
            group
        _ = l * (b * t ^ j) * (t ^ j)⁻¹ * l⁻¹ * b⁻¹ := by rw [htj]
        _ = l * (b * l⁻¹ * b⁻¹) := by group
    rw [hc]
    exact L.mul_mem hl (hnorm b hb l⁻¹ (L.inv_mem hl))
  by_cases hxN : x ∈ L ⊔ zpowers t
  · exact key hxN hy
  · by_cases hyN : y ∈ L ⊔ zpowers t
    · have h1 := key hyN hx
      have : x * y * x⁻¹ * y⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ := by group
      rw [this]
      exact L.inv_mem h1
    ·
      have hH2 : ((L ⊔ zpowers t).subgroupOf (centralizer ({t} : Set G))).index = 2 := hidx
      have hmem : (⟨x, hx⟩⁻¹ * ⟨y, hy⟩ : centralizer ({t} : Set G)) ∈
          (L ⊔ zpowers t).subgroupOf (centralizer ({t} : Set G)) := by
        rw [Subgroup.mul_mem_iff_of_index_two hH2]
        simp only [mem_subgroupOf, Subgroup.inv_mem_iff]
        exact iff_of_false hxN hyN
      have ha : x⁻¹ * y ∈ L ⊔ zpowers t := by simpa using mem_subgroupOf.1 hmem
      have h1 := hnorm x hx _ (L.inv_mem (key ha hx))
      have hc : x * y * x⁻¹ * y⁻¹ =
          x * ((x⁻¹ * y) * x * (x⁻¹ * y)⁻¹ * x⁻¹)⁻¹ * x⁻¹ := by group
      rw [hc]
      exact h1

end CFSG.EvenSporadicStandard.HSStd
