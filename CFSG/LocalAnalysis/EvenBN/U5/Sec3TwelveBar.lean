module

public import CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.LocalAnalysis.EvenBN.U5.Sec312

open Subgroup CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient

variable {G : Type*} [Group G] {A : Subgroup G}

theorem mem_bar_iff_exists {X : Subgroup G} {y : Bar A} :
    y ∈ bar A X ↔ ∃ z : normalizer (A : Set G), (z : G) ∈ X ∧ proj A z = y := by
  simp only [bar, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem bar_sup {X Y : Subgroup G} (hX : X ≤ normalizer (A : Set G))
    (hY : Y ≤ normalizer (A : Set G)) : bar A (X ⊔ Y) = bar A X ⊔ bar A Y := by
  unfold bar
  rw [Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

theorem bar_inf {X Y : Subgroup G} (hAX : A ≤ X) (hAY : A ≤ Y) :
    bar A (X ⊓ Y) = bar A X ⊓ bar A Y := by
  ext y
  obtain ⟨x, rfl⟩ := proj_surjective y
  rw [Subgroup.mem_inf, mem_bar_iff (le_inf hAX hAY), mem_bar_iff hAX, mem_bar_iff hAY,
    Subgroup.mem_inf]

theorem eq_of_bar_eq {X Y : Subgroup G} (hAX : A ≤ X) (hAY : A ≤ Y)
    (hXN : X ≤ normalizer (A : Set G)) (hYN : Y ≤ normalizer (A : Set G))
    (h : bar A X = bar A Y) : X = Y := by
  rw [← lift_bar hAX hXN, ← lift_bar hAY hYN, h]

theorem bar_self : bar A A = ⊥ := by
  ext y
  obtain ⟨x, rfl⟩ := proj_surjective y
  rw [mem_bar_iff le_rfl, Subgroup.mem_bot, proj_eq_one_iff]

theorem bar_map_conj {t : G} (ht : t ∈ normalizer (A : Set G)) (X : Subgroup G) :
    bar A (X.map (MulAut.conj t).toMonoidHom) =
      (bar A X).map (MulAut.conj (proj A ⟨t, ht⟩)).toMonoidHom := by
  ext y
  rw [mem_bar_iff_exists, Subgroup.mem_map]
  constructor
  · rintro ⟨z, ⟨x, hx, hxz⟩, rfl⟩
    have hxN : x ∈ normalizer (A : Set G) := by
      have : x = t⁻¹ * z * t := by
        rw [← hxz]
        change x = t⁻¹ * (t * x * t⁻¹) * t
        group
      rw [this]
      exact mul_mem (mul_mem (inv_mem ht) z.2) ht
    refine ⟨proj A ⟨x, hxN⟩, mem_bar_iff_exists.2 ⟨⟨x, hxN⟩, hx, rfl⟩, ?_⟩
    change proj A ⟨t, ht⟩ * proj A ⟨x, hxN⟩ * (proj A ⟨t, ht⟩)⁻¹ = proj A z
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change t * x * t⁻¹ = z
    exact hxz
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨z₀, hz₀, rfl⟩ := mem_bar_iff_exists.1 hw
    refine ⟨⟨t * z₀ * t⁻¹, mul_mem (mul_mem ht z₀.2) (inv_mem ht)⟩, ⟨z₀, hz₀, rfl⟩, ?_⟩
    change proj A _ = proj A ⟨t, ht⟩ * proj A z₀ * (proj A ⟨t, ht⟩)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl

theorem proj_injOn {X : Subgroup G} (hXA : X ⊓ A = ⊥) {x y : normalizer (A : Set G)}
    (hx : (x : G) ∈ X) (hy : (y : G) ∈ X) (h : proj A x = proj A y) : x = y := by
  have h1 := proj_eq_proj_iff.1 h
  have h2' : (x : G)⁻¹ * y ∈ X := mul_mem (inv_mem hx) hy
  have h2 : (x : G)⁻¹ * y ∈ X ⊓ A := Subgroup.mem_inf.2 ⟨h2', h1⟩
  rw [hXA, Subgroup.mem_bot] at h2
  exact Subtype.ext (inv_mul_eq_one.1 h2)

@[expose] noncomputable def barHom {X : Subgroup G} (hX : X ≤ normalizer (A : Set G)) : X →* Bar A :=
  (proj A).comp (Subgroup.inclusion hX)

theorem barHom_injective {X : Subgroup G} (hX : X ≤ normalizer (A : Set G)) (hXA : X ⊓ A = ⊥) :
    Function.Injective (barHom hX) := by
  intro a b hab
  have := proj_injOn hXA (x := ⟨a, hX a.2⟩) (y := ⟨b, hX b.2⟩) a.2 b.2 hab
  have h' : (a : G) = b := congrArg (fun z : normalizer (A : Set G) => (z : G)) this
  exact Subtype.ext h'

theorem barHom_range {X : Subgroup G} (hX : X ≤ normalizer (A : Set G)) :
    (barHom hX).range = bar A X := by
  ext y
  rw [MonoidHom.mem_range, mem_bar_iff_exists]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, hX x.2⟩, x.2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩

@[expose] noncomputable def barEquiv {X : Subgroup G} (hX : X ≤ normalizer (A : Set G)) (hXA : X ⊓ A = ⊥) :
    X ≃* bar A X :=
  (MonoidHom.ofInjective (barHom_injective hX hXA)).trans
    (MulEquiv.subgroupCongr (barHom_range hX))

theorem card_bar_of_inf_eq_bot {X : Subgroup G} (hX : X ≤ normalizer (A : Set G))
    (hXA : X ⊓ A = ⊥) : Nat.card (bar A X) = Nat.card X :=
  (Nat.card_congr (barEquiv hX hXA).toEquiv).symm

theorem isSylowOf_bar [Finite G] {P X : Subgroup G}
    (hPX : CFSG.ABGLocalTools.IsSylowOf 2 P X) (hXN : X ≤ normalizer (A : Set G))
    (hXA : X ⊓ A = ⊥) : CFSG.ABGLocalTools.IsSylowOf 2 (bar A P) (bar A X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPN : P ≤ normalizer (A : Set G) := hPX.le.trans hXN
  have hPA : P ⊓ A = ⊥ := eq_bot_iff.2 fun x hx => by
    rw [← hXA]
    exact ⟨hPX.le hx.1, hx.2⟩
  refine CFSG.ABGLocalTools.isSylowOf_of_card (bar_mono hPX.le) ?_
  rw [card_bar_of_inf_eq_bot hPN hPA, card_bar_of_inf_eq_bot hXN hXA]
  exact hPX.card_eq

theorem mem_normalizer_lift [Finite G] {Y : Subgroup (Bar A)} {g : G}
    (hg : g ∈ normalizer (A : Set G))
    (h : proj A ⟨g, hg⟩ ∈ normalizer (Y : Set (Bar A))) :
    g ∈ normalizer ((lift Y : Subgroup G) : Set G) := by
  refine mem_normalizer_fintype fun x hx => ?_
  obtain ⟨hxN, hxY⟩ := mem_lift_iff.1 hx
  refine mem_lift_iff.2 ⟨mul_mem (mul_mem hg hxN) (inv_mem hg), ?_⟩
  have e : proj A ⟨g * x * g⁻¹, mul_mem (mul_mem hg hxN) (inv_mem hg)⟩ =
      proj A ⟨g, hg⟩ * proj A ⟨x, hxN⟩ * (proj A ⟨g, hg⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e]
  exact (mem_normalizer_iff.1 h _).1 hxY

theorem bar_inf_of_inf_eq_bot {M H₁ H₂ : Subgroup G} (hM : M ≤ normalizer (A : Set G))
    (hMA : M ⊓ A = ⊥) (h₁ : H₁ ≤ M) (h₂ : H₂ ≤ M) :
    bar A H₁ ⊓ bar A H₂ = bar A (H₁ ⊓ H₂) := by
  refine le_antisymm (fun y hy => ?_) (le_inf (bar_mono inf_le_left) (bar_mono inf_le_right))
  obtain ⟨z₁, hz₁, rfl⟩ := mem_bar_iff_exists.1 hy.1
  obtain ⟨z₂, hz₂, hz⟩ := mem_bar_iff_exists.1 hy.2
  have := proj_injOn hMA (x := z₂) (y := z₁) (h₂ hz₂) (h₁ hz₁) hz
  subst this
  exact mem_bar_iff_exists.2 ⟨z₂, Subgroup.mem_inf.2 ⟨hz₁, hz₂⟩, rfl⟩

end CFSG.LocalAnalysis.EvenBN.U5.Sec312
