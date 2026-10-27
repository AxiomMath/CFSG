module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85eCfg

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85

open Subgroup
open scoped commutatorElement

section Transport

variable {A B : Type} [Group A] [Group B] (φ : A →* B) {P : Subgroup A}

private theorem cfgMap_central_map {x : A} (hc : ∀ y ∈ P, x * y = y * x) :
    ∀ y ∈ P.map φ, φ x * y = y * φ x := by
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, hc y hy]

private theorem cfgMap_central_of_map (hinj : ∀ x ∈ P, ∀ y ∈ P, φ x = φ y → x = y) {x : A}
    (hx : x ∈ P) (hc : ∀ y ∈ P.map φ, φ x * y = y * φ x) : ∀ y ∈ P, x * y = y * x := by
  intro y hy
  refine hinj _ (P.mul_mem hx hy) _ (P.mul_mem hy hx) ?_
  rw [map_mul, map_mul]
  exact hc (φ y) (mem_map_of_mem φ hy)

private theorem cfgMap_card_map (hinj : ∀ x ∈ P, ∀ y ∈ P, φ x = φ y → x = y) :
    Nat.card ↥(P.map φ) = Nat.card ↥P := by
  refine (Nat.card_eq_of_bijective (φ.subgroupMap P) ⟨?_, φ.subgroupMap_surjective P⟩).symm
  intro x y hxy
  exact Subtype.ext (hinj x x.2 y y.2 (congrArg Subtype.val hxy))

private theorem cfgMap_card_center (hinj : ∀ x ∈ P, ∀ y ∈ P, φ x = φ y → x = y) :
    Nat.card ↥(center ↥(P.map φ)) = Nat.card ↥(center ↥P) := by
  let e : ↥P ≃* ↥(P.map φ) := MulEquiv.ofBijective (φ.subgroupMap P)
    ⟨fun x y hxy => Subtype.ext (hinj x x.2 y y.2 (congrArg Subtype.val hxy)),
      φ.subgroupMap_surjective P⟩
  exact (Nat.card_congr (centerCongr e).toEquiv).symm

private theorem cfgMap_orderOf (hinj : ∀ x ∈ P, ∀ y ∈ P, φ x = φ y → x = y) {x : A} (hx : x ∈ P) :
    orderOf (φ x) = orderOf x := by
  have h := orderOf_injective (φ.comp P.subtype)
    (fun a b hab => Subtype.ext (hinj a a.2 b b.2 hab)) ⟨x, hx⟩
  simpa using h

end Transport

theorem U34Cfg.map_injective {A B : Type} [Group A] [Group B] [Finite A] (f : A →* B)
    (hf : Function.Injective f) {P : Subgroup A} {w : A} (h : U34Cfg P w) :
    U34Cfg (P.map f) (f w) := by
  have hinj : ∀ x ∈ P, ∀ y ∈ P, f x = f y → x = y := fun x _ y _ hxy => hf hxy
  refine
    { two := h.two.map f
      five := ?_
      norm := ?_
      cen := ?_
      comm_ge := ?_
      order := ?_
      big := ?_
      center_or := ?_ }
  · obtain ⟨a, ha⟩ := h.five
    exact ⟨a, by rw [← map_pow, ha, map_one]⟩
  · rw [mem_normalizer_iff]
    intro b
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨w * x * w⁻¹, (mem_normalizer_iff.mp h.norm x).mp hx, by simp⟩
    · intro hb
      obtain ⟨y, hy, hyb⟩ := hb
      refine ⟨w⁻¹ * y * w, (mem_normalizer_iff''.mp h.norm y).mp hy, ?_⟩
      rw [map_mul, map_mul, map_inv, hyb]
      group
  · rintro _ ⟨x, hx, rfl⟩ hc
    have hcx := cfgMap_central_of_map f hinj hx (fun y hy => hc y hy)
    rw [← map_inv, ← map_mul, ← map_mul, h.cen x hx hcx]
  · have h1 : ⁅P.map f, zpowers (f w)⁆ = (⁅P, zpowers w⁆).map f := by
      rw [map_commutator, MonoidHom.map_zpowers]
    rw [h1, card_map_of_injective hf]
    exact h.comm_ge
  · rintro _ ⟨x, hx, rfl⟩
    rw [orderOf_injective f hf, card_map_of_injective hf]
    exact h.order x hx
  · rw [card_map_of_injective hf]
    exact h.big
  · rw [cfgMap_card_map f hinj, cfgMap_card_center f hinj]
    rcases h.center_or with h1 | ⟨h1, h2, h3⟩
    · exact Or.inl h1
    · refine Or.inr ⟨h1, h2, ?_⟩
      rintro _ ⟨x, hx, rfl⟩ hc
      rw [← map_mul, h3 x hx (cfgMap_central_of_map f hinj hx (fun y hy => hc y hy)), map_one]

theorem U34Cfg.of_lift {A B : Type} [Group A] [Group B] [Finite A] (φ : A →* B) {P : Subgroup A}
    {w : A} (hinj : ∀ x ∈ P, ∀ y ∈ P, φ x = φ y → x = y)
    {kb : B} (h : U34Cfg (P.map φ) kb) (hw : zpowers (φ w) = zpowers kb)
    (hwn : w ∈ normalizer (P : Set A)) (hw5 : ∃ a : ℕ, w ^ (5 ^ a) = 1) (hP2 : IsPGroup 2 ↥P) :
    U34Cfg P w := by
  refine
    { two := hP2
      five := hw5
      norm := hwn
      cen := ?_
      comm_ge := ?_
      order := ?_
      big := ?_
      center_or := ?_ }
  · intro x hx hcx
    have h1 : kb * φ x * kb⁻¹ = φ x :=
      h.cen (φ x) (mem_map_of_mem φ hx) (cfgMap_central_map φ hcx)
    have h2 : Commute kb (φ x) := by
      have : kb * φ x = φ x * kb := by
        calc kb * φ x = kb * φ x * kb⁻¹ * kb := by group
          _ = φ x * kb := by rw [h1]
      exact this
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hw ▸ mem_zpowers (φ w) : φ w ∈ zpowers kb)
    have h3 : Commute (φ w) (φ x) := hn ▸ h2.zpow_left n
    have hxP : w * x * w⁻¹ ∈ P := (mem_normalizer_iff.mp hwn x).mp hx
    refine hinj _ hxP _ hx ?_
    rw [map_mul, map_mul, map_inv, h3.eq, mul_assoc, mul_inv_cancel, mul_one]
  · have h1 : (⁅P, zpowers w⁆).map φ = ⁅P.map φ, zpowers kb⁆ := by
      rw [map_commutator, MonoidHom.map_zpowers, hw]
    have h2 := h.comm_ge
    rw [← h1] at h2
    exact h2.trans (Nat.card_le_card_of_surjective _ (φ.subgroupMap_surjective _))
  · intro x hx
    have h1 := h.order (φ x) (mem_map_of_mem φ hx)
    rwa [cfgMap_orderOf φ hinj hx, cfgMap_card_map φ hinj] at h1
  · have h1 := h.big
    rwa [cfgMap_card_map φ hinj] at h1
  · rw [← cfgMap_card_map φ hinj, ← cfgMap_card_center φ hinj]
    rcases h.center_or with h1 | ⟨h1, h2, h3⟩
    · exact Or.inl h1
    · refine Or.inr ⟨h1, h2, ?_⟩
      intro x hx hcx
      have h4 : φ x * φ x = 1 :=
        h3 (φ x) (mem_map_of_mem φ hx) (cfgMap_central_map φ hcx)
      refine hinj _ (P.mul_mem hx hx) _ P.one_mem ?_
      rw [map_mul, map_one, h4]

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85
