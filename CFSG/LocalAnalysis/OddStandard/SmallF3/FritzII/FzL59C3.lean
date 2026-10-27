module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59C2

import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup

variable {G : Type} [Group G]

structure fzl59c_Gen (Z : Subgroup G) (s t g : G) : Prop where
  sq_mem : g ^ 2 ∈ Z
  conj_Z : ∀ z ∈ Z, g * z * g⁻¹ ∈ Z
  conj_s : ∃ w ∈ Z, g * s * g⁻¹ = s * w
  conj_t : ∃ β ∈ Z ⊔ zpowers s, g * t * g⁻¹ = t * β

def fzl59c_trSub (T B : Subgroup G) (t : G) : Subgroup G where
  carrier := {β | β ∈ B ∧ ∃ y ∈ T, (∀ x ∈ B, y * x * y⁻¹ = x) ∧ y * t * y⁻¹ = t * β}
  one_mem' := ⟨B.one_mem, 1, T.one_mem, fun x _ => by simp, by simp⟩
  mul_mem' := by
    rintro β β' ⟨hβ, y, hy, hyB, hyt⟩ ⟨hβ', y', hy', hy'B, hy't⟩
    refine ⟨B.mul_mem hβ hβ', y * y', T.mul_mem hy hy', fun x hx => ?_, ?_⟩
    · calc y * y' * x * (y * y')⁻¹ = y * (y' * x * y'⁻¹) * y⁻¹ := by group
        _ = x := by rw [hy'B x hx, hyB x hx]
    · calc y * y' * t * (y * y')⁻¹ = y * (y' * t * y'⁻¹) * y⁻¹ := by group
        _ = y * (t * β') * y⁻¹ := by rw [hy't]
        _ = (y * t * y⁻¹) * (y * β' * y⁻¹) := by group
        _ = (t * β) * β' := by rw [hyt, hyB β' hβ']
        _ = t * (β * β') := by group
  inv_mem' := by
    rintro β ⟨hβ, y, hy, hyB, hyt⟩
    refine ⟨B.inv_mem hβ, y⁻¹, T.inv_mem hy, fun x hx => ?_, ?_⟩
    · calc y⁻¹ * x * y⁻¹⁻¹ = y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ := by rw [hyB x hx]
        _ = x := by group
    · have h1 : y⁻¹ * β * y⁻¹⁻¹ = β := by
        calc y⁻¹ * β * y⁻¹⁻¹ = y⁻¹ * (y * β * y⁻¹) * y⁻¹⁻¹ := by rw [hyB β hβ]
          _ = β := by group
      have ht : t = (y⁻¹ * t * y⁻¹⁻¹) * β := by
        calc t = y⁻¹ * (y * t * y⁻¹) * y⁻¹⁻¹ := by group
          _ = y⁻¹ * (t * β) * y⁻¹⁻¹ := by rw [hyt]
          _ = (y⁻¹ * t * y⁻¹⁻¹) * (y⁻¹ * β * y⁻¹⁻¹) := by group
          _ = (y⁻¹ * t * y⁻¹⁻¹) * β := by rw [h1]
      calc y⁻¹ * t * y⁻¹⁻¹ = ((y⁻¹ * t * y⁻¹⁻¹) * β) * β⁻¹ := by group
        _ = t * β⁻¹ := by rw [← ht]

theorem fzl59c_mem_trSub {T B : Subgroup G} {t β : G} :
    β ∈ fzl59c_trSub T B t ↔
      β ∈ B ∧ ∃ y ∈ T, (∀ x ∈ B, y * x * y⁻¹ = x) ∧ y * t * y⁻¹ = t * β :=
  Iff.rfl

section Chain

variable {Z : Subgroup G} {s t : G} (hA : fzl59c_Abs Z s t)
include hA

theorem fzl59c_gen_normalizer {g : G} (hg : fzl59c_Gen Z s t g) : g ∈ normalizer Z :=
  fzl59c_mem_normalizer_of_sq hg.conj_Z fun m hm => hA.Z_comm _ hg.sq_mem m hm

theorem fzl59c_gen_comm_B {g : G} (hg : fzl59c_Gen Z s t g) {x : G} (hx : x ∈ Z ⊔ zpowers s) :
    g * x * g⁻¹ * x⁻¹ ∈ Z := by
  have hB : Z ⊔ zpowers s ≤ fzl59c_modCent Z ({g} : Set G) := by
    refine sup_le (fun z hz => ?_) (zpowers_le.mpr ?_)
    · refine fzl59c_mem_modCent.mpr ⟨le_normalizer hz, fun y hy => ?_⟩
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have e : z * g * z⁻¹ * g⁻¹ = z * (g * z⁻¹ * g⁻¹) := by group
      rw [e]
      exact Z.mul_mem hz (hg.conj_Z z⁻¹ (Z.inv_mem hz))
    · refine fzl59c_mem_modCent.mpr ⟨?_, fun y hy => ?_⟩
      · refine fzl59c_mem_normalizer_of_sq (fun m hm => ?_) (fun m hm => ?_)
        · have e : s * m * s⁻¹ = m := by
            rw [hA.s_comm m hm]
            group
          rw [e]
          exact hm
        · rw [hA.s_sq]
          simp
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        obtain ⟨w, hw, hgs⟩ := hg.conj_s
        have hsw : s * w⁻¹ = w⁻¹ * s := hA.s_comm w⁻¹ (Z.inv_mem hw)
        have h1 : g * s⁻¹ * g⁻¹ = w⁻¹ * s⁻¹ := by
          calc g * s⁻¹ * g⁻¹ = (g * s * g⁻¹)⁻¹ := by group
            _ = (s * w)⁻¹ := by rw [hgs]
            _ = w⁻¹ * s⁻¹ := by group
        have e : s * g * s⁻¹ * g⁻¹ = w⁻¹ := by
          calc s * g * s⁻¹ * g⁻¹ = s * (g * s⁻¹ * g⁻¹) := by group
            _ = s * (w⁻¹ * s⁻¹) := by rw [h1]
            _ = (s * w⁻¹) * s⁻¹ := by group
            _ = (w⁻¹ * s) * s⁻¹ := by rw [hsw]
            _ = w⁻¹ := by group
        rw [e]
        exact Z.inv_mem hw
  have h := (fzl59c_mem_modCent.mp (hB hx)).2 g (Set.mem_singleton g)
  have e : g * x * g⁻¹ * x⁻¹ = (x * g * x⁻¹ * g⁻¹)⁻¹ := by group
  rw [e]
  exact Z.inv_mem h

theorem fzl59c_gen_mem_one {g : G} (hg : fzl59c_Gen Z s t g) :
    g ∈ fzl59c_modCent Z ((Z ⊔ zpowers s : Subgroup G) : Set G) :=
  fzl59c_mem_modCent.mpr ⟨fzl59c_gen_normalizer hA hg, fun _ hx => fzl59c_gen_comm_B hA hg hx⟩

theorem fzl59c_gen_normalizer_B {g : G} (hg : fzl59c_Gen Z s t g) :
    g ∈ normalizer ((Z ⊔ zpowers s : Subgroup G) : Set G) := by
  refine fzl59c_mem_normalizer_of_sq (fun m hm => ?_) (fun m hm => ?_)
  · have e : g * m * g⁻¹ = (g * m * g⁻¹ * m⁻¹) * m := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (fzl59c_gen_comm_B hA hg hm)) hm
  · exact (fzl59c_B_comm_Z hA hm hg.sq_mem).symm

theorem fzl59c_gen_mem_two {g : G} (hg : fzl59c_Gen Z s t g) :
    g ∈ fzl59c_modCent (Z ⊔ zpowers s) ({t} : Set G) := by
  refine fzl59c_mem_modCent.mpr ⟨fzl59c_gen_normalizer_B hA hg, fun x hx => ?_⟩
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  obtain ⟨β, hβ, hgt⟩ := hg.conj_t
  have hc : β * t = t * β := fzl59c_B_comm_t hA hβ
  have e : g * t * g⁻¹ * t⁻¹ = β := by
    rw [hgt]
    calc t * β * t⁻¹ = β * t * t⁻¹ := by rw [hc]
      _ = β := by group
  rw [e]
  exact hβ

theorem fzl59c_B_nrm {T : Subgroup G} (hT1 : ∀ g ∈ T, ∀ x ∈ Z ⊔ zpowers s, g * x * g⁻¹ * x⁻¹ ∈ Z)
    {g x : G} (hg : g ∈ T) (hx : x ∈ Z ⊔ zpowers s) : g * x * g⁻¹ ∈ Z ⊔ zpowers s := by
  have e : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left (hT1 g hg x hx)) hx

theorem fzl59c_F_nrm {T : Subgroup G} (hT1 : ∀ g ∈ T, ∀ x ∈ Z ⊔ zpowers s, g * x * g⁻¹ * x⁻¹ ∈ Z)
    (hT2 : ∀ g ∈ T, g * t * g⁻¹ * t⁻¹ ∈ Z ⊔ zpowers s) {g f : G} (hg : g ∈ T)
    (hf : f ∈ (Z ⊔ zpowers s) ⊔ zpowers t) : g * f * g⁻¹ ∈ (Z ⊔ zpowers s) ⊔ zpowers t := by
  refine fzl59c_conj_sup (P := Z ⊔ zpowers s) (Q := zpowers t)
    (F := (Z ⊔ zpowers s) ⊔ zpowers t) (fun x hx => ?_) (fun x hx => ?_) f hf
  · exact Subgroup.mem_sup_left (fzl59c_B_nrm hA hT1 hg hx)
  · obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    have h1 : g * t * g⁻¹ ∈ (Z ⊔ zpowers s) ⊔ zpowers t := by
      have e : g * t * g⁻¹ = (g * t * g⁻¹ * t⁻¹) * t := by group
      rw [e]
      exact mul_mem (Subgroup.mem_sup_left (hT2 g hg)) (Subgroup.mem_sup_right (mem_zpowers t))
    rw [← conj_zpow]
    exact zpow_mem h1 n

theorem fzl59c_cent_B [Finite G] {T : Subgroup G}
    (hT1 : ∀ g ∈ T, ∀ x ∈ Z ⊔ zpowers s, g * x * g⁻¹ * x⁻¹ ∈ Z)
    (hcard : Nat.card ↥T = 2 ^ 10) {β : G} (hβ : β ∈ Z ⊔ zpowers s) :
    2 ^ 8 ≤ Nat.card ↥(T ⊓ centralizer ({β} : Set G)) := by
  have hO : {y : G | ∃ g ∈ T, g * β * g⁻¹ = y} ⊆ (fun z => z * β) '' (Z : Set G) := by
    rintro y ⟨g, hg, rfl⟩
    exact ⟨g * β * g⁻¹ * β⁻¹, hT1 g hg β hβ, by group⟩
  have hle : Nat.card {y : G | ∃ g ∈ T, g * β * g⁻¹ = y} ≤ 4 := by
    calc Nat.card {y : G | ∃ g ∈ T, g * β * g⁻¹ = y}
        ≤ Nat.card ((fun z => z * β) '' (Z : Set G)) := Nat.card_mono (Set.toFinite _) hO
      _ = Nat.card (Z : Set G) := Nat.card_image_of_injective (mul_left_injective β) _
      _ = 4 := hA.card_Z
  have hc := fzl59c_card_orbit_mul T β
  rw [hcard] at hc
  have h2 : Nat.card {y : G | ∃ g ∈ T, g * β * g⁻¹ = y} *
      Nat.card ↥(T ⊓ centralizer ({β} : Set G)) ≤ 4 * Nat.card ↥(T ⊓ centralizer ({β} : Set G)) :=
    Nat.mul_le_mul_right _ hle
  omega

theorem fzl59c_orbit_t {T : Subgroup G} {z₀ z₁ : G} (hZ : Z = closure {z₀, z₁})
    (hw₀ : ∃ y ∈ T, (∀ x ∈ Z ⊔ zpowers s, y * x * y⁻¹ = x) ∧ y * t * y⁻¹ = t * z₀)
    (hw₁ : ∃ y ∈ T, (∀ x ∈ Z ⊔ zpowers s, y * x * y⁻¹ = x) ∧ y * t * y⁻¹ = t * z₁)
    (hws : ∃ y ∈ T, (∀ x ∈ Z ⊔ zpowers s, y * x * y⁻¹ = x) ∧ y * t * y⁻¹ = t * s)
    {β : G} (hβ : β ∈ Z ⊔ zpowers s) : ∃ g ∈ T, g * t * g⁻¹ = β * t := by
  have hz₀ : z₀ ∈ Z := by
    rw [hZ]
    exact subset_closure (Set.mem_insert _ _)
  have hz₁ : z₁ ∈ Z := by
    rw [hZ]
    exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hs : s ∈ Z ⊔ zpowers s := Subgroup.mem_sup_right (mem_zpowers s)
  have h0 : z₀ ∈ fzl59c_trSub T (Z ⊔ zpowers s) t :=
    fzl59c_mem_trSub.mpr ⟨Subgroup.mem_sup_left hz₀, hw₀⟩
  have h1 : z₁ ∈ fzl59c_trSub T (Z ⊔ zpowers s) t :=
    fzl59c_mem_trSub.mpr ⟨Subgroup.mem_sup_left hz₁, hw₁⟩
  have h2 : s ∈ fzl59c_trSub T (Z ⊔ zpowers s) t := fzl59c_mem_trSub.mpr ⟨hs, hws⟩
  have hle : Z ⊔ zpowers s ≤ fzl59c_trSub T (Z ⊔ zpowers s) t :=
    sup_le (hZ.le.trans
      ((closure_le _).mpr (Set.insert_subset h0 (Set.singleton_subset_iff.mpr h1))))
      (zpowers_le.mpr h2)
  obtain ⟨_, y, hy, _, hyt⟩ := fzl59c_mem_trSub.mp (hle hβ)
  exact ⟨y, hy, by rw [hyt]; exact (fzl59c_B_comm_t hA hβ).symm⟩

theorem fzl59c_cent_t [Finite G] {T : Subgroup G}
    (hT2 : ∀ g ∈ T, g * t * g⁻¹ * t⁻¹ ∈ Z ⊔ zpowers s) (hcard : Nat.card ↥T = 2 ^ 10)
    (horb : ∀ β ∈ Z ⊔ zpowers s, ∃ g ∈ T, g * t * g⁻¹ = β * t) :
    Nat.card ↥(T ⊓ centralizer ({t} : Set G)) = 2 ^ 7 := by
  have hO : {y : G | ∃ g ∈ T, g * t * g⁻¹ = y} =
      (fun β => β * t) '' ((Z ⊔ zpowers s : Subgroup G) : Set G) := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g * t * g⁻¹ * t⁻¹, hT2 g hg, by group⟩
    · rintro ⟨β, hβ, rfl⟩
      exact horb β hβ
  have hc := fzl59c_card_orbit_mul T t
  rw [hO, Nat.card_image_of_injective (mul_left_injective t), hcard] at hc
  have h8 : Nat.card (((Z ⊔ zpowers s : Subgroup G)) : Set G) = 8 := fzl59c_card_B hA
  rw [h8] at hc
  omega

end Chain

end CFSG.OddStandard.SmallF3.FritzII
