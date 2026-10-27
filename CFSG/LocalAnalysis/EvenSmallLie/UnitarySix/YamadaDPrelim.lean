module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDSetting

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] {d : Data G}

theorem mem_normalizer_sup [Finite G] {A B : Subgroup G} {x : G}
    (hA : x ∈ normalizer (A : Set G)) (hB : x ∈ normalizer (B : Set G)) :
    x ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conj_mem
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj x).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact mem_sup_left ((mem_normalizer_iff.mp hA a).mp ha)
    · exact mem_sup_right ((mem_normalizer_iff.mp hB b).mp hb)
  exact fun y hy => hle hy

theorem mem_centralizer_sup {A B : Subgroup G} {x : G}
    (hA : x ∈ centralizer (A : Set G)) (hB : x ∈ centralizer (B : Set G)) :
    x ∈ centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  have hle : A ⊔ B ≤ centralizer ({x} : Set G) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hA a ha)
    · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hB b hb)
  rw [mem_centralizer_iff]
  intro y hy
  exact (mem_centralizer_singleton_iff.mp (hle hy))

namespace Hyp

variable (h : Hyp d)
include h

theorem t_inv : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right h.t_sq

theorem comm_of_mem_L {l : G} (hl : l ∈ d.L) : l * d.t = d.t * l :=
  mem_centralizer_singleton_iff.mp (h.L_le_H hl)

omit h in
theorem t_mem_H : d.t ∈ d.H := mem_centralizer_singleton_iff.mpr rfl

omit h in
theorem zpowers_t_le_H : zpowers d.t ≤ d.H := by
  rw [zpowers_le]
  exact t_mem_H

theorem withT_le_H {B : Subgroup G} (hB : B ≤ d.L) : d.withT B ≤ d.H :=
  sup_le (hB.trans h.L_le_H) zpowers_t_le_H

theorem mem_withT_iff {B : Subgroup G} (hB : B ≤ d.L) {x : G} :
    x ∈ d.withT B ↔ x ∈ B ∨ x * d.t ∈ B :=
  mem_sup_zpowers_iff h.t_sq (fun _ hb => h.comm_of_mem_L (hB hb))

theorem t_not_mem {B : Subgroup G} (hB : B ≤ d.L) : d.t ∉ B := fun ht => h.t_not_mem_L (hB ht)

theorem card_withT {B : Subgroup G} (hB : B ≤ d.L) :
    Nat.card (d.withT B) = 2 * Nat.card B :=
  card_sup_zpowers h.t_sq (fun _ hb => h.comm_of_mem_L (hB hb)) (h.t_not_mem hB)

omit h in
theorem t_mem_withT (B : Subgroup G) : d.t ∈ d.withT B := mem_sup_right (mem_zpowers _)

omit h in
theorem le_withT (B : Subgroup G) : B ≤ d.withT B := le_sup_left

theorem isPGroup_withT {B : Subgroup G} (hB : B ≤ d.L) (hB2 : IsPGroup 2 B) :
    IsPGroup 2 (d.withT B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : IsPGroup 2 (zpowers d.t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [sq]; exact h.t_sq) h.t_ne_one
  refine IsPGroup.to_sup_of_normal_left' hB2 ht2 ?_
  rw [zpowers_le]
  refine centralizer_le_normalizer _ ?_
  rw [mem_centralizer_iff]
  intro b hb
  exact h.comm_of_mem_L (hB hb)

theorem crossed_C₂ {c : G} (hc : c ∈ d.C₂) : c⁻¹ * d.t * c * d.t ∈ d.A₂ := by
  have h1 : c⁻¹ * d.t * c ∈ d.withT d.A₂ :=
    (mem_normalizer_iff''.mp (h.C₂_le hc) d.t).mp (t_mem_withT _)
  rcases (h.mem_withT_iff h.A₂_le_L).mp h1 with h2 | h2
  · exfalso
    apply h.t_not_mem h.A₂_le_L
    have hcomm := mem_centralizer_iff.mp (h.C₂_le_cent hc) _ h2
    have : d.t = c * (c⁻¹ * d.t * c) * c⁻¹ := by group
    rw [this, ← hcomm]
    simpa [mul_assoc] using h2
  · exact h2

theorem card_C₂ : Nat.card d.C₂ = 2 ^ 19 := by
  rw [card_eq_of_crossed_onto h.t_sq h.C₂_le_cent (fun c hc => h.crossed_C₂ hc) ?_]
  · change Nat.card (d.C₂ ⊓ d.H : Subgroup G) * _ = _
    rw [h.C₂_inf_H, h.card_withT h.A₂_le_L, h.card_A₂]
    norm_num
  · intro a ha
    obtain ⟨c, hc, hct⟩ := h.C₂_conj a ha
    refine ⟨c, hc, ?_⟩
    rw [hct, mul_assoc, h.t_sq, mul_one]

theorem not_conj_mem_A₂ [Finite G] (g : G) : g⁻¹ * d.t * g ∉ d.A₂ := by
  intro ha
  set C' := d.C₂.map (MulAut.conj g).toMonoidHom with hC'
  have hC'H : C' ≤ d.H := by
    rintro _ ⟨c, hc, rfl⟩
    have hcomm := mem_centralizer_iff.mp (h.C₂_le_cent hc) _ ha
    change g * c * g⁻¹ ∈ centralizer ({d.t} : Set G)
    rw [mem_centralizer_singleton_iff]
    calc g * c * g⁻¹ * d.t = g * (c * (g⁻¹ * d.t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * d.t * g) * c) * g⁻¹ := by rw [hcomm]
      _ = d.t * (g * c * g⁻¹) := by group
  have hcard : Nat.card C' = 2 ^ 19 := by
    rw [hC', Subgroup.card_map_of_injective (MulEquiv.injective _), h.card_C₂]
  have := h.card_le C' hC'H (h.C₂_pGroup.map _)
  rw [hcard] at this
  norm_num at this

theorem crossed_mem_of_normalizer [Finite G] {B : Subgroup G} (hB : B ≤ d.A₂) {x : G}
    (hx : x ∈ normalizer (d.withT B : Set G)) : x⁻¹ * d.t * x * d.t ∈ B := by
  have h1 : x⁻¹ * d.t * x ∈ d.withT B :=
    (mem_normalizer_iff''.mp hx d.t).mp (t_mem_withT _)
  rcases (h.mem_withT_iff (hB.trans h.A₂_le_L)).mp h1 with h2 | h2
  · exact absurd (hB h2) (h.not_conj_mem_A₂ x)
  · exact h2

theorem centA₄_le : centralizer (d.A₄ : Set G) ⊓ d.H ≤ normalizer (d.A₃ : Set G) :=
  fun _ hx => h.NHA₄_le ⟨centralizer_le_normalizer _ hx.1, hx.2⟩

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
