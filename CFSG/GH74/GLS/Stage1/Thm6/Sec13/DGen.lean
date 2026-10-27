module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.DCtx

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

namespace D13

variable {x : G} {T V H : Subgroup G} {f : G} (d : D13 x T V H f) {Q : Subgroup G}
include d

theorem cls_sub' (hQ : Q ≤ normalizer (V : Set G) ⊓ normalizer (H : Set G)) {y : G}
    (hy : y ∈ cls Q x) : ∃ q ∈ Hzero H f, y = q * x := by
  obtain ⟨m, hm, rfl⟩ := hy
  exact d.conj_mem (hQ hm).1 (hQ hm).2

theorem f_stable' (hfQ : ∀ q ∈ Q, f * q * f⁻¹ ∈ Q) {y : G} (hy : y ∈ cls Q x) :
    f * y * f⁻¹ ∈ cls Q x := by
  obtain ⟨m, hm, rfl⟩ := hy
  refine ⟨f * m * f⁻¹, hfQ m hm, ?_⟩
  calc f * (m * x * m⁻¹) * f⁻¹ = (f * m * f⁻¹) * (f * x * f⁻¹) * (f * m * f⁻¹)⁻¹ := by group
    _ = (f * m * f⁻¹) * x * (f * m * f⁻¹)⁻¹ := by rw [d.f_x]

theorem fix_eq' (hQ : Q ≤ normalizer (V : Set G) ⊓ normalizer (H : Set G)) {y : G}
    (hy : y ∈ cls Q x) (hfy : f * y * f⁻¹ = y) : y = x := by
  obtain ⟨q, hq, rfl⟩ := d.cls_sub' hQ hy
  have hH : q * x ∈ H := H.mul_mem (d.H0_le hq) d.hI.x_mem
  have hc : q * x ∈ H ⊓ centralizer ({f} : Set G) := by
    refine ⟨hH, ?_⟩
    show q * x ∈ centralizer ({f} : Set G)
    rw [mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact mul_inv_eq_iff_eq_mul.1 hfy
  rw [d.hI.C_H, mem_zpowers_involution d.out.x_sq] at hc
  rcases hc with h1 | h1
  · exfalso
    obtain ⟨m, -, hmy⟩ := hy
    have h2 : m * x * m⁻¹ = 1 := by rw [← hmy]; exact h1
    apply d.out.x_ne
    calc x = m⁻¹ * (m * x * m⁻¹) * m := by group
      _ = 1 := by rw [h2]; group
  · exact h1

theorem card_cls_mod3' [Finite G] (hQ : Q ≤ normalizer (V : Set G) ⊓ normalizer (H : Set G))
    (hfQ : ∀ q ∈ Q, f * q * f⁻¹ ∈ Q) : Nat.card (cls Q x) % 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := d.hI.f3
  have h := card_fix_modEq (p := 3) (cls Q x) f k hk (fun v hv => d.f_stable' hfQ hv)
  have h1 : Nat.card {v : (cls Q x) // f * (v : G) * f⁻¹ = v} = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨⟨x, x_mem_cls⟩, d.f_x⟩, ?_⟩
    intro w
    apply Subtype.ext; apply Subtype.ext
    exact d.fix_eq' hQ w.1.2 w.2
  rw [h1] at h
  unfold Nat.ModEq at h
  simpa using h

theorem card_cls_le' [Finite G] (hQ : Q ≤ normalizer (V : Set G) ⊓ normalizer (H : Set G)) :
    Nat.card (cls Q x) ≤ Nat.card (Hzero H f) := by
  have hsub : cls Q x ⊆ (fun q => q * x) '' (Hzero H f : Set G) := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := d.cls_sub' hQ hy
    exact ⟨q, hq, rfl⟩
  calc Nat.card (cls Q x) = (cls Q x).ncard := Nat.card_coe_set_eq _
    _ ≤ ((fun q => q * x) '' (Hzero H f : Set G)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (Hzero H f : Set G).ncard := Set.ncard_image_le (Set.toFinite _)
    _ = Nat.card (Hzero H f) := (Nat.card_coe_set_eq _).symm

end D13

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
