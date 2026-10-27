module

public import CFSG.ClassicalGroups.Alternating.PointRadical
import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)
open CFSG.LocalAnalysis.ComponentInitial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}

private theorem gl_ext_card {g h : LinearMap.GeneralLinearGroup K V}
    (H : ∀ x, (g : V →ₗ[K] V) x = (h : V →ₗ[K] V) x) : g = h :=
  Units.ext (LinearMap.ext H)

theorem forall_form_apply_siegel_eq_zero_iff [FiniteDimensional K V] (h2 : (2 : K) = 0)
    (hB : B.IsAlt) (hBn : B.Nondegenerate) {u w : V} (hu : u ≠ 0) (huw : B u w = 0) (c : K) :
    (∀ y, B y ((siegel B hB u w c : V →ₗ[K] V) y) = 0) ↔ c = 0 := by
  constructor
  · intro h
    by_contra hc
    obtain ⟨y, hy⟩ : ∃ y, B u y ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hu (hBn.1 u hne)
    have hyu : B y u ≠ 0 := by
      rw [← hB.neg_eq u y]
      exact neg_ne_zero.mpr hy
    have h1 := h y
    rw [siegel_form_apply_self h2 hB huw] at h1
    exact mul_ne_zero hc (pow_ne_zero 2 hyu) h1
  · rintro rfl y
    rw [siegel_form_apply_self h2 hB huw, zero_mul]

theorem siegel_add_smul_self (hB : B.IsAlt) {v w₀ : V} (hw₀ : B v w₀ = 0) (t c : K) :
    siegel B hB v (w₀ + t • v) c = siegel B hB v w₀ (c + 2 * t) := by
  have hw : B v (w₀ + t • v) = 0 := by simp [hw₀, hB.self_eq_zero]
  refine gl_ext_card fun x => ?_
  rw [siegel_apply hB hw, siegel_apply hB hw₀]
  simp only [map_add, map_smul, smul_eq_mul]
  module

theorem siegel_apply_partner (hB : B.IsAlt) {v b w : V} (hbv : B b v = -1) (hvw : B v w = 0)
    (hbw : B b w = 0) (c : K) : (siegel B hB v w c : V →ₗ[K] V) b = b - w - c • v := by
  rw [siegel_apply hB hvw, hbv, hbw]
  module

theorem card_pointRadical [FiniteDimensional K V] (hB : B.IsAlt)
    (hBn : B.Nondegenerate) {v : V} (hv : v ≠ 0) :
    Nat.card (pointRadical B hB v) = Nat.card K ^ (Module.finrank K V - 1) := by
  obtain ⟨b, hb⟩ := (alternating_hyperbolic_splitting hB hBn hv).1
  obtain ⟨hdim, -, -, -, -, hWdim⟩ := (alternating_hyperbolic_splitting hB hBn hv).2 b hb
  set W := B.orthogonal (Submodule.span K {v, b}) with hWdef
  have hWmem : ∀ x : V, x ∈ W ↔ B v x = 0 ∧ B b x = 0 := by
    intro x
    rw [hWdef, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      exact ⟨h v (Submodule.subset_span (by simp)), h b (Submodule.subset_span (by simp))⟩
    · rintro ⟨h1, h2⟩ n hn
      obtain ⟨s, r, rfl⟩ := Submodule.mem_span_pair.mp hn
      simp [h1, h2]
  have hWv : ∀ x : W, B v (x : V) = 0 := fun x => ((hWmem (x : V)).mp x.2).1
  have hWb : ∀ x : W, B b (x : V) = 0 := fun x => ((hWmem (x : V)).mp x.2).2
  have hbv : B b v = -1 := by rw [← hB.neg_eq, hb]
  have hbw : ∀ w : V, B b w = -B w b := fun w => (hB.neg_eq w b).symm
  let f : W × K → ↥(pointRadical B hB v) := fun p =>
    ⟨siegel B hB v (p.1 : V) p.2, siegel_mem_pointRadical hB (hWv p.1) p.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨x, c⟩ ⟨y, d⟩ hxy
    have h1 : siegel B hB v (x : V) c = siegel B hB v (y : V) d := congrArg Subtype.val hxy
    have h2 : (siegel B hB v (x : V) c : V →ₗ[K] V) b =
        (siegel B hB v (y : V) d : V →ₗ[K] V) b := by rw [h1]
    rw [siegel_apply_partner hB hbv (hWv x) (hWb x),
      siegel_apply_partner hB hbv (hWv y) (hWb y)] at h2
    have h3 := congrArg (B b) h2
    simp only [map_sub, map_smul, smul_eq_mul, hB.self_eq_zero, hWb x, hWb y, hbv] at h3
    have hcd : c = d := by linear_combination h3
    rw [hcd] at h2
    have h4 : (x : V) = y := sub_right_inj.mp (sub_left_inj.mp h2)
    exact Prod.ext (Subtype.ext h4) hcd
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨w, c, hw, rfl⟩ := hg
    have hw₀v : B v (w - (B w b) • v) = 0 := by simp [hw, hB.self_eq_zero]
    have hw₀ : w - (B w b) • v ∈ W := by
      rw [hWmem]
      refine ⟨hw₀v, ?_⟩
      rw [map_sub, map_smul, smul_eq_mul, hbv, hbw w]
      ring
    refine ⟨(⟨w - (B w b) • v, hw₀⟩, c + 2 * B w b), Subtype.ext ?_⟩
    show siegel B hB v (w - (B w b) • v) (c + 2 * B w b) = siegel B hB v w c
    rw [← siegel_add_smul_self hB hw₀v (B w b) c, sub_add_cancel]
  have hWcard : Nat.card W = Nat.card K ^ Module.finrank K W :=
    Module.natCard_eq_pow_finrank
  have hn : 2 ≤ Module.finrank K V := by
    have := Submodule.finrank_le (Submodule.span K ({v, b} : Set V))
    omega
  have e : Module.finrank K V - 1 = Module.finrank K V - 2 + 1 := by omega
  rw [← Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩, Nat.card_prod, hWcard, hWdim, e, pow_succ]

end CFSG.ClassicalGroups.Alternating
