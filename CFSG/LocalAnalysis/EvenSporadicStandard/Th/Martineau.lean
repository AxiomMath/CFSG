module

public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Module Submodule

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

def TransvEquivariant (β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] V) : Prop :=
  ∀ (f : Dual (ZMod 2) V) (w : V), f w = 0 → ∀ u u' : V,
    β (u + f u • w) (u' + f u' • w) = β u u' + f (β u u') • w

omit [Module (ZMod 2) V] in
theorem zmod_two_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  revert a; decide

theorem exists_dual_one_of_notMem {p : Submodule (ZMod 2) V} {v : V} (hv : v ∉ p) :
    ∃ f : Dual (ZMod 2) V, f v = 1 ∧ ∀ u ∈ p, f u = 0 := by
  have : Module.Free (ZMod 2) (V ⧸ p) := Module.Free.of_divisionRing (ZMod 2) (V ⧸ p)
  obtain ⟨f, hf, hp⟩ := exists_dual_map_eq_bot_of_notMem hv inferInstance
  refine ⟨f, zmod_two_eq_one_of_ne_zero hf, fun u hu => ?_⟩
  have : f u ∈ p.map f := ⟨u, hu, rfl⟩
  rw [hp] at this
  exact this

omit [Module (ZMod 2) V] in
theorem zmod_two_add_self {R : Type*} [AddCommGroup R] [Module (ZMod 2) R] (v : R) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v]
  have : (2 : ZMod 2) = 0 := by decide
  rw [this, zero_smul]

theorem coeff_eq_zero_of_indep {u v : V} (hu : u ≠ 0) (hv : v ∉ span (ZMod 2) {u}) {a b : ZMod 2}
    (h : a • u + b • v = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    have hb1 : b = 1 := zmod_two_eq_one_of_ne_zero hb
    rw [hb1, one_smul] at h
    apply hv
    have : v = a • u := by
      have h2 : v = -(a • u) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
      rw [h2]
      have h3 : -(a • u) = a • u := by
        rw [neg_eq_iff_add_eq_zero]; exact zmod_two_add_self _
      exact h3
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  rw [hb, zero_smul, add_zero] at h
  refine ⟨?_, hb⟩
  by_contra ha
  exact hu (by
    have := zmod_two_eq_one_of_ne_zero ha
    rwa [this, one_smul] at h)

theorem not_mem_span_of_ne {x z : V} (hz : z ≠ 0)
    (h : x ∉ span (ZMod 2) {z}) : z ∉ span (ZMod 2) {x} := by
  intro hm
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hm
  have hc1 : c = 1 := zmod_two_eq_one_of_ne_zero (fun h0 => hz (by rw [← hc, h0, zero_smul]))
  rw [hc1, one_smul] at hc
  apply h
  rw [hc]
  exact Submodule.mem_span_singleton_self z

theorem exists_triple [FiniteDimensional (ZMod 2) V] (hdim : 3 ≤ finrank (ZMod 2) V) {z : V}
    (hz : z ≠ 0) :
    ∃ x y : V, x ∉ span (ZMod 2) {z} ∧ y ∉ span (ZMod 2) {z, x} := by
  classical
  have h1 : ∃ x : V, x ∉ span (ZMod 2) {z} := by
    by_contra hcon
    push Not at hcon
    have htop : span (ZMod 2) {z} = ⊤ := Submodule.eq_top_iff'.2 hcon
    have := finrank_span_singleton (K := ZMod 2) hz
    rw [htop, finrank_top] at this
    omega
  obtain ⟨x, hx⟩ := h1
  have h2 : ∃ y : V, y ∉ span (ZMod 2) {z, x} := by
    by_contra hcon
    push Not at hcon
    have htop : span (ZMod 2) {z, x} = ⊤ := Submodule.eq_top_iff'.2 hcon
    have h2 : finrank (ZMod 2) (span (ZMod 2) (↑({z, x} : Finset V) : Set V)) ≤
        ({z, x} : Finset V).card := finrank_span_finset_le_card _
    rw [Finset.coe_pair, htop, finrank_top] at h2
    have h3 : ({z, x} : Finset V).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨y, hy⟩ := h2
  exact ⟨x, y, hx, hy⟩

section Main

variable {β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] V} (hβ : TransvEquivariant β)
include hβ

theorem TransvEquivariant.exists_diag {x : V} (hx : x ≠ 0) : ∃ c : ZMod 2, β x x = c • x := by
  by_contra hcon
  have hnm : β x x ∉ span (ZMod 2) {x} := by
    intro hm
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hm
    exact hcon ⟨c, hc.symm⟩
  obtain ⟨f, hf1, hf0⟩ := exists_dual_one_of_notMem hnm
  have hfx : f x = 0 := hf0 x (Submodule.mem_span_singleton_self x)
  have h := hβ f x hfx x x
  rw [hfx, zero_smul, add_zero, hf1, one_smul] at h
  exact hx (by simpa using h)

theorem TransvEquivariant.offdiag {x y : V} {a b : ZMod 2} (hx : x ≠ 0)
    (hy : y ∉ span (ZMod 2) {x}) (hxx : β x x = a • x) (hyy : β y y = b • y) :
    β x y = b • x + a • y := by
  have hy0 : y ≠ 0 := fun h => hy (h ▸ Submodule.zero_mem _)
  have hxy : x ∉ span (ZMod 2) {y} := by
    intro hm
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hm
    have hc1 : c = 1 := zmod_two_eq_one_of_ne_zero (fun h => hx (by rw [← hc, h, zero_smul]))
    apply hy
    rw [hc1, one_smul] at hc
    rw [hc]
    exact Submodule.mem_span_singleton_self x
  have key : ∀ f : Dual (ZMod 2) V, f x = 0 → f y = 1 → f (β x y) = a := by
    intro f hfx hfy
    have h := hβ f x hfx x y
    rw [hfx, zero_smul, add_zero, hfy, one_smul, map_add, hxx] at h
    have h2 : a • x = f (β x y) • x := add_left_cancel h
    exact (smul_left_injective (ZMod 2) hx h2).symm
  obtain ⟨f, hfy, hf0⟩ := exists_dual_one_of_notMem hy
  have hfx : f x = 0 := hf0 x (Submodule.mem_span_singleton_self x)
  have hmem : β x y ∈ span (ZMod 2) {x, y} := by
    by_contra hnm
    obtain ⟨g, hg1, hg0⟩ := exists_dual_one_of_notMem hnm
    have hgx : g x = 0 := hg0 x (Submodule.subset_span (by simp))
    have hgy : g y = 0 := hg0 y (Submodule.subset_span (by simp))
    have h1 := key (f + g) (by simp [hfx, hgx]) (by simp [hfy, hgy])
    rw [LinearMap.add_apply, key f hfx hfy, hg1] at h1
    have : (1 : ZMod 2) = 0 := by
      have h2 : a + 1 = a + 0 := by rw [add_zero]; exact h1
      exact add_left_cancel h2
    exact absurd this (by decide)
  obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.1 hmem
  have hq : q = a := by
    have := key f hfx hfy
    rw [← hpq, map_add, map_smul, map_smul, hfx, hfy] at this
    simpa using this
  obtain ⟨f', hf'x, hf'0⟩ := exists_dual_one_of_notMem hxy
  have hf'y : f' y = 0 := hf'0 y (Submodule.mem_span_singleton_self y)
  have hp : p = b := by
    have h := hβ f' y hf'y x y
    rw [hf'y, zero_smul, add_zero, hf'x, one_smul, map_add, LinearMap.add_apply, hyy] at h
    have h2 : b • y = f' (β x y) • y := add_left_cancel h
    have h3 : f' (β x y) = b := (smul_left_injective (ZMod 2) hy0 h2).symm
    rw [← h3, ← hpq, map_add, map_smul, map_smul, hf'x, hf'y]
    simp
  rw [← hpq, hp, hq]

theorem TransvEquivariant.diag_eq_zero [FiniteDimensional (ZMod 2) V]
    (hdim : 3 ≤ finrank (ZMod 2) V) {z : V} (hz : z ≠ 0) : β z z = 0 := by
  obtain ⟨x, y, hxz, hyzx⟩ := exists_triple hdim hz
  have hx0 : x ≠ 0 := fun h => hxz (h ▸ Submodule.zero_mem _)
  have hy0 : y ≠ 0 := fun h => hyzx (h ▸ Submodule.zero_mem _)
  have hyx : y ∉ span (ZMod 2) {x} := fun hm =>
    hyzx (span_mono (by intro a ha; simp at ha ⊢; exact Or.inr ha) hm)
  have hyz : y ∉ span (ZMod 2) {z} := fun hm =>
    hyzx (span_mono (by intro a ha; simp at ha ⊢; exact Or.inl ha) hm)
  have hzx : z ∉ span (ZMod 2) {x} := not_mem_span_of_ne hz hxz
  have hzy : z ∉ span (ZMod 2) {y} := by
    intro hm
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hm
    have hc1 : c = 1 := zmod_two_eq_one_of_ne_zero (fun h => hz (by rw [← hc, h, zero_smul]))
    rw [hc1, one_smul] at hc
    exact hyzx (by rw [hc]; exact Submodule.subset_span (by simp))
  obtain ⟨cz, hcz⟩ := hβ.exists_diag hz
  obtain ⟨cx, hcx⟩ := hβ.exists_diag hx0
  obtain ⟨cy, hcy⟩ := hβ.exists_diag hy0
  have hyz' : β y z = cz • y + cy • z := hβ.offdiag hy0 hzy hcy hcz
  have hzy' : β z y = cy • z + cz • y := hβ.offdiag hz hyz hcz hcy
  have hw0 : y + z ≠ 0 := by
    intro h
    apply hyz
    have : y = -z := eq_neg_of_add_eq_zero_left h
    rw [this]
    have h3 : -z = z := by rw [neg_eq_iff_add_eq_zero]; exact zmod_two_add_self _
    rw [h3]
    exact Submodule.mem_span_singleton_self z
  have hwx : y + z ∉ span (ZMod 2) {x} := by
    intro hm
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hm
    apply hyzx
    have h2 : y = c • x + z := by
      have : y = c • x - z := eq_sub_of_add_eq (by rw [← hc])
      rw [this, sub_eq_add_neg]
      have h3 : -z = z := by rw [neg_eq_iff_add_eq_zero]; exact zmod_two_add_self _
      rw [h3]
    rw [h2]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.subset_span (by simp))
  obtain ⟨cw, hcw⟩ := hβ.exists_diag hw0
  have hww : β (y + z) (y + z) = cy • y + cz • z := by
    have hexp : β (y + z) (y + z) = β y y + β y z + β z y + β z z := by
      simp only [map_add, LinearMap.add_apply]; abel
    rw [hexp, hcy, hcz, hyz', hzy']
    calc cy • y + (cz • y + cy • z) + (cy • z + cz • y) + cz • z
        = cy • y + cz • z + ((cz • y + cz • y) + (cy • z + cy • z)) := by abel
      _ = cy • y + cz • z := by rw [zmod_two_add_self, zmod_two_add_self, add_zero, add_zero]
  have h1 : (cw - cy) • y + (cw - cz) • z = 0 := by
    rw [sub_smul, sub_smul]
    have : cw • y + cw • z = cy • y + cz • z := by rw [← smul_add, ← hcw]; exact hww
    calc cw • y - cy • y + (cw • z - cz • z) = (cw • y + cw • z) - (cy • y + cz • z) := by abel
      _ = 0 := by rw [this, sub_self]
  obtain ⟨hc1, hc2⟩ := coeff_eq_zero_of_indep hy0 hzy h1
  have hcwy : cw = cy := sub_eq_zero.1 hc1
  have hcwz : cw = cz := sub_eq_zero.1 hc2
  have hxy' : β x y = cy • x + cx • y := hβ.offdiag hx0 hyx hcx hcy
  have hxz' : β x z = cz • x + cx • z := hβ.offdiag hx0 hzx hcx hcz
  have hxw' : β x (y + z) = cw • x + cx • (y + z) := hβ.offdiag hx0 hwx hcx hcw
  have hsum : β x (y + z) = β x y + β x z := map_add _ _ _
  have h2 : (cw - cy - cz) • x = 0 := by
    rw [sub_smul, sub_smul]
    have : cw • x + cx • (y + z) = (cy • x + cx • y) + (cz • x + cx • z) := by
      rw [← hxw', hsum, hxy', hxz']
    calc cw • x - cy • x - cz • x
        = (cw • x + cx • (y + z)) - ((cy • x + cx • y) + (cz • x + cx • z)) := by
          simp only [smul_add]; abel
      _ = 0 := by rw [this, sub_self]
  have h3 : cw - cy - cz = 0 := (smul_eq_zero.1 h2).resolve_right hx0
  have h4 : cz = 0 := by
    have h5 : cw = cy + cz := by linear_combination h3
    have h6 : cz = cz + cz := by
      calc cz = cw := hcwz.symm
        _ = cy + cz := h5
        _ = cz + cz := by rw [← hcwy, hcwz]
    have h7 : ∀ a : ZMod 2, a = a + a → a = 0 := by decide
    exact h7 cz h6
  rw [hcz, h4, zero_smul]

theorem TransvEquivariant.eq_zero [FiniteDimensional (ZMod 2) V] (hdim : 3 ≤ finrank (ZMod 2) V) :
    β = 0 := by
  have hdiag : ∀ z : V, β z z = 0 := fun z => by
    by_cases hz : z = 0
    · simp [hz]
    · exact hβ.diag_eq_zero hdim hz
  have hoff : ∀ x y : V, β x y = 0 := by
    intro x y
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y ∈ span (ZMod 2) {x}
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [map_smul, hdiag, smul_zero]
    · rw [hβ.offdiag hx hy (by rw [hdiag, zero_smul]) (by rw [hdiag, zero_smul])]
      simp
  exact LinearMap.ext fun x => LinearMap.ext fun y => hoff x y

end Main

theorem martineau [FiniteDimensional (ZMod 2) V] (hdim : 3 ≤ finrank (ZMod 2) V)
    (β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] V)
    (hβ : ∀ (g : V ≃ₗ[ZMod 2] V) (u u' : V), β (g u) (g u') = g (β u u')) : β = 0 := by
  refine TransvEquivariant.eq_zero ?_ hdim
  intro f w hfw u u'
  have := hβ (LinearEquiv.transvection hfw) u u'
  exact this

end CFSG.EvenSporadicStandard.ThStd
