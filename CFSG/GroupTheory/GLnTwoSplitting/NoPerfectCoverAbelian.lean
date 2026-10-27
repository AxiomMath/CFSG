module

public import CFSG.GroupTheory.GLnTwoSplitting.Extension

public section

namespace CFSG.GroupTheory.GLnTwoSplitting

open Module Submodule Subgroup
open scoped commutatorElement

section Commutator

variable {C : Type*} [Group C]

theorem commutatorElement_mul_left_of_mem_center {a z : C} (b : C) (hz : z ∈ center C) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have h : z * b = b * z := (mem_center_iff.1 hz b).symm
  calc ⁅a * z, b⁆ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [commutatorElement_def]; group
    _ = ⁅a, b⁆ := by rw [h, commutatorElement_def]; group

theorem commutatorElement_mul_right_of_mem_center (a : C) {b z : C} (hz : z ∈ center C) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv, commutatorElement_mul_left_of_mem_center a hz,
    commutatorElement_inv]

theorem commutatorElement_eq_of_map_eq {D : Type*} [Group D] {f : C →* D}
    (hcen : f.ker ≤ center C) {a a' b b' : C} (ha : f a = f a') (hb : f b = f b') :
    ⁅a', b'⁆ = ⁅a, b⁆ := by
  have hz : a⁻¹ * a' ∈ center C :=
    hcen (by rw [MonoidHom.mem_ker, map_mul, map_inv, ha, inv_mul_cancel])
  have hz' : b⁻¹ * b' ∈ center C :=
    hcen (by rw [MonoidHom.mem_ker, map_mul, map_inv, hb, inv_mul_cancel])
  rw [← mul_inv_cancel_left a a', ← mul_inv_cancel_left b b',
    commutatorElement_mul_left_of_mem_center _ hz, commutatorElement_mul_right_of_mem_center _ hz']

theorem commutatorElement_mul_right_eq {a x b : C} (h : ⁅a, b⁆ * x⁻¹ = x⁻¹ * ⁅a, b⁆) :
    ⁅a, x * b⁆ = ⁅a, x⁆ * ⁅a, b⁆ := by
  calc ⁅a, x * b⁆ = a * x * a⁻¹ * (⁅a, b⁆ * x⁻¹) := by
        simp only [commutatorElement_def]
        group
    _ = ⁅a, x⁆ * ⁅a, b⁆ := by
        rw [h]
        simp only [commutatorElement_def]
        group

end Commutator

theorem exists_dual_apply_eq_zero_of_three_le {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (hE : 3 ≤ finrank (ZMod 2) E) (a b : E) :
    ∃ (f : Dual (ZMod 2) E) (x : E), f a = 0 ∧ f b = 0 ∧ f x = 1 := by
  obtain ⟨x, -, hx⟩ := exists_mem_notMem_of_finrank_lt (U := ⊤) (S := span (ZMod 2) {a, b})
    (by rw [finrank_top]; have := finrank_span_pair_le a b; omega)
  obtain ⟨f, hf, hfx⟩ := exists_dual_eq_one_of_notMem hx
  exact ⟨f, x, hf a (subset_span (by simp)), hf b (subset_span (by simp)), hfx⟩

namespace NatExt

variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  (X : NatExt G E) {C : Type*} [Group C] {p : C →* G}

theorem exists_eq_ι_of_π_eq_one {v : C} (hv : X.π (p v) = 1) : ∃ e, p v = X.ι e := by
  obtain ⟨e, he⟩ := (X.ker_iff _).1 hv
  exact ⟨e, he.symm⟩

theorem map_conj_eq_ι {v : C} {e : E} (hv : p v = X.ι e) (g : C) :
    p (g * v * g⁻¹) = X.ι (X.π (p g) e) := by
  rw [map_mul, map_mul, map_inv, hv, X.conj]

theorem commutatorElement_mem_ker {u w : C} {μ ν : E} (hu : p u = X.ι μ) (hw : p w = X.ι ν) :
    ⁅u, w⁆ ∈ p.ker := by
  rw [MonoidHom.mem_ker, map_commutatorElement, hu, hw, commutatorElement_eq_one_iff_mul_comm,
    X.ι_mul_comm]

variable (hp : Function.Surjective p) (hcen : p.ker ≤ center C)
include hp hcen

theorem commute_of_π_eq_one [FiniteDimensional (ZMod 2) E] (hE : 3 ≤ finrank (ZMod 2) E)
    {a b : C} (ha : X.π (p a) = 1) (hb : X.π (p b) = 1) : a * b = b * a := by
  obtain ⟨α, hα⟩ := X.exists_eq_ι_of_π_eq_one ha
  obtain ⟨β, hβ⟩ := X.exists_eq_ι_of_π_eq_one hb
  obtain ⟨f, x₀, hfα, hfβ, hfx⟩ := exists_dual_apply_eq_zero_of_three_le hE α β
  obtain ⟨x, hx⟩ := hp (X.ι x₀)
  obtain ⟨g, hg⟩ := (X.surjective.comp hp) (LinearEquiv.transvection hfβ)
  have hg' : X.π (p g) = LinearEquiv.transvection hfβ := hg
  have h1 : p a = p (g * a * g⁻¹) := by
    rw [X.map_conj_eq_ι hα, hg', transvection_apply, hfα, zero_smul, add_zero, hα]
  have h2 : p (x * b) = p (g * x * g⁻¹) := by
    rw [X.map_conj_eq_ι hx, hg', transvection_apply, hfx, one_smul, X.ι_add, map_mul, hx, hβ]
  have hc : ⁅a, x⁆ ∈ center C := hcen (X.commutatorElement_mem_ker hα hx)
  have hd : ⁅a, b⁆ ∈ center C := hcen (X.commutatorElement_mem_ker hα hβ)
  have h3 : ⁅a, x⁆ = ⁅a, x⁆ * ⁅a, b⁆ := by
    calc ⁅a, x⁆ = g * ⁅a, x⁆ * g⁻¹ := by rw [mem_center_iff.1 hc g, mul_inv_cancel_right]
      _ = ⁅g * a * g⁻¹, g * x * g⁻¹⁆ := by simp only [commutatorElement_def]; group
      _ = ⁅a, x * b⁆ := commutatorElement_eq_of_map_eq hcen h1 h2
      _ = ⁅a, x⁆ * ⁅a, b⁆ := commutatorElement_mul_right_eq (mem_center_iff.1 hd x⁻¹).symm
  exact commutatorElement_eq_one_iff_mul_comm.1 (left_eq_mul.1 h3)

theorem mul_self_eq_one_of_π_eq_one [FiniteDimensional (ZMod 2) E] (hE : 3 ≤ finrank (ZMod 2) E)
    (hsq : ∀ z ∈ p.ker, z * z = 1) {a : C} (ha : X.π (p a) = 1) : a * a = 1 := by
  obtain ⟨α, hα⟩ := X.exists_eq_ι_of_π_eq_one ha
  obtain ⟨f, x₀, hfα, -, hfx⟩ := exists_dual_apply_eq_zero_of_three_le hE α α
  obtain ⟨x, hx⟩ := hp (X.ι x₀)
  obtain ⟨g, hg⟩ := (X.surjective.comp hp) (LinearEquiv.transvection hfα)
  have hg' : X.π (p g) = LinearEquiv.transvection hfα := hg
  have hxπ : X.π (p x) = 1 := by rw [hx, X.π_ι]
  have hz : (x * a)⁻¹ * (g * x * g⁻¹) ∈ p.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, X.map_conj_eq_ι hx, hg', transvection_apply, hfx,
      one_smul, X.ι_add, map_mul, hx, hα, inv_mul_cancel]
  set z := (x * a)⁻¹ * (g * x * g⁻¹) with hz_def
  have hgx : g * x * g⁻¹ = x * a * z := by rw [hz_def, mul_inv_cancel_left]
  have hxx : x * x ∈ p.ker := by rw [MonoidHom.mem_ker, map_mul, hx, X.ι_mul_self]
  have hzc := mem_center_iff.1 (hcen hz)
  have hax : a * x = x * a := X.commute_of_π_eq_one hp hcen hE ha hxπ
  have h1 : x * x = x * x * (a * a) := by
    calc x * x = g * (x * x) * g⁻¹ := by
          rw [mem_center_iff.1 (hcen hxx) g, mul_inv_cancel_right]
      _ = g * x * g⁻¹ * (g * x * g⁻¹) := by group
      _ = x * a * (z * (x * a)) * z := by rw [hgx]; group
      _ = x * (a * x) * a * (z * z) := by rw [← hzc (x * a)]; group
      _ = x * x * (a * a) := by rw [hax, hsq z hz]; group
  exact left_eq_mul.1 h1

end NatExt

end CFSG.GroupTheory.GLnTwoSplitting
