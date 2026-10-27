module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.GF2Type.Smith1979.Case2

namespace PhaseB

open Module QuadraticMap

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem polar_self_eq_zero (q : QuadraticForm (ZMod 2) V) (x : V) : polar q x x = 0 := by
  rw [polar_self, two_nsmul, ZModModule.add_self]

theorem polarBilin_isRefl (q : QuadraticForm (ZMod 2) V) : (polarBilin q).IsRefl := fun x y h => by
  rw [polarBilin_apply_apply] at h ⊢
  rwa [polar_comm]

structure Ctx (q : QuadraticForm (ZMod 2) V) (a : V) (E : Submodule (ZMod 2) V)
    (L : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop where
  nondeg : (polarBilin q).Nondegenerate
  finrank_V : finrank (ZMod 2) V = 12
  a_ne : a ≠ 0
  a_mem : a ∈ E
  finrank_E : finrank (ZMod 2) E = 6
  q_E : ∀ e ∈ E, q e = 0
  perp_E : ∀ x, (∀ e ∈ E, polar q x e = 0) → x ∈ E
  card_L : Nat.card L = 32
  q_apply : ∀ s ∈ L, ∀ x, q (s x) = q x
  mul_self : ∀ s ∈ L, s * s = 1
  apply_a : ∀ s ∈ L, s a = a
  comm : ∀ s ∈ L, ∀ s' ∈ L, s * s' = s' * s
  sub_E : ∀ s ∈ L, ∀ e ∈ E, s e - e ∈ Submodule.span (ZMod 2) {a}
  sub_A : ∀ s ∈ L, ∀ x, polar q a x = 0 → s x - x ∈ E
  faithful : ∀ s ∈ L, (∀ e ∈ E, s e = e) → s = 1

@[expose] def Asp (q : QuadraticForm (ZMod 2) V) (a : V) : Submodule (ZMod 2) V :=
  LinearMap.BilinForm.orthogonal (polarBilin q) (Submodule.span (ZMod 2) {a})

theorem mem_Asp {q : QuadraticForm (ZMod 2) V} {a x : V} : x ∈ Asp q a ↔ polar q a x = 0 := by
  rw [Asp, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    simpa using h a (Submodule.mem_span_singleton_self a)
  · intro h n hn
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hn
    simp [polar_smul_left, h]

theorem finrank_map_add_finrank_inf_ker [FiniteDimensional (ZMod 2) V] (f : V →ₗ[ZMod 2] V)
    (P : Submodule (ZMod 2) V) :
    finrank (ZMod 2) (P.map f) + finrank (ZMod 2) ↥(P ⊓ LinearMap.ker f) =
      finrank (ZMod 2) P := by
  let φ : P →ₗ[ZMod 2] V := f.comp P.subtype
  have hrange : LinearMap.range φ = P.map f := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hker : (LinearMap.ker φ).map P.subtype = P ⊓ LinearMap.ker f := by
    ext v
    rw [Submodule.mem_map, Submodule.mem_inf]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, hw⟩
    · rintro ⟨hv, hfix⟩
      exact ⟨⟨v, hv⟩, hfix, rfl⟩
  have h := LinearMap.finrank_range_add_finrank_ker φ
  rw [hrange] at h
  rw [← hker, Submodule.finrank_map_subtype_eq]
  exact h

@[expose] def Rsp (q : QuadraticForm (ZMod 2) V) (a : V) (s : V ≃ₗ[ZMod 2] V) :
    Submodule (ZMod 2) V :=
  Asp q a ⊓ (Submodule.span (ZMod 2) {a}).comap ((s : V →ₗ[ZMod 2] V) - 1)

theorem mem_Rsp {q : QuadraticForm (ZMod 2) V} {a : V} {s : V ≃ₗ[ZMod 2] V} {x : V} :
    x ∈ Rsp q a s ↔ x ∈ Asp q a ∧ s x - x ∈ Submodule.span (ZMod 2) {a} := by
  simp [Rsp, Submodule.mem_inf, Submodule.mem_comap]

namespace Ctx

variable {q : QuadraticForm (ZMod 2) V} {a : V} {E : Submodule (ZMod 2) V}
  {L : Subgroup (V ≃ₗ[ZMod 2] V)} (C : Ctx q a E L)

include C

theorem polar_E {e e' : V} (he : e ∈ E) (he' : e' ∈ E) : polar q e e' = 0 := by
  have h := C.q_E (e + e') (add_mem he he')
  have h2 : q (e + e') = q e + q e' + polar q e e' := QuadraticMap.map_add q e e'
  rw [h2, C.q_E e he, C.q_E e' he', zero_add, zero_add] at h
  exact h

theorem E_le_A : E ≤ Asp q a := fun _ he => mem_Asp.mpr (C.polar_E C.a_mem he)

theorem apply_apply {s : V ≃ₗ[ZMod 2] V} (hs : s ∈ L) (x : V) : s (s x) = x := by
  have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f x) (C.mul_self s hs)
  simpa using this

theorem polar_apply {s : V ≃ₗ[ZMod 2] V} (hs : s ∈ L) (x y : V) :
    polar q (s x) (s y) = polar q x y := by
  simp only [polar, ← map_add, C.q_apply s hs]

theorem polar_sub_swap {s : V ≃ₗ[ZMod 2] V} (hs : s ∈ L) (x y : V) :
    polar q (s x - x) y = polar q x (s y - y) := by
  have h : polar q (s x) y = polar q x (s y) := by
    have := C.polar_apply hs x (s y)
    rwa [C.apply_apply hs] at this
  rw [polar_sub_left, polar_sub_right, h]

theorem sub_sq {s : V ≃ₗ[ZMod 2] V} (hs : s ∈ L) (x : V) : s (s x - x) = s x - x := by
  rw [map_sub, C.apply_apply hs, ZModModule.sub_eq_add, ZModModule.sub_eq_add, add_comm]

theorem exists_partner : ∃ b, polar q a b = 1 := by
  by_contra h
  push Not at h
  refine C.a_ne (C.nondeg.1 a fun y => ?_)
  rw [polarBilin_apply_apply]
  have := h y
  generalize polar q a y = c at this ⊢
  revert c
  decide

variable [FiniteDimensional (ZMod 2) V]

theorem finrank_A : finrank (ZMod 2) (Asp q a) = 11 := by
  have h := LinearMap.BilinForm.finrank_orthogonal C.nondeg (Submodule.span (ZMod 2) {a})
  rw [finrank_span_singleton C.a_ne, C.finrank_V] at h
  exact h

theorem perp_A {u : V} (hu : ∀ x ∈ Asp q a, polar q x u = 0) :
    u ∈ Submodule.span (ZMod 2) {a} := by
  have h := LinearMap.BilinForm.orthogonal_orthogonal C.nondeg
    (polarBilin_isRefl q) (Submodule.span (ZMod 2) {a})
  rw [← h]
  refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun x hx => ?_
  rw [polarBilin_apply_apply]
  exact hu x hx

theorem not_range_le_E {s : V ≃ₗ[ZMod 2] V} (hs : s ∈ L) (hs1 : s ≠ 1) :
    ¬ LinearMap.range ((s : V →ₗ[ZMod 2] V) - 1) ≤ E := by
  intro hle
  refine hs1 (C.faithful s hs fun e he => ?_)
  have h0 : s e - e = 0 := by
    refine C.nondeg.1 _ fun x => ?_
    rw [polarBilin_apply_apply, C.polar_sub_swap hs]
    exact C.polar_E he (hle ⟨x, rfl⟩)
  exact sub_eq_zero.mp h0

theorem exists_sub_eq_a {s : V ≃ₗ[ZMod 2] V} (hs : s ∈ L) (hs1 : s ≠ 1) :
    ∃ e ∈ E, s e - e = a := by
  by_contra hcon
  push Not at hcon
  refine hs1 (C.faithful s hs fun e he => ?_)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (C.sub_E s hs e he)
  have h1 : c = 0 := by
    by_contra hc0
    have hc1 : c = 1 := by
      revert hc0
      generalize c = d
      revert d
      decide
    exact hcon e he (by rw [← hc, hc1, one_smul])
  rw [h1, zero_smul] at hc
  exact sub_eq_zero.mp hc.symm

theorem finrank_range_add_finrank_Rsp {s : V ≃ₗ[ZMod 2] V} (hs : s ∈ L) (hs1 : s ≠ 1) :
    finrank (ZMod 2) (LinearMap.range ((s : V →ₗ[ZMod 2] V) - 1)) +
      finrank (ZMod 2) (Rsp q a s) = 13 := by
  set N : V →ₗ[ZMod 2] V := (s : V →ₗ[ZMod 2] V) - 1 with hN
  have hNapp : ∀ x, N x = s x - x := fun x => by simp [hN]
  have hNA : (Asp q a).map N ≤ E := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hNapp]
    exact C.sub_A s hs x (mem_Asp.mp hx)
  have hlt : (Asp q a).map N < LinearMap.range N := by
    refine lt_of_le_of_ne (LinearMap.map_le_range) fun h => ?_
    exact C.not_range_le_E hs hs1 (h ▸ hNA)
  have hlt' := Submodule.finrank_lt_finrank_of_lt hlt
  have h1 := LinearMap.finrank_range_add_finrank_ker N
  have h2 := finrank_map_add_finrank_inf_ker N (Asp q a)
  have h3 : finrank (ZMod 2) ↥(Asp q a ⊓ LinearMap.ker N) ≤ finrank (ZMod 2) (LinearMap.ker N) :=
    Submodule.finrank_mono inf_le_right
  have hA := C.finrank_A
  have hV := C.finrank_V
  obtain ⟨e, he, hea⟩ := C.exists_sub_eq_a hs hs1
  have hmapR : (Rsp q a s).map N = Submodule.span (ZMod 2) {a} := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact (mem_Rsp.mp hx).2
    · rw [Submodule.span_singleton_le_iff_mem]
      refine ⟨e, mem_Rsp.mpr ⟨C.E_le_A he, ?_⟩, by rw [hNapp, hea]⟩
      rw [hea]
      exact Submodule.mem_span_singleton_self a
  have hinfR : Rsp q a s ⊓ LinearMap.ker N = Asp q a ⊓ LinearMap.ker N := by
    ext x
    simp only [Submodule.mem_inf, LinearMap.mem_ker, mem_Rsp]
    constructor
    · rintro ⟨⟨hx, -⟩, hk⟩
      exact ⟨hx, hk⟩
    · rintro ⟨hx, hk⟩
      refine ⟨⟨hx, ?_⟩, hk⟩
      have : s x - x = 0 := by rw [← hNapp]; exact hk
      rw [this]
      exact zero_mem _
  have h4 := finrank_map_add_finrank_inf_ker N (Rsp q a s)
  rw [hmapR, hinfR, finrank_span_singleton C.a_ne] at h4
  omega

end Ctx

end PhaseB

end CFSG.GF2Type.Smith1979.Case2
