module
public import CFSG.FeitThompson.Representations.FiniteOrderTraceCharacters
public import Mathlib.RepresentationTheory.Character
import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module TensorProduct LinearMap

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

section Aux

variable {M : Type*} [AddCommGroup M] [Module k M]

theorem restrict_congr {p : Submodule k M} {f g : Module.End k M}
    (hf : ∀ x ∈ p, f x ∈ p) (hg : ∀ x ∈ p, g x ∈ p) (h : ∀ x ∈ p, f x = g x) :
    f.restrict hf = g.restrict hg := by
  ext x
  rw [LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply]
  exact h x x.2

theorem restrict_eq_neg {p : Submodule k M} {f g : Module.End k M}
    (hf : ∀ x ∈ p, f x ∈ p) (hg : ∀ x ∈ p, g x ∈ p) (h : ∀ x ∈ p, f x = -g x) :
    f.restrict hf = -(g.restrict hg) := by
  ext x
  rw [LinearMap.coe_restrict_apply, LinearMap.neg_apply, Submodule.coe_neg,
    LinearMap.coe_restrict_apply]
  exact h x x.2

theorem trace_eq_add_of_isCompl [FiniteDimensional k M] {p q : Submodule k M} (h : IsCompl p q)
    (f : Module.End k M) (hp : ∀ x ∈ p, f x ∈ p) (hq : ∀ x ∈ q, f x ∈ q) :
    trace k M f = trace k p (f.restrict hp) + trace k q (f.restrict hq) := by
  classical
  have huniv : (Set.univ : Set Bool) = {true, false} := by ext b; cases b <;> simp
  have hint : DirectSum.IsInternal (fun b : Bool => if b then p else q) :=
    (DirectSum.isInternal_submodule_iff_isCompl _ (i := true) (j := false)
      (by simp) huniv).2 (by simpa using h)
  have hf : ∀ b : Bool, Set.MapsTo f ((if b then p else q) : Submodule k M)
      ((if b then p else q) : Submodule k M) := by
    intro b; cases b
    · exact fun x hx => hq x hx
    · exact fun x hx => hp x hx
  rw [LinearMap.trace_eq_sum_trace_restrict hint hf, Fintype.sum_bool]
  simp

end Aux

theorem Subrepresentation.character_eq_trace_restrict {ρ : Representation k G V}
    (ρ' : Subrepresentation ρ) (g : G) (h : ∀ x ∈ ρ'.toSubmodule, ρ g x ∈ ρ'.toSubmodule) :
    ρ'.toRepresentation.character g = trace k ρ'.toSubmodule ((ρ g).restrict h) := (rfl)

def tensorFlip (k : Type*) [CommSemiring k] (V : Type*) [AddCommMonoid V] [Module k V] :
    Module.End k (V ⊗[k] V) := (TensorProduct.comm k V V).toLinearMap

@[simp] theorem tensorFlip_tmul {k : Type*} [CommSemiring k] {V : Type*} [AddCommMonoid V]
    [Module k V] (v w : V) : tensorFlip k V (v ⊗ₜ w) = w ⊗ₜ v := (rfl)

@[simp] theorem tensorFlip_tensorFlip {k : Type*} [CommSemiring k] {V : Type*} [AddCommMonoid V]
    [Module k V] (x : V ⊗[k] V) : tensorFlip k V (tensorFlip k V x) = x :=
  (TensorProduct.comm k V V).symm_apply_apply x

theorem tensorFlip_map_apply (f : V →ₗ[k] V) (x : V ⊗[k] V) :
    tensorFlip k V (TensorProduct.map f f x) = TensorProduct.map f f (tensorFlip k V x) :=
  (TensorProduct.map_comm f f x).symm

theorem isCompl_eigenspace_tensorFlip (h2 : (2 : k) ≠ 0) :
    IsCompl (Module.End.eigenspace (tensorFlip k V) 1)
      (Module.End.eigenspace (tensorFlip k V) (-1)) := by
  constructor
  · rw [disjoint_iff_inf_le]
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, one_smul] at hx1
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, neg_one_smul] at hx2
    have hxx : x = -x := hx1.symm.trans hx2
    have h : (2 : k) • x = 0 := by
      rw [two_smul]; nth_rewrite 1 [hxx]; exact neg_add_cancel x
    rcases smul_eq_zero.1 h with h' | h'
    · exact absurd h' h2
    · simpa using h'
  · rw [codisjoint_iff_le_sup]
    intro x _
    have hd : x = (2 : k)⁻¹ • (x + tensorFlip k V x) + (2 : k)⁻¹ • (x - tensorFlip k V x) := by
      rw [← smul_add,
        show x + tensorFlip k V x + (x - tensorFlip k V x) = (2 : k) • x by rw [two_smul]; abel,
        smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [hd]
    refine Submodule.add_mem_sup (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
    · refine Module.End.mem_eigenspace_iff.2 ?_
      rw [map_add, one_smul, tensorFlip_tensorFlip]; abel
    · refine Module.End.mem_eigenspace_iff.2 ?_
      rw [map_sub, neg_one_smul, tensorFlip_tensorFlip]; abel

theorem trace_tensorFlip_comp_map [FiniteDimensional k V] (f : V →ₗ[k] V) :
    trace k (V ⊗[k] V) (tensorFlip k V ∘ₗ TensorProduct.map f f) = trace k V (f ∘ₗ f) := by
  classical
  obtain ⟨ι, b⟩ := Module.Free.exists_basis (R := k) (M := V)
  have hι : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  have key : ∀ p : ι × ι, (toMatrix (b.tensorProduct b) (b.tensorProduct b)
        (tensorFlip k V ∘ₗ TensorProduct.map f f)) p p
      = toMatrix b b f p.1 p.2 * toMatrix b b f p.2 p.1 := by
    rintro ⟨i, j⟩
    rw [LinearMap.toMatrix_apply]
    simp only [Basis.tensorProduct_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
      tensorFlip_tmul, Basis.tensorProduct_repr_tmul_apply, smul_eq_mul,
      LinearMap.toMatrix_apply]
    ring
  rw [LinearMap.trace_eq_matrix_trace k (b.tensorProduct b), Matrix.trace]
  simp only [Matrix.diag_apply, key]
  rw [LinearMap.trace_eq_matrix_trace k b, LinearMap.toMatrix_comp b b b, Matrix.trace,
    Fintype.sum_prod_type]
  simp [Matrix.mul_apply]

namespace Representation

def symmetricSquare (ρ : Representation k G V) : Subrepresentation (ρ.tprod ρ) where
  toSubmodule := Module.End.eigenspace (tensorFlip k V) 1
  apply_mem_toSubmodule g x hx := by
    rw [Module.End.mem_eigenspace_iff, one_smul] at hx ⊢
    rw [Representation.tprod_apply, tensorFlip_map_apply, hx]

def alternatingSquare (ρ : Representation k G V) : Subrepresentation (ρ.tprod ρ) where
  toSubmodule := Module.End.eigenspace (tensorFlip k V) (-1)
  apply_mem_toSubmodule g x hx := by
    rw [Module.End.mem_eigenspace_iff, neg_one_smul] at hx ⊢
    rw [Representation.tprod_apply, tensorFlip_map_apply, hx, map_neg]

@[simp] theorem symmetricSquare_toSubmodule (ρ : Representation k G V) :
    (symmetricSquare ρ).toSubmodule = Module.End.eigenspace (tensorFlip k V) 1 := (rfl)

@[simp] theorem alternatingSquare_toSubmodule (ρ : Representation k G V) :
    (alternatingSquare ρ).toSubmodule = Module.End.eigenspace (tensorFlip k V) (-1) := (rfl)

theorem mem_symmetricSquare_iff {ρ : Representation k G V} {x : V ⊗[k] V} :
    x ∈ (symmetricSquare ρ).toSubmodule ↔ tensorFlip k V x = x := by
  rw [symmetricSquare_toSubmodule, Module.End.mem_eigenspace_iff, one_smul]

theorem mem_alternatingSquare_iff {ρ : Representation k G V} {x : V ⊗[k] V} :
    x ∈ (alternatingSquare ρ).toSubmodule ↔ tensorFlip k V x = -x := by
  rw [alternatingSquare_toSubmodule, Module.End.mem_eigenspace_iff, neg_one_smul]

theorem tmul_add_tmul_mem_symmetricSquare {ρ : Representation k G V} (v w : V) :
    v ⊗ₜ[k] w + w ⊗ₜ[k] v ∈ (symmetricSquare ρ).toSubmodule := by
  rw [mem_symmetricSquare_iff, map_add, tensorFlip_tmul, tensorFlip_tmul]
  abel

theorem tmul_sub_tmul_mem_alternatingSquare {ρ : Representation k G V} (v w : V) :
    v ⊗ₜ[k] w - w ⊗ₜ[k] v ∈ (alternatingSquare ρ).toSubmodule := by
  rw [mem_alternatingSquare_iff, map_sub, tensorFlip_tmul, tensorFlip_tmul]
  abel

theorem isCompl_symmetricSquare_alternatingSquare (h2 : (2 : k) ≠ 0)
    (ρ : Representation k G V) :
    IsCompl (symmetricSquare ρ).toSubmodule (alternatingSquare ρ).toSubmodule := by
  simpa using isCompl_eigenspace_tensorFlip (k := k) (V := V) h2

variable [FiniteDimensional k V]

theorem character_symmetricSquare_add_alternatingSquare (h2 : (2 : k) ≠ 0)
    (ρ : Representation k G V) (g : G) :
    (symmetricSquare ρ).toRepresentation.character g
      + (alternatingSquare ρ).toRepresentation.character g = ρ.character g ^ 2 := by
  have h := trace_eq_add_of_isCompl (isCompl_symmetricSquare_alternatingSquare h2 ρ)
    ((ρ.tprod ρ) g) (fun _ hx => (symmetricSquare ρ).apply_mem_toSubmodule g hx)
    (fun _ hx => (alternatingSquare ρ).apply_mem_toSubmodule g hx)
  rw [Subrepresentation.character_eq_trace_restrict (symmetricSquare ρ) g
      (fun _ hx => (symmetricSquare ρ).apply_mem_toSubmodule g hx),
    Subrepresentation.character_eq_trace_restrict (alternatingSquare ρ) g
      (fun _ hx => (alternatingSquare ρ).apply_mem_toSubmodule g hx), ← h,
    Representation.tprod_apply, LinearMap.trace_tensorProduct', Representation.character, sq]

theorem character_symmetricSquare_sub_alternatingSquare (h2 : (2 : k) ≠ 0)
    (ρ : Representation k G V) (g : G) :
    (symmetricSquare ρ).toRepresentation.character g
      - (alternatingSquare ρ).toRepresentation.character g = ρ.character (g ^ 2) := by
  set F : Module.End k (V ⊗[k] V) := tensorFlip k V ∘ₗ (ρ.tprod ρ) g with hF
  have hFapp : ∀ x, F x = tensorFlip k V ((ρ.tprod ρ) g x) := fun _ => rfl
  have hp : ∀ x ∈ (symmetricSquare ρ).toSubmodule, F x ∈ (symmetricSquare ρ).toSubmodule := by
    intro x hx
    have h1 := (symmetricSquare ρ).apply_mem_toSubmodule g hx
    rw [hFapp, mem_symmetricSquare_iff.1 h1]
    exact h1
  have hq : ∀ x ∈ (alternatingSquare ρ).toSubmodule, F x ∈ (alternatingSquare ρ).toSubmodule := by
    intro x hx
    have h1 := (alternatingSquare ρ).apply_mem_toSubmodule g hx
    rw [hFapp, mem_alternatingSquare_iff.1 h1]
    exact Submodule.neg_mem _ h1
  have h := trace_eq_add_of_isCompl (isCompl_symmetricSquare_alternatingSquare h2 ρ) F hp hq
  have h1 : F.restrict hp = ((ρ.tprod ρ) g).restrict
      (fun _ hx => (symmetricSquare ρ).apply_mem_toSubmodule g hx) :=
    restrict_congr _ _ fun x hx => by
      rw [hFapp, mem_symmetricSquare_iff.1 ((symmetricSquare ρ).apply_mem_toSubmodule g hx)]
  have h3 : F.restrict hq = -(((ρ.tprod ρ) g).restrict
      (fun _ hx => (alternatingSquare ρ).apply_mem_toSubmodule g hx)) :=
    restrict_eq_neg _ _ fun x hx => by
      rw [hFapp, mem_alternatingSquare_iff.1 ((alternatingSquare ρ).apply_mem_toSubmodule g hx)]
  rw [h1, h3, map_neg] at h
  have hF2 : trace k (V ⊗[k] V) F = ρ.character (g ^ 2) := by
    rw [hF, Representation.tprod_apply, trace_tensorFlip_comp_map, Representation.character,
      sq, map_mul]
    rfl
  rw [Subrepresentation.character_eq_trace_restrict (symmetricSquare ρ) g
      (fun _ hx => (symmetricSquare ρ).apply_mem_toSubmodule g hx),
    Subrepresentation.character_eq_trace_restrict (alternatingSquare ρ) g
      (fun _ hx => (alternatingSquare ρ).apply_mem_toSubmodule g hx), ← hF2, h]
  ring

theorem character_symmetricSquare (h2 : (2 : k) ≠ 0) (ρ : Representation k G V) (g : G) :
    (symmetricSquare ρ).toRepresentation.character g
      = (ρ.character g ^ 2 + ρ.character (g ^ 2)) / 2 := by
  have hadd := character_symmetricSquare_add_alternatingSquare h2 ρ g
  have hsub := character_symmetricSquare_sub_alternatingSquare h2 ρ g
  field_simp
  linear_combination hadd + hsub

theorem character_alternatingSquare (h2 : (2 : k) ≠ 0) (ρ : Representation k G V) (g : G) :
    (alternatingSquare ρ).toRepresentation.character g
      = (ρ.character g ^ 2 - ρ.character (g ^ 2)) / 2 := by
  have hadd := character_symmetricSquare_add_alternatingSquare h2 ρ g
  have hsub := character_symmetricSquare_sub_alternatingSquare h2 ρ g
  field_simp
  linear_combination hadd - hsub

end Representation

end CFSG.FeitThompson
