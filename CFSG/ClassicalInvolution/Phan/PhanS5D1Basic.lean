module

public import CFSG.ClassicalInvolution.Phan.PhanS4Std
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.D

open CFSG.ClassicalInvolution.PhanB3.S.Std

variable {K : Type} [Field K] (M : Model K)

theorem bf_add_right (x y z : Vec K) : bf M x (y + z) = bf M x y + bf M x z := by
  rw [bf_comm, bf_add_left, bf_comm M y, bf_comm M z]

@[expose] def bfL : LinearMap.BilinForm K (Vec K) :=
  LinearMap.mk₂ K (bf M) (bf_add_left M) (fun c x y => by simpa using bf_smul_left M c x y)
    (bf_add_right M) (fun c x y => by simpa using bf_smul_right M c x y)

theorem bfL_apply (x y : Vec K) : bfL M x y = bf M x y := by
  simp [bfL]

theorem bfL_isSymm : (bfL M).IsSymm := ⟨fun x y => by simpa [bfL_apply] using bf_comm M x y⟩

@[expose] def ev (s : Fin 3 ⊕ Fin 3 ⊕ Unit) : Vec K := Pi.single s 1

theorem bf_ev_inl (x : Vec K) (i : Fin 3) : bf M x (ev (.inl i)) = x (.inr (.inl i)) := by
  simp [bf, ev, Pi.single_apply]

theorem bf_ev_inr (x : Vec K) (i : Fin 3) : bf M x (ev (.inr (.inl i))) = x (.inl i) := by
  simp [bf, ev, Pi.single_apply]

theorem bf_ev_c (x : Vec K) : bf M x (ev (.inr (.inr ()))) = M.κ * x (.inr (.inr ())) := by
  simp [bf, ev]

theorem eq_zero_of_bf_eq_zero {x : Vec K} (h : ∀ y, bf M x y = 0) : x = 0 := by
  funext s
  rcases s with i | i | u
  · have := h (ev (.inr (.inl i)))
    rwa [bf_ev_inr] at this
  · have := h (ev (.inl i))
    rwa [bf_ev_inl] at this
  · have := h (ev (.inr (.inr ())))
    rw [bf_ev_c] at this
    exact (mul_eq_zero.mp this).resolve_left M.κ_ne

theorem bfL_nondegenerate : (bfL M).Nondegenerate := by
  have h1 : (bfL M).SeparatingLeft := fun x hx =>
    eq_zero_of_bf_eq_zero M fun y => by simpa [bfL_apply] using hx y
  refine ⟨h1, fun y hy => eq_zero_of_bf_eq_zero M fun x => ?_⟩
  rw [bf_comm]
  simpa [bfL_apply] using hy x

theorem finrank_vec : Module.finrank K (Vec K) = 7 := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp

@[expose] def orthSpan (s : Set (Vec K)) : Submodule K (Vec K) :=
  (bfL M).orthogonal (Submodule.span K s)

theorem mem_orthSpan {s : Set (Vec K)} {c : Vec K} :
    c ∈ orthSpan M s ↔ ∀ u ∈ s, bf M u c = 0 := by
  unfold orthSpan
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h u hu
    simpa [bfL_apply] using h u (Submodule.subset_span hu)
  · intro h n hn
    induction hn using Submodule.span_induction with
    | mem u hu => simpa [bfL_apply] using h u hu
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul r x _ hx => simp [hx]

theorem finrank_orthSpan_ge (s : Finset (Vec K)) :
    7 - s.card ≤ Module.finrank K (orthSpan M (s : Set (Vec K))) := by
  have h1 := LinearMap.BilinForm.finrank_orthogonal (bfL_nondegenerate M)
    (Submodule.span K (s : Set (Vec K)))
  have h2 : Module.finrank K (Submodule.span K (s : Set (Vec K))) ≤ s.card :=
    finrank_span_finset_le_card s
  unfold orthSpan
  rw [h1, finrank_vec]
  omega

theorem orth_orthSpan (s : Set (Vec K)) :
    (bfL M).orthogonal (orthSpan M s) = Submodule.span K s :=
  LinearMap.BilinForm.orthogonal_orthogonal (bfL_nondegenerate M) (bfL_isSymm M).isRefl _

theorem mem_span_of_forall_orth {s : Set (Vec K)} {v : Vec K}
    (h : ∀ z ∈ orthSpan M s, bf M v z = 0) : v ∈ Submodule.span K s := by
  rw [← orth_orthSpan M s, LinearMap.BilinForm.mem_orthogonal_iff]
  intro z hz
  simpa [bfL_apply, bf_comm M z] using h z hz

end CFSG.ClassicalInvolution.PhanB3.S.Std.D
