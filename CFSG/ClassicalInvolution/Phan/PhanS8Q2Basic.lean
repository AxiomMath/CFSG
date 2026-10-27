module

public import CFSG.ClassicalInvolution.Phan.PhanS4Std
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q

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

theorem orth_orthSpan (s : Set (Vec K)) :
    (bfL M).orthogonal (orthSpan M s) = Submodule.span K s :=
  LinearMap.BilinForm.orthogonal_orthogonal (bfL_nondegenerate M) (bfL_isSymm M).isRefl _

theorem mem_span_of_forall_orth {s : Set (Vec K)} {v : Vec K}
    (h : ∀ z ∈ orthSpan M s, bf M v z = 0) : v ∈ Submodule.span K s := by
  rw [← orth_orthSpan M s, LinearMap.BilinForm.mem_orthogonal_iff]
  intro z hz
  simpa [bfL_apply, bf_comm M z] using h z hz

structure Sesq (G : Vec K → Vec K → K) : Prop where
  add_left : ∀ x x' y, G (x + x') y = G x y + G x' y
  add_right : ∀ x y y', G x (y + y') = G x y + G x y'
  smul_left : ∀ (c : K) x y, G (c • x) y = c * G x y
  smul_right : ∀ (c : K) x y, G x (c • y) = M.τ c * G x y

theorem sesq_her : Sesq M (her M) :=
  ⟨her_add_left M, her_add_right M, her_smul_left M, her_smul_right M⟩

theorem bf_sum_left {ι : Type*} [Fintype ι] (l : ι → K) (x : ι → Vec K) (y : Vec K) :
    bf M (∑ i, l i • x i) y = ∑ i, l i * bf M (x i) y := by
  calc bf M (∑ i, l i • x i) y = bfL M (∑ i, l i • x i) y := (bfL_apply _ _ _).symm
    _ = ∑ i, l i * bfL M (x i) y := by
      simp [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
    _ = ∑ i, l i * bf M (x i) y := by simp [bfL_apply]

theorem bf_zero_left (y : Vec K) : bf M 0 y = 0 := by
  simp [bf]

section Four

variable {M}

@[expose] def GramInj (M : Model K) (x : Fin 4 → Vec K) : Prop :=
  ∀ l : Fin 4 → K, (∀ j, ∑ i, l i * bf M (x i) (x j) = 0) → l = 0

theorem GramInj.linearIndependent {x : Fin 4 → Vec K} (h : GramInj M x) :
    LinearIndependent K x := by
  rw [Fintype.linearIndependent_iff]
  intro l hl i
  have h0 : l = 0 := h l fun j => by
    rw [← bf_sum_left, hl, bf_zero_left]
  exact congrFun h0 i

theorem GramInj.finrank_span {x : Fin 4 → Vec K} (h : GramInj M x) :
    Module.finrank K (Submodule.span K (Set.range x)) = 4 := by
  rw [finrank_span_eq_card h.linearIndependent]
  simp

theorem GramInj.finrank_orth {x : Fin 4 → Vec K} (h : GramInj M x) :
    Module.finrank K (orthSpan M (Set.range x)) = 3 := by
  have h1 := LinearMap.BilinForm.finrank_orthogonal (bfL_nondegenerate M)
    (Submodule.span K (Set.range x))
  unfold orthSpan
  rw [h1, finrank_vec, h.finrank_span]

theorem mem_span_range_four {x : Fin 4 → Vec K} {s : Vec K}
    (hs : s ∈ Submodule.span K (Set.range x)) : ∃ l : Fin 4 → K, s = ∑ i, l i • x i := by
  obtain ⟨l, hl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hs
  exact ⟨l, hl.symm⟩

theorem GramInj.eq_zero_of_orth {x : Fin 4 → Vec K} (h : GramInj M x) {z : Vec K}
    (hz : z ∈ orthSpan M (Set.range x)) (hz' : ∀ z' ∈ orthSpan M (Set.range x), bf M z z' = 0) :
    z = 0 := by
  have hs : z ∈ Submodule.span K (Set.range x) := mem_span_of_forall_orth M hz'
  obtain ⟨l, rfl⟩ := mem_span_range_four hs
  have h0 : l = 0 := h l fun j => by
    rw [← bf_sum_left]
    exact (mem_orthSpan M).1 hz (x j) ⟨j, rfl⟩ |> fun h' => by rw [bf_comm]; exact h'
  subst h0
  simp

end Four

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q
