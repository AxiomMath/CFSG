module

public import CFSG.ClassicalInvolution.Phan.PhanS4Std
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.T

variable {K : Type} [Field K] (M : Model K)

theorem bf_zero_left (y : Vec K) : bf M 0 y = 0 := by
  simp [bf]

theorem bf_zero_right (x : Vec K) : bf M x 0 = 0 := by
  rw [bf_comm, bf_zero_left]

theorem bf_add_right (x y z : Vec K) : bf M x (y + z) = bf M x y + bf M x z := by
  rw [bf_comm, bf_add_left, bf_comm, bf_comm M z]

theorem bf_sub_left (x y z : Vec K) : bf M (x - y) z = bf M x z - bf M y z := by
  have h := bf_add_left M (x - y) y z
  rw [sub_add_cancel] at h
  linear_combination (-1 : K) * h

theorem bf_sub_right (x y z : Vec K) : bf M x (y - z) = bf M x y - bf M x z := by
  rw [bf_comm, bf_sub_left, bf_comm, bf_comm M z]

theorem bf_neg_left (x y : Vec K) : bf M (-x) y = -bf M x y := by
  have := bf_smul_left M (-1) x y
  simpa using this

theorem bf_neg_right (x y : Vec K) : bf M x (-y) = -bf M x y := by
  rw [bf_comm, bf_neg_left, bf_comm]

@[expose] def bfB : LinearMap.BilinForm K (Vec K) :=
  LinearMap.mk₂ K (bf M) (bf_add_left M) (bf_smul_left M) (bf_add_right M)
    (bf_smul_right M)

theorem bfB_apply (x y : Vec K) : bfB M x y = bf M x y := rfl

theorem bf_single_inr_inl (x : Vec K) (i : Fin 3) :
    bf M x (Pi.single (Sum.inr (Sum.inl i)) 1) = x (Sum.inl i) := by
  simp [bf, Pi.single_apply]

theorem bf_single_inl (x : Vec K) (i : Fin 3) :
    bf M x (Pi.single (Sum.inl i) 1) = x (Sum.inr (Sum.inl i)) := by
  simp [bf, Pi.single_apply]

theorem bf_single_c (x : Vec K) :
    bf M x (Pi.single (Sum.inr (Sum.inr ())) 1) = M.κ * x (Sum.inr (Sum.inr ())) := by
  simp [bf]

theorem eq_zero_of_bf_eq_zero {x : Vec K} (h : ∀ y, bf M x y = 0) : x = 0 := by
  funext s
  rcases s with i | i | u
  · have := h (Pi.single (Sum.inr (Sum.inl i)) 1)
    rw [bf_single_inr_inl] at this
    simpa using this
  · have := h (Pi.single (Sum.inl i) 1)
    rw [bf_single_inl] at this
    simpa using this
  · have := h (Pi.single (Sum.inr (Sum.inr ())) 1)
    rw [bf_single_c] at this
    have h2 : x (Sum.inr (Sum.inr ())) = 0 := by
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd h1 M.κ_ne
      · exact h1
    simpa [Subsingleton.elim u ()] using h2

theorem ker_bfB : LinearMap.ker (bfB M) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  refine eq_zero_of_bf_eq_zero M fun y => ?_
  have := congrArg (fun f => f y) hx
  simpa [bfB_apply] using this

theorem finrank_vec : Module.finrank K (Vec K) = 7 := by
  simp [Vec]

theorem ts3 {n : ℕ} (v : Fin n → Vec K) (hli : LinearIndependent K v)
    (h : ∀ i j, bf M (v i) (v j) = 0) : n ≤ 3 := by
  set S : Submodule K (Vec K) := Submodule.span K (Set.range v) with hSdef
  have hS : S ≤ (bfB M).orthogonal S := by
    intro x hx y hy
    show bf M y x = 0
    rw [hSdef] at hx hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact h j i
      | zero => exact bf_zero_right M _
      | add x₁ x₂ _ _ ih₁ ih₂ => rw [bf_add_right, ih₁, ih₂, add_zero]
      | smul c x _ ih => rw [bf_smul_right, ih, mul_zero]
    | zero => exact bf_zero_left M _
    | add y₁ y₂ _ _ ih₁ ih₂ => rw [bf_add_left, ih₁, ih₂, add_zero]
    | smul c y _ ih => rw [bf_smul_left, ih, mul_zero]
  have h1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := bfB M) S
  rw [ker_bfB, inf_bot_eq, finrank_bot, add_zero, finrank_vec] at h1
  have h2 : Module.finrank K S = n := by
    rw [hSdef, finrank_span_eq_card hli]
    simp
  have h3 : Module.finrank K S ≤ Module.finrank K ((bfB M).orthogonal S) :=
    Submodule.finrank_mono hS
  omega

end CFSG.ClassicalInvolution.PhanB3.S.Std.T
