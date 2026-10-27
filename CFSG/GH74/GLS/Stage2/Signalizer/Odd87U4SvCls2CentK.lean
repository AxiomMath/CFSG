module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls2Frame
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls2Levi
public import CFSG.GH74.GLS.IVK.Proofs2.NoOuter
public import CFSG.GH74.GLS.IVK.Proofs2.TwoTori
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Local.Prop27Cfg
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SurvU4Core
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvDefs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix Module CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped MatrixGroups commutatorElement

section CentK

variable {p f : ℕ} {K : Type} [Field K]

local macro "levi_expand" loc:Lean.Parser.Tactic.location : tactic =>
  `(tactic| simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Finset.univ_eq_empty,
    Finset.sum_empty, leviMat_ee, leviMat_ff, leviMat_ef, leviMat_fe, uEl_00, uEl_01, uEl_10, uEl_11,
    lEl_00, lEl_01, lEl_10, lEl_11, dualU_00, dualU_01, dualU_10, dualU_11, dualL_00, dualL_01,
    dualL_10, dualL_11] $loc:location)

theorem cross_zero_of_comm_levi (h : UnitaryFieldData p f K)
    (X : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
    (hX : ∀ A : SL(2, K), X * leviMat h A = leviMat h A * X) :
    (∀ i j : Fin 2, X (Sum.inl i) (Sum.inr (Sum.inr j)) = 0) ∧
      ∀ i j : Fin 2, X (Sum.inr (Sum.inr i)) (Sum.inl j) = 0 := by
  obtain ⟨τ, hτ⟩ := h.exists_bar_ne
  have hτ' : τ - h.bar τ ≠ 0 := sub_ne_zero.2 (Ne.symm hτ)
  have hb1 : h.bar 1 = 1 := map_one h.bar
  have u1 := fun a b => congrFun (congrFun (hX (uEl 1)) a) b
  have uτ := fun a b => congrFun (congrFun (hX (uEl τ)) a) b
  have l1 := fun a b => congrFun (congrFun (hX (lEl 1)) a) b
  have e10 := u1 (Sum.inr (Sum.inr 1)) (Sum.inl 0)
  have e11 := u1 (Sum.inr (Sum.inr 1)) (Sum.inl 1)
  have e12 := uτ (Sum.inr (Sum.inr 1)) (Sum.inl 1)
  have e20 := u1 (Sum.inl 0) (Sum.inr (Sum.inr 0))
  have e21 := uτ (Sum.inl 0) (Sum.inr (Sum.inr 0))
  have e22 := u1 (Sum.inl 1) (Sum.inr (Sum.inr 0))
  have e30 := l1 (Sum.inr (Sum.inr 1)) (Sum.inl 0)
  have e31 := l1 (Sum.inl 1) (Sum.inr (Sum.inr 0))
  levi_expand at e10 e11 e12 e20 e21 e22 e30 e31
  rw [hb1] at e10 e11 e20 e22
  have f0e0 : X (Sum.inr (Sum.inr 0)) (Sum.inl 0) = 0 := by linear_combination e10
  have f1e1 : X (Sum.inr (Sum.inr 1)) (Sum.inl 1) = 0 := by linear_combination e30
  have f1e0 : X (Sum.inr (Sum.inr 1)) (Sum.inl 0) = 0 := by
    have h1 : (τ - h.bar τ) * X (Sum.inr (Sum.inr 1)) (Sum.inl 0) = 0 := by
      linear_combination e12 - h.bar τ * e11
    exact (mul_eq_zero.1 h1).resolve_left hτ'
  have f0e1 : X (Sum.inr (Sum.inr 0)) (Sum.inl 1) = 0 := by linear_combination e11 - f1e0
  have e0f1 : X (Sum.inl 0) (Sum.inr (Sum.inr 1)) = 0 := by
    have h1 : (τ - h.bar τ) * X (Sum.inl 0) (Sum.inr (Sum.inr 1)) = 0 := by
      linear_combination e21 - τ * e20
    exact (mul_eq_zero.1 h1).resolve_left hτ'
  have e1f0 : X (Sum.inl 1) (Sum.inr (Sum.inr 0)) = 0 := by linear_combination -e20 - e0f1
  have e1f1 : X (Sum.inl 1) (Sum.inr (Sum.inr 1)) = 0 := by linear_combination -e22
  have e0f0 : X (Sum.inl 0) (Sum.inr (Sum.inr 0)) = 0 := by linear_combination -e31
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact e0f0
    · exact e0f1
    · exact e1f0
    · exact e1f1
  · fin_cases i <;> fin_cases j
    · exact f0e0
    · exact f0e1
    · exact f1e0
    · exact f1e1

theorem comm_a0_of_cross_zero (l : K) (X : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
    (h1 : ∀ i j : Fin 2, X (Sum.inl i) (Sum.inr (Sum.inr j)) = 0)
    (h2 : ∀ i j : Fin 2, X (Sum.inr (Sum.inr i)) (Sum.inl j) = 0) :
    X * a0Mat l = a0Mat l * X := by
  rw [a0Mat]
  ext a b
  rw [mul_diagonal, diagonal_mul]
  rcases a with i | k | i <;> rcases b with j | k' | j
  · simp [dSign, mul_comm]
  · exact k'.elim0
  · simp [h1]
  · exact k.elim0
  · exact k.elim0
  · exact k.elim0
  · simp [h2]
  · exact k'.elim0
  · simp [dSign, mul_comm]

theorem cls2_centK_frame (h : UnitaryFieldData p f K) {l : K} (hl0 : l ≠ 0) (hN : h.norm l = -1)
    (x : ↥(hypSU h 2 0))
    (hx : ∀ ι : SL(2, K) →* ↥(hypSU h 2 0),
      (∀ g, hypProj h 2 0 (ι g) ∈ fixSub (hypPhi h (a0U h hl0 hN))) → ∀ g, x * ι g = ι g * x) :
    hypPhi h (a0U h hl0 hN) (hypProj h 2 0 x) = hypProj h 2 0 x := by
  have hcomm : ∀ A : SL(2, K), x * leviSU h 0 A = leviSU h 0 A * x :=
    hx (leviSU h 0) (fun A => hypProj_mem_fixSub_of_comm h hl0 hN _ (a0Mat_comm_levi h l A))
  have hX : ∀ A : SL(2, K), ((x : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      leviMat h A = leviMat h A * ((x : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) :=
    fun A => by
    have := congrArg (fun g : ↥(hypSU h 2 0) => ((g : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K)) (hcomm A)
    simpa using this
  obtain ⟨c1, c2⟩ := cross_zero_of_comm_levi h _ hX
  exact hypProj_mem_fixSub_of_comm h hl0 hN x (comm_a0_of_cross_zero l _ c1 c2).symm

end CentK

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
