module

public import CFSG.ClassicalInvolution.ModelFacts.MF15Defs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Fundamental

public section

namespace CFSG.ClassicalInvolution.ModelFacts.MF15

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

namespace SemiSim

variable (x : SemiSim Q)

theorem map_zero : x.toFun 0 = 0 := by
  have h := x.map_add' 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

theorem map_neg (v : V) : x.toFun (-v) = - x.toFun v := by
  have h := x.map_add' v (-v)
  rw [add_neg_cancel, x.map_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem map_sub (v w : V) : x.toFun (v - w) = x.toFun v - x.toFun w := by
  rw [sub_eq_add_neg, x.map_add', x.map_neg, ← sub_eq_add_neg]

theorem polar_map (v w : V) :
    polar Q (x.toFun v) (x.toFun w) = x.μ * x.φ (polar Q v w) := by
  have h : Q (x.toFun v + x.toFun w) = x.μ * x.φ (Q (v + w)) := by
    rw [← x.map_add']; exact x.map_Q' _
  simp only [polar, h, x.map_Q', _root_.map_sub]
  ring

theorem surjective : Function.Surjective x.toFun := x.bijective.2

theorem injective : Function.Injective x.toFun := x.bijective.1

theorem coords_map_eq_zero (fr : Frame Q)
    (T : Matrix (Fin 2) (Fin 2) F → Matrix (Fin 2) (Fin 2) F)
    (hT : ∀ X, x.toFun (fr.incl X) = fr.incl (T X)) (hTs : Function.Surjective T)
    {r : V} (hr : fr.coords r = 0) : fr.coords (x.toFun r) = 0 := by
  rw [← Frame.mem_perp_iff, Frame.mem_perp_iff_forall_incl]
  intro Y
  obtain ⟨X, rfl⟩ := hTs Y
  rw [← hT, x.polar_map]
  have : polar Q r (fr.incl X) = 0 :=
    (Frame.mem_perp_iff_forall_incl fr).mp ((Frame.mem_perp_iff fr).mpr hr) X
  rw [this, _root_.map_zero, mul_zero]

end SemiSim

@[expose] def frameOfVectors (e₁ f₁ e₂ f₂ : V) (h1 : Q e₁ = 0) (h2 : Q f₁ = 0)
    (h3 : polar Q e₁ f₁ = 1) (h4 : Q e₂ = 0) (h5 : Q f₂ = 0) (h6 : polar Q e₂ f₂ = 1)
    (h7 : polar Q e₁ e₂ = 0) (h8 : polar Q e₁ f₂ = 0) (h9 : polar Q f₁ e₂ = 0)
    (h10 : polar Q f₁ f₂ = 0) : Frame Q :=
  ⟨⟨e₁, f₁, h1, h2, h3⟩, ⟨e₂, f₂, h4, h5, h6⟩, ⟨h7, h8, h9, h10⟩⟩

theorem incl_frameOfVectors (e₁ f₁ e₂ f₂ : V) (h1 : Q e₁ = 0) (h2 : Q f₁ = 0)
    (h3 : polar Q e₁ f₁ = 1) (h4 : Q e₂ = 0) (h5 : Q f₂ = 0) (h6 : polar Q e₂ f₂ = 1)
    (h7 : polar Q e₁ e₂ = 0) (h8 : polar Q e₁ f₂ = 0) (h9 : polar Q f₁ e₂ = 0)
    (h10 : polar Q f₁ f₂ = 0) (X : Matrix (Fin 2) (Fin 2) F) :
    (frameOfVectors e₁ f₁ e₂ f₂ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).incl X =
      X 0 0 • e₁ + X 1 1 • f₁ + (-X 0 1) • e₂ + X 1 0 • f₂ := rfl

section Comm

variable (fr : Frame Q) (x : SemiSim Q)

theorem comm_embLin (T : Matrix (Fin 2) (Fin 2) F → Matrix (Fin 2) (Fin 2) F)
    (hT : ∀ X, x.toFun (fr.incl X) = fr.incl (T X)) (hTs : Function.Surjective T)
    (S : Module.End F (Matrix (Fin 2) (Fin 2) F)) (hS : ∀ X, T (S X) = S (T X)) (v : V) :
    x.toFun (fr.embLin S v) = fr.embLin S (x.toFun v) := by
  set c := fr.coords v with hc
  set r := v - fr.incl c with hr
  have hr0 : fr.coords r = 0 := by
    rw [hr, map_sub, Frame.coords_incl, hc, sub_self]
  have hxr : fr.coords (x.toFun r) = 0 := x.coords_map_eq_zero fr T hT hTs hr0
  have hv : v = fr.incl c + r := by rw [hr]; abel
  have h1 : x.toFun (fr.embLin S v) = fr.incl (T (S c)) + x.toFun r := by
    rw [Frame.embLin_apply_eq, x.map_add', hT]
  have h2 : x.toFun v = fr.incl (T c) + x.toFun r := by
    conv_lhs => rw [hv]
    rw [x.map_add', hT]
  have h3 : fr.embLin S (x.toFun v) = fr.incl (S (T c)) + x.toFun r := by
    rw [Frame.embLin_apply_eq, h2, map_add, Frame.coords_incl, hxr, add_zero]
    abel
  rw [h1, h3, hS]

end Comm

end CFSG.ClassicalInvolution.ModelFacts.MF15
