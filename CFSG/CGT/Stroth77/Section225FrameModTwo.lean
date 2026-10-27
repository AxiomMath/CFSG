module

public import CFSG.CGT.Stroth77.Section225FrameTorus
public import CFSG.CGT.Stroth77.TorusNormalForm
public import CFSG.CGT.Stroth77.TypePredicates

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace Stroth225Frame

@[expose] def barUv : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 1; 0, 1, 0; 0, 0, 1]
@[expose] def barT : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 1; 0, 1, 0; 0, 0, 1]
@[expose] def barU : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 0, 1; 0, 1, 0]
@[expose] def barRho : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 1; 0, 0, 1; 0, 1, 1]
@[expose] def topUv : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 1, 1, 0; 1, 0, 1]
@[expose] def topT : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 1, 1, 0; 0, 0, 1]
@[expose] def topU : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 0, 1; 0, 1, 0]
@[expose] def topRho : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 0, 1; 0, 1, 1]

theorem rhoTwo_mulVec (v : Fin 3 → ℤ) :
    ofCols ![1, 0, 0] ![0, 0, 1] ![-1, -1, -1] *ᵥ v = ![v 0 - v 2, -v 2, v 1 - v 2] := by
  funext i
  fin_cases i <;> simp [ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem ofCols_mulVec_apply (P Q V w : Fin 3 → ℤ) (i : Fin 3) :
    (ofCols P Q V *ᵥ w) i = P i * w 0 + Q i * w 1 + V i * w 2 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, ofCols_apply]
  rfl

theorem bar_uv_t_of_cols {X Y Z W : Fin 3 → ℤ}
    (hX : ∀ i, ((X i : ℤ) : ZMod 2) = ![1, 0, 0] i)
    (hY : ∀ i, ((Y i : ℤ) : ZMod 2) = ![1, 0, 0] i)
    (hZ : ∀ i, ((Z i : ℤ) : ZMod 2) = ![0, 1, 0] i)
    (hW : ∀ i, ((W i : ℤ) : ZMod 2) = ![1, 1, 0] i) :
    (∀ i j, ((ofCols X W (ofCols ![1, 0, 0] ![0, 0, 1] ![-1, -1, -1] *ᵥ
        (ofCols Y Z (ofCols ![1, 0, 0] ![0, 0, 1] ![-1, -1, -1] *ᵥ W) *ᵥ W)) i j : ℤ) :
          ZMod 2) = barUv i j) ∧
    (∀ i j, ((ofCols Y Z (ofCols ![1, 0, 0] ![0, 0, 1] ![-1, -1, -1] *ᵥ W) i j : ℤ) :
      ZMod 2) = barT i j) := by
  have hX0 := hX 0; have hX1 := hX 1; have hX2 := hX 2
  have hY0 := hY 0; have hY1 := hY 1; have hY2 := hY 2
  have hZ0 := hZ 0; have hZ1 := hZ 1; have hZ2 := hZ 2
  have hW0 := hW 0; have hW1 := hW 1; have hW2 := hW 2
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hX0 hX1 hX2 hY0 hY1 hY2 hZ0 hZ1 hZ2 hW0 hW1 hW2
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp only [ofCols_apply, rhoTwo_mulVec, ofCols_mulVec_apply, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, barUv, barT,
      Matrix.of_apply] <;>
    push_cast <;>
    simp only [hX0, hX1, hX2, hY0, hY1, hY2, hZ0, hZ1, hZ2, hW0, hW1, hW2] <;>
    decide

theorem bar_u_of_uMat {cu : Fin 3 → ℤ} {κ : ℤ}
    (hcu : ∀ i, ((cu i : ℤ) : ZMod 2) = ![1, 0, 0] i) (hκ : ((κ : ℤ) : ZMod 2) = 0) :
    ∀ i j, ((uMat cu κ i j : ℤ) : ZMod 2) = barU i j := by
  have h0 := hcu 0; have h1 := hcu 1; have h2 := hcu 2
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [uMat, ofCols_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, barU, Matrix.of_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;>
    push_cast <;>
    simp only [h0, h1, h2, hκ] <;>
    decide

theorem bar_rhoTwo :
    ∀ i j, ((ofCols ![1, 0, 0] ![0, 0, 1] ![-1, -1, -1] i j : ℤ) : ZMod 2) = barRho i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem bar_t200 (m : ℕ) :
    (∀ i j, (((StrothTypeIndex.t200 m).action.uv i j : ℤ) : ZMod 2) = barUv i j) ∧
    (∀ i j, (((StrothTypeIndex.t200 m).action.t i j : ℤ) : ZMod 2) = barT i j) ∧
    (∀ i j, (((StrothTypeIndex.t200 m).action.u i j : ℤ) : ZMod 2) = barU i j) ∧
    (∀ i j, (((StrothTypeIndex.t200 m).action.ρ i j : ℤ) : ZMod 2) = barRho i j) := by
  have h := bar_uv_t_of_cols (X := ![-3, -4, -4]) (Y := ![1, 4, 0]) (Z := ![0, -1, 0])
    (W := ![1, 1, 2]) (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
  exact ⟨h.1, h.2, bar_u_of_uMat (by intro i; fin_cases i <;> decide) (by decide), bar_rhoTwo⟩

theorem bar_t201 (m : ℕ) :
    (∀ i j, (((StrothTypeIndex.t201 m).action.uv i j : ℤ) : ZMod 2) = barUv i j) ∧
    (∀ i j, (((StrothTypeIndex.t201 m).action.t i j : ℤ) : ZMod 2) = barT i j) ∧
    (∀ i j, (((StrothTypeIndex.t201 m).action.u i j : ℤ) : ZMod 2) = barU i j) ∧
    (∀ i j, (((StrothTypeIndex.t201 m).action.ρ i j : ℤ) : ZMod 2) = barRho i j) := by
  have hp : (((2 : ℤ) ^ (m + 1) : ℤ) : ZMod 2) = 0 := by
    push_cast; rw [pow_succ, show (2 : ZMod 2) = 0 by decide, mul_zero]
  have h := bar_uv_t_of_cols (X := ![-3, -4, -4]) (Y := ![1, 4, 0])
    (Z := ![0, -1 + 2 ^ (m + 1), 0]) (W := ![1, 1, 2 + 2 ^ (m + 1)])
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by intro i; fin_cases i <;> simp [hp])
    (by intro i; fin_cases i <;> simp [hp]; decide)
  exact ⟨h.1, h.2, bar_u_of_uMat (by intro i; fin_cases i <;> decide) (by decide), bar_rhoTwo⟩

private theorem zmod2_two : (2 : ZMod 2) = 0 := by decide
private theorem zmod2_four : (4 : ZMod 2) = 0 := by decide
private theorem zmod2_eight : (8 : ZMod 2) = 0 := by decide

theorem iV_cast_zmod_two (s : ℕ) : ((Type120.iV (s + 4) : ℤ) : ZMod 2) = 1 := by
  rw [iV_eq_eight_GV_add_nineteen]
  push_cast
  rw [zmod2_eight, zero_mul, zero_add]
  decide

theorem FV_cast_zmod_two (s : ℕ) : ((Type120.FV (s + 4) : ℤ) : ZMod 2) = 1 := by
  rw [FV_eq_four_GV_add_nine]
  push_cast
  rw [zmod2_four, zero_mul, zero_add]
  decide

theorem bar_t210 (m : ℕ) (hm : 2 ≤ m) :
    (∀ i j, (((StrothTypeIndex.t210 m hm).action.uv i j : ℤ) : ZMod 2) = barUv i j) ∧
    (∀ i j, (((StrothTypeIndex.t210 m hm).action.t i j : ℤ) : ZMod 2) = barT i j) ∧
    (∀ i j, (((StrothTypeIndex.t210 m hm).action.u i j : ℤ) : ZMod 2) = barU i j) ∧
    (∀ i j, (((StrothTypeIndex.t210 m hm).action.ρ i j : ℤ) : ZMod 2) = barRho i j) := by
  have h := bar_uv_t_of_cols (X := ![-3, -4 + 8 * 2 ^ (m - 2), -4])
    (Y := ![1, 4, 8 * 2 ^ (m - 2)])
    (Z := ![2 * 2 ^ (m - 2), -1 - 4 * 2 ^ (m - 2), 8 * 2 ^ (m - 2)])
    (W := ![2 * 2 ^ (m - 2) + 1, 1 + 8 * 2 ^ (m - 2), 2 - 4 * 2 ^ (m - 2)])
    (by intro i; fin_cases i <;> simp [zmod2_eight] <;> decide)
    (by intro i; fin_cases i <;> simp [zmod2_four, zmod2_eight])
    (by intro i; fin_cases i <;> simp [zmod2_two, zmod2_four, zmod2_eight])
    (by intro i; fin_cases i <;> simp [zmod2_two, zmod2_four, zmod2_eight])
  exact ⟨h.1, h.2, bar_u_of_uMat (by intro i; fin_cases i <;> simp [zmod2_two])
    (by simp [zmod2_two]), bar_rhoTwo⟩

theorem bar_t211 (m : ℕ) (hm : 2 ≤ m) :
    (∀ i j, (((StrothTypeIndex.t211 m hm).action.uv i j : ℤ) : ZMod 2) = barUv i j) ∧
    (∀ i j, (((StrothTypeIndex.t211 m hm).action.t i j : ℤ) : ZMod 2) = barT i j) ∧
    (∀ i j, (((StrothTypeIndex.t211 m hm).action.u i j : ℤ) : ZMod 2) = barU i j) ∧
    (∀ i j, (((StrothTypeIndex.t211 m hm).action.ρ i j : ℤ) : ZMod 2) = barRho i j) := by
  have h := bar_uv_t_of_cols (X := ![-3, -4 + 8 * 2 ^ (m - 2), -4])
    (Y := ![1, 4, 8 * 2 ^ (m - 2)])
    (Z := ![2 * 2 ^ (m - 2), -1 + 4 * 2 ^ (m - 2), 8 * 2 ^ (m - 2)])
    (W := ![2 * 2 ^ (m - 2) + 1, 1 + 8 * 2 ^ (m - 2), 2 + 4 * 2 ^ (m - 2)])
    (by intro i; fin_cases i <;> simp [zmod2_eight] <;> decide)
    (by intro i; fin_cases i <;> simp [zmod2_four, zmod2_eight])
    (by intro i; fin_cases i <;> simp [zmod2_two, zmod2_four, zmod2_eight])
    (by intro i; fin_cases i <;> simp [zmod2_two, zmod2_four, zmod2_eight])
  exact ⟨h.1, h.2, bar_u_of_uMat (by intro i; fin_cases i <;> simp [zmod2_two])
    (by simp [zmod2_two]), bar_rhoTwo⟩

theorem bar_t220 (s : ℕ) (hs : 1 ≤ s) :
    (∀ i j, (((StrothTypeIndex.t220 s hs).action.uv i j : ℤ) : ZMod 2) = barUv i j) ∧
    (∀ i j, (((StrothTypeIndex.t220 s hs).action.t i j : ℤ) : ZMod 2) = barT i j) ∧
    (∀ i j, (((StrothTypeIndex.t220 s hs).action.u i j : ℤ) : ZMod 2) = barU i j) ∧
    (∀ i j, (((StrothTypeIndex.t220 s hs).action.ρ i j : ℤ) : ZMod 2) = barRho i j) := by
  have hi := iV_cast_zmod_two s
  have hF := FV_cast_zmod_two s
  set i := Type120.iV (s + 4)
  set F := Type120.FV (s + 4)
  set G := Type120.GV (s + 4)
  have h := bar_uv_t_of_cols (X := ![-i, 4, -4]) (Y := ![4 - i, 4, 8])
    (Z := ![2 * G * i, -7 * i, -8 * i]) (W := ![F * i, -5 * i, 2 * i])
    (by intro j; fin_cases j <;> simp [hi, zmod2_four])
    (by intro j; fin_cases j <;> simp [hi, zmod2_four, zmod2_eight])
    (by intro j; fin_cases j <;> simp [hi, zmod2_two, zmod2_eight]; decide)
    (by intro j; fin_cases j <;> simp [hi, hF, zmod2_two]; decide)
  exact ⟨h.1, h.2, bar_u_of_uMat (by intro j; fin_cases j <;> simp)
    (by simp [zmod2_two]), bar_rhoTwo⟩

theorem bar_t221 (s : ℕ) (hs : 1 ≤ s) :
    (∀ i j, (((StrothTypeIndex.t221 s hs).action.uv i j : ℤ) : ZMod 2) = barUv i j) ∧
    (∀ i j, (((StrothTypeIndex.t221 s hs).action.t i j : ℤ) : ZMod 2) = barT i j) ∧
    (∀ i j, (((StrothTypeIndex.t221 s hs).action.u i j : ℤ) : ZMod 2) = barU i j) ∧
    (∀ i j, (((StrothTypeIndex.t221 s hs).action.ρ i j : ℤ) : ZMod 2) = barRho i j) := by
  have hi := iV_cast_zmod_two s
  have hF := FV_cast_zmod_two s
  set i := Type120.iV (s + 4)
  set F := Type120.FV (s + 4)
  set G := Type120.GV (s + 4)
  have h := bar_uv_t_of_cols (X := ![-i, 4, -4]) (Y := ![4 - i, 4, 8])
    (Z := ![2 * G * i, -7 * i + 8 * 2 ^ s, -8 * i])
    (W := ![F * i, -5 * i, 2 * i + 8 * 2 ^ s])
    (by intro j; fin_cases j <;> simp [hi, zmod2_four])
    (by intro j; fin_cases j <;> simp [hi, zmod2_four, zmod2_eight])
    (by intro j; fin_cases j <;> simp [hi, zmod2_two, zmod2_eight]; decide)
    (by intro j; fin_cases j <;> simp [hi, hF, zmod2_two, zmod2_eight]; decide)
  exact ⟨h.1, h.2, bar_u_of_uMat (by intro j; fin_cases j <;> simp)
    (by simp [zmod2_two]), bar_rhoTwo⟩

theorem bar_t230 (s : ℕ) (hs : 1 ≤ s) :
    (∀ i j, (((StrothTypeIndex.t230 s hs).action.uv i j : ℤ) : ZMod 2) = barUv i j) ∧
    (∀ i j, (((StrothTypeIndex.t230 s hs).action.t i j : ℤ) : ZMod 2) = barT i j) ∧
    (∀ i j, (((StrothTypeIndex.t230 s hs).action.u i j : ℤ) : ZMod 2) = barU i j) ∧
    (∀ i j, (((StrothTypeIndex.t230 s hs).action.ρ i j : ℤ) : ZMod 2) = barRho i j) := by
  have hi := iV_cast_zmod_two s
  have hF := FV_cast_zmod_two s
  set i := Type120.iV (s + 4)
  set F := Type120.FV (s + 4)
  set G := Type120.GV (s + 4)
  have h := bar_uv_t_of_cols (X := ![-i, 4 + 8 * 2 ^ s, -4]) (Y := ![4 - i, 4, 8 + 8 * 2 ^ s])
    (Z := ![2 * 2 ^ s + 2 * G * i, -7 * i - 4 * 2 ^ s, -8 * i + 8 * 2 ^ s])
    (W := ![2 * 2 ^ s + F * i, -5 * i + 8 * 2 ^ s, 2 * i - 4 * 2 ^ s])
    (by intro j; fin_cases j <;> simp [hi, zmod2_four, zmod2_eight])
    (by intro j; fin_cases j <;> simp [hi, zmod2_four, zmod2_eight])
    (by intro j; fin_cases j <;> simp [hi, zmod2_two, zmod2_four, zmod2_eight]; decide)
    (by intro j; fin_cases j <;> simp [hi, hF, zmod2_two, zmod2_four, zmod2_eight]; decide)
  exact ⟨h.1, h.2, bar_u_of_uMat (by intro j; fin_cases j <;> simp [zmod2_two])
    (by simp [zmod2_two]), bar_rhoTwo⟩

theorem bar_t231 (s : ℕ) (hs : 1 ≤ s) :
    (∀ i j, (((StrothTypeIndex.t231 s hs).action.uv i j : ℤ) : ZMod 2) = barUv i j) ∧
    (∀ i j, (((StrothTypeIndex.t231 s hs).action.t i j : ℤ) : ZMod 2) = barT i j) ∧
    (∀ i j, (((StrothTypeIndex.t231 s hs).action.u i j : ℤ) : ZMod 2) = barU i j) ∧
    (∀ i j, (((StrothTypeIndex.t231 s hs).action.ρ i j : ℤ) : ZMod 2) = barRho i j) := by
  have hi := iV_cast_zmod_two s
  have hF := FV_cast_zmod_two s
  set i := Type120.iV (s + 4)
  set F := Type120.FV (s + 4)
  set G := Type120.GV (s + 4)
  have h := bar_uv_t_of_cols (X := ![-i, 4 + 8 * 2 ^ s, -4]) (Y := ![4 - i, 4, 8 + 8 * 2 ^ s])
    (Z := ![2 * 2 ^ s + 2 * G * i, -7 * i + 4 * 2 ^ s, -8 * i + 8 * 2 ^ s])
    (W := ![2 * 2 ^ s + F * i, -5 * i + 8 * 2 ^ s, 2 * i + 4 * 2 ^ s])
    (by intro j; fin_cases j <;> simp [hi, zmod2_four, zmod2_eight])
    (by intro j; fin_cases j <;> simp [hi, zmod2_four, zmod2_eight])
    (by intro j; fin_cases j <;> simp [hi, zmod2_two, zmod2_four, zmod2_eight]; decide)
    (by intro j; fin_cases j <;> simp [hi, hF, zmod2_two, zmod2_four, zmod2_eight]; decide)
  exact ⟨h.1, h.2, bar_u_of_uMat (by intro j; fin_cases j <;> simp [zmod2_two])
    (by simp [zmod2_two]), bar_rhoTwo⟩

theorem familyTwo_bar {τ : StrothTypeIndex} (hfam : τ.m + 2 = τ.n) :
    (∀ i j, ((τ.action.uv i j : ℤ) : ZMod 2) = barUv i j) ∧
    (∀ i j, ((τ.action.t i j : ℤ) : ZMod 2) = barT i j) ∧
    (∀ i j, ((τ.action.u i j : ℤ) : ZMod 2) = barU i j) ∧
    (∀ i j, ((τ.action.ρ i j : ℤ) : ZMod 2) = barRho i j) := by
  cases τ with
  | t200 m => exact bar_t200 m
  | t201 m => exact bar_t201 m
  | t210 m hm => exact bar_t210 m hm
  | t211 m hm => exact bar_t211 m hm
  | t220 s hs => exact bar_t220 s hs
  | t221 s hs => exact bar_t221 s hs
  | t230 s hs => exact bar_t230 s hs
  | t231 s hs => exact bar_t231 s hs
  | t100 m =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type100.k] at hfam
  | t101 s =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type101.k] at hfam
  | t110 t =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type110.k] at hfam
  | t111 t =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type111.k] at hfam
  | t120 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type120.k] at hfam
  | t121 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type121.k] at hfam
  | t130 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type130.k] at hfam
  | t131 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type131.k] at hfam
  | t300 n =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type300.k] at hfam
  | t310 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type310.k] at hfam
  | t320 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type320.k, Type32x.k] at hfam
  | t330 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type330.k, Type32x.k] at hfam
  | t321 =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type321.k] at hfam
  | t331 =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type331.k] at hfam

theorem familyTwo_eight {τ : StrothTypeIndex} (hfam : τ.m + 2 = τ.n) :
    (8 : ℤ) ∣ τ.action.uv 1 0 - 4 ∧ (8 : ℤ) ∣ τ.action.uv 2 0 - 4 ∧
    (8 : ℤ) ∣ τ.action.t 1 0 - 4 ∧ (8 : ℤ) ∣ τ.action.t 2 0 ∧
    (8 : ℤ) ∣ τ.action.u 1 0 ∧ (8 : ℤ) ∣ τ.action.u 2 0 ∧
    (8 : ℤ) ∣ τ.action.ρ 1 0 ∧ (8 : ℤ) ∣ τ.action.ρ 2 0 := by
  cases τ with
  | t200 m =>
    refine ⟨⟨-1, ?_⟩, ⟨-1, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;> rfl
  | t201 m =>
    refine ⟨⟨-1, ?_⟩, ⟨-1, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;> rfl
  | t210 m hm =>
    refine ⟨⟨-1 + 2 ^ (m - 2), ?_⟩, ⟨-1, ?_⟩, ⟨0, ?_⟩, ⟨2 ^ (m - 2), ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩,
      ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;>
      simp [StrothTypeIndex.action, Type210.action, SigmaFourAction.ofMatEq, Type210.uvM,
        Type210.tM, Type210.uM, Type210.ρM, uMat, ofCols_apply]
    ring
  | t211 m hm =>
    refine ⟨⟨-1 + 2 ^ (m - 2), ?_⟩, ⟨-1, ?_⟩, ⟨0, ?_⟩, ⟨2 ^ (m - 2), ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩,
      ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;>
      simp [StrothTypeIndex.action, Type211.action, SigmaFourAction.ofMatEq, Type211.uvM,
        Type211.tM, Type211.uM, Type211.ρM, uMat, ofCols_apply]
    ring
  | t220 s hs =>
    refine ⟨⟨0, ?_⟩, ⟨-1, ?_⟩, ⟨0, ?_⟩, ⟨1, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;>
      simp [StrothTypeIndex.action, Type220.actionPaper, Type220.action,
        SigmaFourAction.ofMatEq, Type220.uvM, Type220.tM, Type220.uM, Type220.ρM, uMat,
        ofCols_apply]
  | t221 s hs =>
    refine ⟨⟨0, ?_⟩, ⟨-1, ?_⟩, ⟨0, ?_⟩, ⟨1, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;>
      simp [StrothTypeIndex.action, Type221.actionPaper, Type221.action,
        SigmaFourAction.ofMatEq, Type221.uvM, Type221.tM, Type221.uM, Type221.ρM, uMat,
        ofCols_apply]
  | t230 s hs =>
    refine ⟨⟨2 ^ s, ?_⟩, ⟨-1, ?_⟩, ⟨0, ?_⟩, ⟨1 + 2 ^ s, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩,
      ⟨0, ?_⟩⟩ <;>
      simp [StrothTypeIndex.action, Type230.actionPaper, Type230.action,
        SigmaFourAction.ofMatEq, Type230.uvM, Type230.tM, Type230.uM, Type230.ρM, uMat,
        ofCols_apply]
    ring
  | t231 s hs =>
    refine ⟨⟨2 ^ s, ?_⟩, ⟨-1, ?_⟩, ⟨0, ?_⟩, ⟨1 + 2 ^ s, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩,
      ⟨0, ?_⟩⟩ <;>
      simp [StrothTypeIndex.action, Type231.actionPaper, Type231.action,
        SigmaFourAction.ofMatEq, Type231.uvM, Type231.tM, Type231.uM, Type231.ρM, uMat,
        ofCols_apply]
    ring
  | t100 m =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type100.k] at hfam
  | t101 s =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type101.k] at hfam
  | t110 t =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type110.k] at hfam
  | t111 t =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type111.k] at hfam
  | t120 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type120.k] at hfam
  | t121 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type121.k] at hfam
  | t130 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type130.k] at hfam
  | t131 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type131.k] at hfam
  | t300 n =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type300.k] at hfam
  | t310 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type310.k] at hfam
  | t320 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type320.k, Type32x.k] at hfam
  | t330 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type330.k, Type32x.k] at hfam
  | t321 =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type321.k] at hfam
  | t331 =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type331.k] at hfam

theorem familyTwo_k {τ : StrothTypeIndex} (hfam : τ.m + 2 = τ.n) :
    τ.k = ![τ.m, τ.m + 2, τ.m + 2] := by
  rw [τ.k_eq, hfam]

theorem familyTwo_torusBar {τ : StrothTypeIndex} (hfam : τ.m + 2 = τ.n)
    (hk : ∀ i, 1 ≤ τ.k i) (v : Torus τ.k) :
    torusBar τ.k hk (τ.action.φuv v) = barUv *ᵥ torusBar τ.k hk v ∧
    torusBar τ.k hk (τ.action.φt v) = barT *ᵥ torusBar τ.k hk v ∧
    torusBar τ.k hk (τ.action.φu v) = barU *ᵥ torusBar τ.k hk v ∧
    torusBar τ.k hk (τ.action.φρ v) = barRho *ᵥ torusBar τ.k hk v := by
  obtain ⟨huv, ht, hu, hρ⟩ := familyTwo_bar hfam
  exact ⟨torusBar_matAct _ hk _ _ _ huv v, torusBar_matAct _ hk _ _ _ ht v,
    torusBar_matAct _ hk _ _ _ hu v, torusBar_matAct _ hk _ _ _ hρ v⟩

theorem familyTwo_torusHalf {τ : StrothTypeIndex} (hfam : τ.m + 2 = τ.n) (hm : 1 ≤ τ.m)
    (ε : Fin 3 → ZMod 2) :
    τ.action.φuv (torusHalf τ.k ε) = torusHalf τ.k (topUv *ᵥ ε) ∧
    τ.action.φt (torusHalf τ.k ε) = torusHalf τ.k (topT *ᵥ ε) ∧
    τ.action.φu (torusHalf τ.k ε) = torusHalf τ.k (topU *ᵥ ε) ∧
    τ.action.φρ (torusHalf τ.k ε) = torusHalf τ.k (topRho *ᵥ ε) := by
  obtain ⟨huv, ht, hu, hρ⟩ := familyTwo_bar hfam
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := familyTwo_eight hfam
  have hk := familyTwo_k hfam
  have v1 : (1 : ZMod 2).val = 1 := rfl
  have v0 : (0 : ZMod 2).val = 0 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine matAct_torusHalf_familyTwo hk hm _ _ topUv ((huv 0 0).trans (by decide)) (by decide)
      (by decide) ?_ ((huv 1 1).trans (by decide)) ((huv 1 2).trans (by decide)) ?_
      ((huv 2 1).trans (by decide)) ((huv 2 2).trans (by decide)) ε
    · rw [show topUv 1 0 = 1 by decide, v1]; simpa using e1
    · rw [show topUv 2 0 = 1 by decide, v1]; simpa using e2
  · refine matAct_torusHalf_familyTwo hk hm _ _ topT ((ht 0 0).trans (by decide)) (by decide)
      (by decide) ?_ ((ht 1 1).trans (by decide)) ((ht 1 2).trans (by decide)) ?_
      ((ht 2 1).trans (by decide)) ((ht 2 2).trans (by decide)) ε
    · rw [show topT 1 0 = 1 by decide, v1]; simpa using e3
    · rw [show topT 2 0 = 0 by decide, v0]; simpa using e4
  · refine matAct_torusHalf_familyTwo hk hm _ _ topU ((hu 0 0).trans (by decide)) (by decide)
      (by decide) ?_ ((hu 1 1).trans (by decide)) ((hu 1 2).trans (by decide)) ?_
      ((hu 2 1).trans (by decide)) ((hu 2 2).trans (by decide)) ε
    · rw [show topU 1 0 = 0 by decide, v0]; simpa using e5
    · rw [show topU 2 0 = 0 by decide, v0]; simpa using e6
  · refine matAct_torusHalf_familyTwo hk hm _ _ topRho ((hρ 0 0).trans (by decide))
      (by decide) (by decide) ?_ ((hρ 1 1).trans (by decide)) ((hρ 1 2).trans (by decide)) ?_
      ((hρ 2 1).trans (by decide)) ((hρ 2 2).trans (by decide)) ε
    · rw [show topRho 1 0 = 0 by decide, v0]; simpa using e7
    · rw [show topRho 2 0 = 0 by decide, v0]; simpa using e8

end Stroth225Frame

end CFSG.CGT.Stroth77
