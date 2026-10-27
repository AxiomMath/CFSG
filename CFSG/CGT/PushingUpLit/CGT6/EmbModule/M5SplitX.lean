module

public import CFSG.LieType.Multipliers.G23Bridge
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M5Split
public import Certificates.Certificate271036

public section

namespace CFSG.CGT.PushingUpLit.CGT6.EmbModule

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Sporadic.He.Native CFSG.LieType.Multipliers.G23

variable {K : Type} [Field K] (σ : K ≃+* ZMod 3)

noncomputable def eltX (w : List (Fin 4)) : adjointGroup .G2 K := (w.map (rootElt σ)).prod

theorem mat_eltX (w : List (Fin 4)) :
    ((matHom σ (eltX σ w) : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) =
      toMat 3 14 (rootProd w) :=
  val_matHom_prod σ w

theorem mat_one_X : ((matHom σ (1 : adjointGroup .G2 K) : GL (Fin 14) (ZMod 3)) :
    Matrix (Fin 14) (Fin 14) (ZMod 3)) = toMat 3 14 (idM 14) := by
  rw [map_one, Units.val_one, toMat_idM]

theorem mat_mul_X {x y : adjointGroup .G2 K} {X Y : Array (Array ℕ)}
    (hx : ((matHom σ x : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) = toMat 3 14 X)
    (hy : ((matHom σ y : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) =
      toMat 3 14 Y) :
    ((matHom σ (x * y) : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) =
      toMat 3 14 (mulM 3 14 X Y) := by
  rw [map_mul, Units.val_mul, hx, hy, toMat_mulM]

theorem eq_of_beq_X {x y : adjointGroup .G2 K} {X Y : Array (Array ℕ)}
    (hx : ((matHom σ x : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) = toMat 3 14 X)
    (hy : ((matHom σ y : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) = toMat 3 14 Y)
    (h : (X == Y) = true) : x = y :=
  matHom_injective σ (Units.ext (by rw [hx, hy]; exact toMat_eq_of_beq h))

theorem ne_one_of_entry_X {x : adjointGroup .G2 K} {X : Array (Array ℕ)} {i j : Fin 14}
    (hij : i ≠ j) (hx : ((matHom σ x : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) =
      toMat 3 14 X) (h : (entryOf X i.val j.val == 2) = true) : x ≠ 1 := by
  intro hx1
  rw [hx1, map_one, Units.val_one] at hx
  have h1 := congrFun (congrFun hx i) j
  rw [Matrix.one_apply_ne hij, toMat_apply] at h1
  rw [beq_iff_eq] at h
  have h2 : ((X[i.val]!)[j.val]! : ZMod 3) = 2 := by
    change ((entryOf X i.val j.val : ℕ) : ZMod 3) = 2
    rw [h]
    rfl
  rw [h2] at h1
  exact absurd h1.symm (by decide)

section Facts


theorem split_facts_adjoint :
    SplitCfg (eltX σ uW) (eltX σ vW) (eltX σ z0W) (eltX σ a1W) (eltX σ a2W) (eltX σ cW) := by
  have h := Certificates.certificate271036
  simp only [splitCheck, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  have hU : _ = toMat 3 14 splU := mat_eltX σ uW
  have hV : _ = toMat 3 14 splV := mat_eltX σ vW
  have hZ : _ = toMat 3 14 splZ := mat_eltX σ z0W
  have hA1 : _ = toMat 3 14 splA1 := mat_eltX σ a1W
  have hA2 : _ = toMat 3 14 splA2 := mat_eltX σ a2W
  have hC : _ = toMat 3 14 splC := mat_eltX σ cW
  have hone := mat_one_X (K := K) σ
  have cube : ∀ {x : adjointGroup .G2 K} {X : Array (Array ℕ)},
      ((matHom σ x : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) = toMat 3 14 X →
      (mulM 3 14 X (mulM 3 14 X X) == idM 14) = true → x ^ 3 = 1 := by
    intro x X hx hb
    rw [pow_three]
    exact eq_of_beq_X σ (mat_mul_X σ hx (mat_mul_X σ hx hx)) hone hb
  have comm : ∀ {x y : adjointGroup .G2 K} {X Y : Array (Array ℕ)},
      ((matHom σ x : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) = toMat 3 14 X →
      ((matHom σ y : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) = toMat 3 14 Y →
      (mulM 3 14 X Y == mulM 3 14 Y X) = true → x * y = y * x := by
    intro x y X Y hx hy hb
    exact eq_of_beq_X σ (mat_mul_X σ hx hy) (mat_mul_X σ hy hx) hb
  refine ⟨cube hA1 h1, cube hA2 h2, cube hZ h3, cube hU h4, comm hA1 hA2 h5, comm hU hA1 h6,
    comm hU hA2 h7, comm hV hA1 h8, comm hV hA2 h9, comm hZ hA1 h10, comm hZ hA2 h11,
    comm hU hZ h12, comm hV hZ h13, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [mul_assoc]
    exact eq_of_beq_X σ (mat_mul_X σ hU hV)
      (mat_mul_X σ hZ (mat_mul_X σ hV hU)) h14
  · exact eq_of_beq_X σ (mat_mul_X σ hC hA1) (mat_mul_X σ hA2 hC) h15
  · rw [mul_assoc]
    exact eq_of_beq_X σ (mat_mul_X σ hC hA2) (mat_mul_X σ hA1 (mat_mul_X σ hA2 hC)) h16
  · exact ne_one_of_entry_X σ (i := 0) (j := 5) (by decide) hA1 h17
  · exact ne_one_of_entry_X σ (i := 0) (j := 12) (by decide) hZ h18

include σ in
theorem split_bound_adjoint {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (ρ : adjointGroup .G2 K →* MulAut V) (hρ : Function.Injective ρ) : 2 ^ 14 ≤ Nat.card V :=
  split_bound hV (split_facts_adjoint σ) ρ hρ

end Facts

end CFSG.CGT.PushingUpLit.CGT6.EmbModule
