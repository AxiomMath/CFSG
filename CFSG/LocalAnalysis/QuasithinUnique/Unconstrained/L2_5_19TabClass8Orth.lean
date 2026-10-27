module

import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27L34GL
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabL5Aut

public section

namespace CFSG.QuasithinUnique.Id2519.Tab.L5

open Matrix

@[expose] def orthU : Matrix (Fin 4) (Fin 5) (ZMod 2) :=
  Matrix.of fun j i => if (i : ℕ) = j then 1 else 0

@[expose] def orthT : Matrix (Fin 5) (Fin 4) (ZMod 2) :=
  Matrix.of fun i j => if (i : ℕ) = 4 then 1 else if (i : ℕ) = j then 1 else 0

@[expose] def orthY : Matrix (Fin 4) (Fin 5) (ZMod 2) :=
  Matrix.of fun j i => if (i : ℕ) = j then 0 else 1

theorem orthU_mul_orthT : orthU * orthT = 1 := by decide

theorem orth_resolve :
    orthT * orthY + Matrix.vecMulVec (fun _ : Fin 5 => (1 : ZMod 2)) (fun _ => 1) = 1 := by
  decide

theorem orth_rowsum {h : M5} (hh : h * hᵀ = 1) (i : Fin 5) : ∑ j, h i j = 1 := by
  have h1 := congrFun (congrFun hh i) i
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : ∀ x : ZMod 2, x = x * x := by decide
  exact this _

theorem orth_colsum {h : M5} (hh : h * hᵀ = 1) (j : Fin 5) : ∑ i, h i j = 1 := by
  have hh' : hᵀ * h = 1 := mul_eq_one_comm.mp hh
  have h1 := congrFun (congrFun hh' j) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : ∀ x : ZMod 2, x = x * x := by decide
  exact this _

theorem orth_key {h : M5} (hcol : ∀ j, ∑ i, h i j = 1) :
    orthT * (orthU * h * orthT) = h * orthT := by
  have c0 := hcol 0
  have c1 := hcol 1
  have c2 := hcol 2
  have c3 := hcol 3
  have c4 := hcol 4
  simp only [Fin.sum_univ_five] at c0 c1 c2 c3 c4
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_four, orthT, orthU,
      Matrix.of_apply] <;>
    simp <;> grind

theorem orth_inj_aux {h : M5} (hh : h * hᵀ = 1) (hT : h * orthT = orthT) : h = 1 := by
  have hc : h *ᵥ (fun _ : Fin 5 => (1 : ZMod 2)) = fun _ => 1 := by
    funext i
    simpa [Matrix.mulVec, dotProduct] using orth_rowsum hh i
  calc h = h * (orthT * orthY +
        Matrix.vecMulVec (fun _ : Fin 5 => (1 : ZMod 2)) (fun _ => 1)) := by
        rw [orth_resolve, mul_one]
    _ = (h * orthT) * orthY +
        h * Matrix.vecMulVec (fun _ : Fin 5 => (1 : ZMod 2)) (fun _ => 1) := by
        rw [Matrix.mul_add, Matrix.mul_assoc]
    _ = orthT * orthY + Matrix.vecMulVec (fun _ : Fin 5 => (1 : ZMod 2)) (fun _ => 1) := by
        rw [hT, Matrix.mul_vecMulVec, hc]
    _ = 1 := orth_resolve

theorem orth_inj {h : M5} (hh : h * hᵀ = 1) (hA : orthU * h * orthT = 1) : h = 1 := by
  have hT0 : h * orthT = orthT := by
    have := orth_key (fun j => orth_colsum hh j)
    rw [hA, Matrix.mul_one] at this
    exact this.symm
  exact orth_inj_aux hh hT0

@[expose] noncomputable def orthHom {A : Type} [Group A] (κ : A →* S)
    (horth : ∀ a, (κ a : M5) * (κ a : M5)ᵀ = 1) : A →* GL (Fin 4) (ZMod 2) :=
  MonoidHom.toHomUnits
    { toFun := fun a => orthU * (κ a : M5) * orthT
      map_one' := by
        rw [map_one, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, orthU_mul_orthT]
      map_mul' := fun a b => by
        have key := orth_key (fun j => orth_colsum (horth b) j)
        rw [map_mul, Matrix.SpecialLinearGroup.coe_mul]
        calc orthU * ((κ a : M5) * (κ b : M5)) * orthT
            = orthU * (κ a : M5) * ((κ b : M5) * orthT) := by simp only [Matrix.mul_assoc]
          _ = orthU * (κ a : M5) * (orthT * (orthU * (κ b : M5) * orthT)) := by rw [key]
          _ = (orthU * (κ a : M5) * orthT) * (orthU * (κ b : M5) * orthT) := by
            simp only [Matrix.mul_assoc] }

theorem coe_orthHom {A : Type} [Group A] (κ : A →* S)
    (horth : ∀ a, (κ a : M5) * (κ a : M5)ᵀ = 1) (a : A) :
    ((orthHom κ horth a : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      orthU * (κ a : M5) * orthT := rfl

theorem orthHom_injective {A : Type} [Group A] (κ : A →* S) (hκ : Function.Injective κ)
    (horth : ∀ a, (κ a : M5) * (κ a : M5)ᵀ = 1) : Function.Injective (orthHom κ horth) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 : orthU * (κ a : M5) * orthT = 1 := by
    rw [← coe_orthHom κ horth a, ha]
    rfl
  have h2 : (κ a : M5) = 1 := orth_inj (horth a) h1
  apply hκ
  rw [map_one]
  exact Subtype.ext h2

theorem card_GL_four : Nat.card (GL (Fin 4) (ZMod 2)) = 20160 :=
  CFSG.OddStandard.Seitz77.card_GL_four_two

theorem orth_of_dl_fixed (h : S) (hh : dl h = h) : (h : M5) * (h : M5)ᵀ = 1 := by
  have h1 : ((h⁻¹ : S) : M5)ᵀ = (h : M5) := by
    have := congrArg (fun x : S => (x : M5)) hh
    simpa [dl_apply, Matrix.SpecialLinearGroup.coe_transpose] using this
  have h2 : ((h⁻¹ : S) : M5) = (h : M5)ᵀ := by
    rw [← h1, Matrix.transpose_transpose]
  rw [← h2, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

end CFSG.QuasithinUnique.Id2519.Tab.L5
