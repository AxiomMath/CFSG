module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlShape

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped Matrix
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG modelToG_mono modelToG_map_conj)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_anti)

section Swap

variable {n : ℕ}

@[expose] def oddSwap (x : Fin n ⊕ Fin n) : Fin n ⊕ Fin n :=
  if (Sum.elim (fun i : Fin n => i.val) (fun i : Fin n => i.val) x) % 2 = 1 then par x else x

theorem oddSwap_inl (i : Fin n) :
    oddSwap (Sum.inl i) = if i.val % 2 = 1 then Sum.inr i else Sum.inl i := rfl

theorem oddSwap_inr (i : Fin n) :
    oddSwap (Sum.inr i) = if i.val % 2 = 1 then Sum.inl i else Sum.inr i := rfl

theorem oddSwap_oddSwap (x : Fin n ⊕ Fin n) : oddSwap (oddSwap x) = x := by
  rcases x with i | i <;> by_cases h : i.val % 2 = 1 <;>
    simp [oddSwap_inl, oddSwap_inr, h]

theorem oddSwap_injective : Function.Injective (oddSwap : Fin n ⊕ Fin n → Fin n ⊕ Fin n) :=
  fun a b h => by rw [← oddSwap_oddSwap a, h, oddSwap_oddSwap]

theorem oddSwap_par (x : Fin n ⊕ Fin n) : oddSwap (par x) = par (oddSwap x) := by
  rcases x with i | i <;> by_cases h : i.val % 2 = 1 <;>
    simp [oddSwap_inl, oddSwap_inr, h]

end Swap

section SwapMat

variable {K : Type} [Field K] {n : ℕ}

variable (K n) in
@[expose] def oddSwapMat : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.of fun a b => if a = oddSwap b then 1 else 0

theorem sgn_eq_one_of_charTwo [CharP K 2] (a : Fin n ⊕ Fin n) : sgn K a = 1 := by
  rcases a with i | i
  · rfl
  · rw [sgn_inr, CharTwo.neg_eq]

theorem oddSwapMat_symplectic [CharP K 2] :
    (oddSwapMat K n)ᵀ * CFSG.ClassicalInvolution.Models.SymplecticPairs.gram K n * oddSwapMat K n =
      CFSG.ClassicalInvolution.Models.SymplecticPairs.gram K n := by
  ext a b
  rw [transpose_mul_gram_mul_apply, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply,
    Finset.sum_eq_single (oddSwap a)]
  · simp only [oddSwapMat, Matrix.of_apply, ite_true, one_mul, sgn_eq_one_of_charTwo, ← oddSwap_par]
    by_cases hb : b = par a
    · rw [ite_eq_left (by rw [hb]), ite_eq_left hb]
    · rw [ite_eq_right (fun h => hb (oddSwap_injective h).symm), ite_eq_right hb]
  · intro c _ hc
    simp [oddSwapMat, hc]
  · simp

variable (K n) in
@[expose] noncomputable def oddSwapSp [CharP K 2] : StatedSp n K :=
  ofSymplecticMat (oddSwapMat K n) oddSwapMat_symplectic

@[expose] def oddCoordInv (t : Fin n → Kˣ) : Fin n → Kˣ :=
  fun k => if k.val % 2 = 1 then (t k)⁻¹ else t k

theorem oddSwapSp_mul_diagSp [CharP K 2] (t : Fin n → Kˣ) :
    oddSwapSp K n * diagSp K n t = diagSp K n (oddCoordInv t) * oddSwapSp K n := by
  apply mat_injective
  rw [map_mul, map_mul, oddSwapSp, mat_ofSymplecticMat, mat_diagSp, mat_diagSp]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [oddSwapMat, Matrix.of_apply]
  by_cases hab : a = oddSwap b
  · subst hab
    rw [ite_eq_left rfl, one_mul, mul_one]
    rcases b with i | i <;> by_cases h : i.val % 2 = 1 <;>
      simp [oddSwap_inl, oddSwap_inr, h, oddCoordInv, diagSpEntry]
  · rw [ite_eq_right hab, zero_mul, mul_zero]

theorem map_conj_oddSwapSp_siegelTorus_le [CharP K 2] (j : ℕ) :
    (siegelTorus K n).map (MulAut.conj (oddSwapSp K n)).toMonoidHom ≤ spATorus K n j := by
  rintro _ ⟨x, ⟨s, rfl⟩, rfl⟩
  refine ⟨oddCoordInv (fun _ => s), fun a b h1 h2 h3 h4 => ?_, ?_⟩
  · have hab : a.val % 2 ≠ b.val % 2 := by
      intro h
      apply h2
      exact Fin.ext (by omega)
    simp only [oddCoordInv]
    by_cases ha : a.val % 2 = 1
    · rw [ite_eq_left ha, ite_eq_right (by omega), inv_mul_cancel]
    · rw [ite_eq_right ha, ite_eq_left (by omega), mul_inv_cancel]
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.coe_comp,
      Function.comp_apply]
    rw [oddSwapSp_mul_diagSp, mul_inv_cancel_right]
    rfl

end SwapMat

end CFSG.SeitzReduction.SymplecticPilot
