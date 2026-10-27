module

public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoM12A
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.M12

open CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.ClassicalInvolution
open CFSG.ClassicalInvolution.Q3.TL4.MF163 CFSG.ComponentClassification.M12Cover

section Beta


theorem beta_getD (k : ℕ) (x : NativeSporadic.M12)
    (hx : (x : Equiv.Perm (Fin 12)) = [m12gA, m12gB].getD k 1) :
    (beta x : Equiv.Perm (Fin 12)) = [m12gA, m12bp].getD k 1 := by
  rcases k with _ | _ | k
  · obtain rfl : x = m12a := Subtype.ext hx
    rw [beta_m12a]
    rfl
  · obtain rfl : x = m12b := Subtype.ext hx
    exact beta_m12b
  · obtain rfl : x = 1 := Subtype.ext (by simpa using hx)
    simp

theorem beta_evalCodes (w : List ℤ) (x : NativeSporadic.M12)
    (hx : (x : Equiv.Perm (Fin 12)) = evalCodes [m12gA, m12gB] w) :
    (beta x : Equiv.Perm (Fin 12)) = evalCodes [m12gA, m12bp] w := by
  induction w generalizing x with
  | nil =>
    obtain rfl : x = 1 := Subtype.ext hx
    simp [evalCodes]
  | cons z w ih =>
    let y : NativeSporadic.M12 := ⟨evalCodes [m12gA, m12gB] w, evalCodes_mem _ gens_mem w⟩
    let l : NativeSporadic.M12 := x * y⁻¹
    have hyv : (y : Equiv.Perm (Fin 12)) = evalCodes [m12gA, m12gB] w := rfl
    have hxl : x = l * y := (inv_mul_cancel_right x y).symm
    have hlv : (l : Equiv.Perm (Fin 12)) = if 0 < z then [m12gA, m12gB].getD (z.toNat - 1) 1
        else ([m12gA, m12gB].getD ((-z).toNat - 1) 1)⁻¹ := by
      show ((x * y⁻¹ : NativeSporadic.M12) : Equiv.Perm (Fin 12)) = _
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hx, hyv, evalCodes, mul_inv_cancel_right]
    rw [hxl, map_mul, Subgroup.coe_mul, ih y hyv, evalCodes]
    congr 1
    split_ifs at hlv ⊢
    · exact beta_getD _ l hlv
    · have h1 := beta_getD ((-z).toNat - 1) l⁻¹ (by rw [Subgroup.coe_inv, hlv, inv_inv])
      rw [← h1, map_inv, Subgroup.coe_inv, inv_inv]


theorem qL_beta {b : Bool} {x : NativeSporadic.M12} (hx : (x : Equiv.Perm (Fin 12)) ∈ qL b) :
    (beta x : Equiv.Perm (Fin 12)) ∈ qL (!b) := by
  have h := beta_lists
  have key : ∀ wi wj : List ℤ, (x : Equiv.Perm (Fin 12)) ∈
      q8List (evalCodes [m12gA, m12gB] wi) (evalCodes [m12gA, m12gB] wj) →
      (beta x : Equiv.Perm (Fin 12)) ∈
        q8List (evalCodes [m12gA, m12bp] wi) (evalCodes [m12gA, m12bp] wj) := by
    intro wi wj hmem
    let i : NativeSporadic.M12 := ⟨evalCodes [m12gA, m12gB] wi, evalCodes_mem _ gens_mem wi⟩
    let j : NativeSporadic.M12 := ⟨evalCodes [m12gA, m12gB] wj, evalCodes_mem _ gens_mem wj⟩
    have hq : ∀ i j : NativeSporadic.M12, q8List i j = (q8L i j).map NativeSporadic.M12.subtype :=
      fun i j => by rw [q8L_map]; rfl
    change (x : Equiv.Perm (Fin 12)) ∈ q8List i j at hmem
    rw [hq, List.mem_map] at hmem
    obtain ⟨x', hx', hxx⟩ := hmem
    obtain rfl : x' = x := Subtype.ext hxx
    have h1 := List.mem_map_of_mem (f := NativeSporadic.M12.subtype)
      (mem_q8L_map (beta : NativeSporadic.M12 ≃* NativeSporadic.M12).toMonoidHom hx')
    rwa [← hq, MulEquiv.coe_toMonoidHom, beta_evalCodes wi i rfl, beta_evalCodes wj j rfl] at h1
  cases b
  · exact h.1 _ (key wI0 wJ0 hx)
  · exact h.2 _ (key wI1 wJ1 hx)

end Beta

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.M12
