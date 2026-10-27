module

public import CFSG.ClassicalInvolution.Q3.AE.Group
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.ClassicalInvolution.Sp62Rec.I1

open Equiv CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open scoped commutatorElement

@[expose] def v6 (s : List (Fin 6)) : Fin 6 → ZMod 2 := fun i => if i ∈ s then 1 else 0

private theorem card_even_vectors_six :
    Nat.card {v : Fin 6 → ZMod 2 // ∑ i, v i = 0} = 32 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

@[expose] def Wsub : Subgroup (Wr 6) where
  carrier := {a | wsum a = 0}
  mul_mem' {a b} ha hb := by
    show wsum (a * b) = 0
    rw [wsum_mul, show wsum a = 0 from ha, show wsum b = 0 from hb, add_zero]
  one_mem' := wsum_one
  inv_mem' {a} ha := by
    show wsum a⁻¹ = 0
    rw [wsum_inv]
    exact ha

theorem mem_Wsub {a : Wr 6} : a ∈ Wsub ↔ wsum a = 0 := Iff.rfl

theorem aeSub_le_Wsub : aeSub 6 ≤ Wsub := fun _ ha => ha.1

theorem allOnes_mem_Wsub : allOnes 6 ∈ Wsub := by
  show wsum (allOnes 6) = 0
  decide

theorem card_Wsub : Nat.card Wsub = 23040 := by
  have h1 : Nat.card Wsub = Nat.card ({v : Fin 6 → ZMod 2 // ∑ i, v i = 0} × Perm (Fin 6)) := by
    refine Nat.card_congr
      { toFun := fun a => (⟨(a : Wr 6).vec, a.2⟩, (a : Wr 6).perm)
        invFun := fun p => ⟨⟨p.1.1, p.2⟩, p.1.2⟩
        left_inv := fun a => rfl
        right_inv := fun p => rfl }
  rw [h1, Nat.card_prod, card_even_vectors_six, Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_fin]
  decide

theorem commutator_Wsub (hperf : Group.IsPerfect ↥(aeSub 6)) : ⁅Wsub, Wsub⁆ = aeSub 6 := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    have ha' : wsum a = 0 := ha
    have hb' : wsum b = 0 := hb
    refine ⟨?_, ?_⟩
    · show wsum ⁅a, b⁆ = 0
      rw [commutatorElement_def]
      simp only [wsum_mul, wsum_inv, ha', hb', add_zero]
    · show Perm.sign ((⁅a, b⁆ : Wr 6).perm) = 1
      rw [commutatorElement_def]
      simp only [mul_perm, inv_perm, map_mul, map_inv]
      generalize Perm.sign a.perm = x
      generalize Perm.sign b.perm = y
      rcases Int.units_eq_one_or x with rfl | rfl <;>
        rcases Int.units_eq_one_or y with rfl | rfl <;> decide
  · have h1 : (commutator ↥(aeSub 6)).map (aeSub 6).subtype = ⁅aeSub 6, aeSub 6⁆ :=
      Subgroup.map_subtype_commutator _
    rw [hperf.commutator_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
    rw [h1]
    exact Subgroup.commutator_mono aeSub_le_Wsub aeSub_le_Wsub

end CFSG.ClassicalInvolution.Sp62Rec.I1
