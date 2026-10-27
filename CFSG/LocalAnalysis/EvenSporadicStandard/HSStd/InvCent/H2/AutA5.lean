module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup

theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

set_option synthInstance.maxSize 4096 in
private theorem alt5_involutions_conj_aux :
    ∀ x y : alternatingGroup (Fin 5), x ≠ 1 → y ≠ 1 → x * x = 1 → y * y = 1 →
      ∃ s : alternatingGroup (Fin 5), s * x * s⁻¹ = y := by
  decide +kernel

theorem alt5_involutions_conj {x y : alternatingGroup (Fin 5)} (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hx2 : x * x = 1) (hy2 : y * y = 1) : ∃ s : alternatingGroup (Fin 5), s * x * s⁻¹ = y :=
  alt5_involutions_conj_aux x y hx1 hy1 hx2 hy2

set_option synthInstance.maxSize 4096 in
private theorem perm5_centralizer_klein :
    ∀ a b : alternatingGroup (Fin 5),
      a ≠ 1 → b ≠ 1 → a ≠ b → a * a = 1 → b * b = 1 → a * b = b * a →
      ∀ π : Equiv.Perm (Fin 5),
        π * (a : Equiv.Perm (Fin 5)) = (a : Equiv.Perm (Fin 5)) * π →
        π * (b : Equiv.Perm (Fin 5)) = (b : Equiv.Perm (Fin 5)) * π →
        π = 1 ∨ π = (a : Equiv.Perm (Fin 5)) ∨ π = (b : Equiv.Perm (Fin 5)) ∨
          π = (a : Equiv.Perm (Fin 5)) * (b : Equiv.Perm (Fin 5)) := by
  decide +kernel

theorem aut_alt5_of_fixes {a b : alternatingGroup (Fin 5)} (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hcomm : a * b = b * a)
    (σ : MulAut (alternatingGroup (Fin 5))) (hσa : σ a = a) (hσb : σ b = b) :
    ∃ x : alternatingGroup (Fin 5), (x = 1 ∨ x = a ∨ x = b ∨ x = a * b) ∧
      ∀ y : alternatingGroup (Fin 5), σ y = x * y * x⁻¹ := by
  obtain ⟨π, hπ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    (by decide) (by decide)).2 σ
  have hπa : π * (a : Equiv.Perm (Fin 5)) = (a : Equiv.Perm (Fin 5)) * π := by
    have h : MulAut.conjNormal (H := alternatingGroup (Fin 5)) π a = a := by
      rw [hπ]; exact hσa
    have h' : π * (a : Equiv.Perm (Fin 5)) * π⁻¹ = (a : Equiv.Perm (Fin 5)) := by
      simpa using congrArg (fun z : alternatingGroup (Fin 5) => (z : Equiv.Perm (Fin 5))) h
    calc π * (a : Equiv.Perm (Fin 5))
        = (π * (a : Equiv.Perm (Fin 5)) * π⁻¹) * π := by group
      _ = (a : Equiv.Perm (Fin 5)) * π := by rw [h']
  have hπb : π * (b : Equiv.Perm (Fin 5)) = (b : Equiv.Perm (Fin 5)) * π := by
    have h : MulAut.conjNormal (H := alternatingGroup (Fin 5)) π b = b := by
      rw [hπ]; exact hσb
    have h' : π * (b : Equiv.Perm (Fin 5)) * π⁻¹ = (b : Equiv.Perm (Fin 5)) := by
      simpa using congrArg (fun z : alternatingGroup (Fin 5) => (z : Equiv.Perm (Fin 5))) h
    calc π * (b : Equiv.Perm (Fin 5))
        = (π * (b : Equiv.Perm (Fin 5)) * π⁻¹) * π := by group
      _ = (b : Equiv.Perm (Fin 5)) * π := by rw [h']
  have hdisj := perm5_centralizer_klein a b ha1 hb1 hab ha2 hb2 hcomm π hπa hπb
  have hπeven : Equiv.Perm.sign π = 1 := by
    rcases hdisj with h | h | h | h
    · rw [h]; exact Equiv.Perm.sign_one
    · rw [h]; exact Equiv.Perm.mem_alternatingGroup.mp a.2
    · rw [h]; exact Equiv.Perm.mem_alternatingGroup.mp b.2
    · rw [h, map_mul, Equiv.Perm.mem_alternatingGroup.mp a.2,
        Equiv.Perm.mem_alternatingGroup.mp b.2, mul_one]
  refine ⟨⟨π, hπeven⟩, ?_, ?_⟩
  · rcases hdisj with h | h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))
  · intro y
    have hσy : σ y = MulAut.conjNormal (H := alternatingGroup (Fin 5)) π y := by rw [← hπ]
    rw [hσy]
    apply Subtype.ext
    simp [MulAut.conjNormal_apply]

end CFSG.EvenSporadicStandard.HSStd.InvCent
