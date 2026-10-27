module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Models2

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

namespace UT3

variable {F : Type*} [CommRing F]

theorem comm_central (u v w : UT3 F) : ⁅u, v⁆ * w = w * ⁅u, v⁆ := by
  rw [commutator_eq]
  ext
  · simp
  · simp
  · simp; ring

theorem card_eq [Finite F] : Nat.card (UT3 F) = Nat.card F ^ 3 := by
  have e : UT3 F ≃ F × F × F :=
    { toFun := fun u => (u.a, u.b, u.c)
      invFun := fun p => ⟨p.1, p.2.1, p.2.2⟩
      left_inv := fun u => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod]
  ring

theorem central_ab [Nontrivial F] (z : UT3 F) (hz : ∀ w : UT3 F, z * w = w * z) :
    z.a = 0 ∧ z.b = 0 := by
  have h1 := hz ⟨1, 0, 0⟩
  have h2 := hz ⟨0, 1, 0⟩
  have e1 := congrArg UT3.c h1
  have e2 := congrArg UT3.c h2
  simp at e1 e2
  exact ⟨e2, e1⟩

end UT3

theorem UT3_gf4_central_card (Z : Subgroup (UT3 (GaloisField 2 2)))
    (hZ : ∀ z ∈ Z, ∀ w : UT3 (GaloisField 2 2), z * w = w * z) : Nat.card Z ≤ 4 := by
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    have := GaloisField.card 2 2 (by norm_num)
    simpa using this
  rw [← hK]
  refine Nat.card_le_card_of_injective (fun z : Z => z.1.c) ?_
  intro z z' h
  apply Subtype.ext
  obtain ⟨ha, hb⟩ := UT3.central_ab z.1 (hZ z.1 z.2)
  obtain ⟨ha', hb'⟩ := UT3.central_ab z'.1 (hZ z'.1 z'.2)
  ext
  · rw [ha, ha']
  · rw [hb, hb']
  · exact h

end CFSG.GH74.GLS.Stage1.Thm6.Sec13

