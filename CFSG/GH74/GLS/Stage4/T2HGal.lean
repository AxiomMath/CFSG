module

public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.GH74.GLS.Stage4.Rest

theorem t2H_sl_galoisField {F : Type} [Field F] [Finite F] {n : ℕ} (hn : n ≠ 0)
    (hF : Nat.card F = 3 ^ n) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 n)) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have : Fintype (GaloisField 3 n) := Fintype.ofFinite (GaloisField 3 n)
  have hcard : Fintype.card F = Fintype.card (GaloisField 3 n) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, GaloisField.card 3 n hn]
  let e : F ≃+* GaloisField 3 n := FiniteField.ringEquivOfCardEq hcard
  refine ⟨
    { toFun := Matrix.SpecialLinearGroup.map (e : F →+* GaloisField 3 n)
      invFun := Matrix.SpecialLinearGroup.map (e.symm : GaloisField 3 n →+* F)
      left_inv := fun g => by
        apply Subtype.ext
        ext i j
        simp
      right_inv := fun g => by
        apply Subtype.ext
        ext i j
        simp
      map_mul' := fun g h => map_mul _ g h }⟩

end CFSG.GH74.GLS.Stage4.Rest
