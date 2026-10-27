module

public import Certificates.Data.G23RecogTriInputs
public import CFSG.GH74.QTGen4.Recog.G23.Abstract

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.GH74.QTGen4.Recog.G23

@[expose] def flipLetters {X : Type*} [Group X] {m : ℕ} (f : Fin m → Bool) (ρ : Fin m → X) :
    Fin m → X :=
  fun i => if f i then (ρ i)⁻¹ else ρ i

@[expose] def modelFlip : Fin 6 × Fin 6 → Fin 6 → Bool
  | (1, 1) => ![false, false, false, false, false, true]
  | (2, 3) => ![false, false, true, true, false, false]
  | (3, 2) => ![true, true, false, false, false, false]
  | _ => ![false, false, false, false, false, false]

theorem vertexPart_model : ∀ p ∈ modelPairs,
    vertexPart p.1 p.2 = (vertexPart 0 0).map (flipWord (modelFlip p)) := by
  decide +kernel


theorem lift_mk_mapWord {X : Type*} [Group X] {m n : ℕ} (g : Fin m → Fin n) (f : Fin n → X)
    (r : List (Fin m × Bool)) :
    FreeGroup.lift f (FreeGroup.mk (mapWord g r)) = FreeGroup.lift (f ∘ g) (FreeGroup.mk r) := by
  induction r with
  | nil => simp [mapWord]
  | cons l r ih =>
    have h1 : mapWord g (l :: r) = mapWord g [l] ++ mapWord g r := by simp [mapWord]
    have h2 : (l :: r) = [l] ++ r := rfl
    rw [h1, ← FreeGroup.mul_mk, map_mul, ih, h2, ← FreeGroup.mul_mk, map_mul]
    congr 1

theorem lift_mk_flipWord {X : Type*} [Group X] {m : ℕ} (φ : Fin m → Bool) (ρ : Fin m → X)
    (r : List (Fin m × Bool)) :
    FreeGroup.lift ρ (FreeGroup.mk (flipWord φ r)) =
      FreeGroup.lift (flipLetters φ ρ) (FreeGroup.mk r) := by
  induction r with
  | nil => simp [flipWord]
  | cons l r ih =>
    have h1 : flipWord φ (l :: r) = flipWord φ [l] ++ flipWord φ r := by simp [flipWord]
    have h2 : (l :: r) = [l] ++ r := rfl
    rw [h1, ← FreeGroup.mul_mk, map_mul, ih, h2, ← FreeGroup.mul_mk, map_mul]
    congr 1
    obtain ⟨i, b⟩ := l
    simp only [flipWord, List.map_cons, List.map_nil]
    rw [lift_mk_single, lift_mk_single]
    cases b <;> cases hφ : φ i <;> simp [flipLetters, hφ]

end CFSG.GH74.QTGen4.Recog.G23.P7
