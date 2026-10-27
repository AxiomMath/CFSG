module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace FixedLift

open Subgroup

theorem card_sq_eq_one_le_of_surjective {H G : Type*} [Group H] [Group G] [Finite H]
    (hH : ∀ x y : H, x * y = y * x) (f : H →* G) (hf : Function.Surjective f) :
    Nat.card {g : G // g ^ 2 = 1} ≤ Nat.card {h : H // h ^ 2 = 1} := by
  have : Finite G := Finite.of_surjective f hf
  have hG : ∀ x y : G, x * y = y * x := by
    intro x y
    obtain ⟨x, rfl⟩ := hf x
    obtain ⟨y, rfl⟩ := hf y
    rw [← map_mul, hH, map_mul]
  let sqH : H →* H :=
    { toFun := fun h => h ^ 2
      map_one' := by simp
      map_mul' := fun x y => Commute.mul_pow (hH x y) 2 }
  let sqG : G →* G :=
    { toFun := fun g => g ^ 2
      map_one' := by simp
      map_mul' := fun x y => Commute.mul_pow (hG x y) 2 }
  have hkerH : Nat.card sqH.ker = Nat.card {h : H // h ^ 2 = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => MonoidHom.mem_ker)
  have hkerG : Nat.card sqG.ker = Nat.card {g : G // g ^ 2 = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => MonoidHom.mem_ker)
  let f' : sqH.range →* G := f.comp sqH.range.subtype
  have hf'range : f'.range = sqG.range := by
    ext g
    constructor
    · rintro ⟨⟨_, h, rfl⟩, rfl⟩
      exact ⟨f h, by simp [f', sqH, sqG, map_pow]⟩
    · rintro ⟨g', rfl⟩
      obtain ⟨h, rfl⟩ := hf g'
      exact ⟨⟨sqH h, h, rfl⟩, by simp [f', sqH, sqG, map_pow]⟩
  have hf'ker : Nat.card f'.ker ≤ Nat.card f.ker :=
    Nat.card_le_card_of_injective (fun w => ⟨((w : sqH.range) : H), MonoidHom.mem_ker.mp w.2⟩)
      fun v w h => by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun x : f.ker => (x : H)) h
  have h1 : Nat.card sqH.range ≤ Nat.card f.ker * Nat.card sqG.range := by
    rw [← card_ker_mul_card_range f', hf'range]
    exact Nat.mul_le_mul_right _ hf'ker
  have h2 := card_ker_mul_card_range sqH
  have h3 := card_ker_mul_card_range sqG
  have h4 := card_ker_mul_card_range f
  rw [MonoidHom.range_eq_top.mpr hf, card_top] at h4
  rw [hkerH] at h2
  rw [hkerG] at h3
  have hpos : 0 < Nat.card sqG.range * Nat.card sqH.range :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card {g : G // g ^ 2 = 1} * (Nat.card sqG.range * Nat.card sqH.range)
      _ = Nat.card G * Nat.card sqH.range := by rw [← h3, mul_assoc]
      _ ≤ Nat.card G * (Nat.card f.ker * Nat.card sqG.range) := Nat.mul_le_mul_left _ h1
      _ = Nat.card H * Nat.card sqG.range := by rw [← h4]; ring
      _ = Nat.card {h : H // h ^ 2 = 1} * (Nat.card sqG.range * Nat.card sqH.range) := by
        rw [← h2]; ring

end FixedLift

end CFSG.LocalAnalysis.ComponentInitial
