module

public import CFSG.ClassicalInvolution.Q3.AE.Wreath
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

@[expose] def vec4 (s : List (Fin 4)) : Fin 4 → ZMod 2 := fun i => if i ∈ s then 1 else 0

@[expose] def d₁ : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def d₂ : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

@[expose] def d₃ : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 1 2

@[expose] def zQ : Wr 4 := ⟨vec4 [0, 1, 2, 3], 1⟩

@[expose] def kList : List (Wr 4) :=
  [1, zQ, ⟨vec4 [0, 2], d₁⟩, ⟨vec4 [1, 3], d₁⟩, ⟨vec4 [0, 3], d₂⟩, ⟨vec4 [1, 2], d₂⟩,
    ⟨vec4 [0, 1], d₃⟩, ⟨vec4 [2, 3], d₃⟩]

@[expose] def kStarList : List (Wr 4) :=
  [1, zQ, ⟨vec4 [0, 3], d₁⟩, ⟨vec4 [1, 2], d₁⟩, ⟨vec4 [0, 1], d₂⟩, ⟨vec4 [2, 3], d₂⟩,
    ⟨vec4 [0, 2], d₃⟩, ⟨vec4 [1, 3], d₃⟩]

theorem kList_mul : ∀ a ∈ kList, ∀ b ∈ kList, a * b ∈ kList := by decide +kernel

theorem kList_inv : ∀ a ∈ kList, a⁻¹ ∈ kList := by decide +kernel

theorem kStarList_mul : ∀ a ∈ kStarList, ∀ b ∈ kStarList, a * b ∈ kStarList := by
  decide +kernel

theorem kStarList_inv : ∀ a ∈ kStarList, a⁻¹ ∈ kStarList := by decide +kernel

@[expose] def kQ : Subgroup (Wr 4) where
  carrier := {a | a ∈ kList}
  mul_mem' {a b} ha hb := kList_mul a ha b hb
  one_mem' := by show (1 : Wr 4) ∈ kList; decide +kernel
  inv_mem' {a} ha := kList_inv a ha

@[expose] def kQStar : Subgroup (Wr 4) where
  carrier := {a | a ∈ kStarList}
  mul_mem' {a b} ha hb := kStarList_mul a ha b hb
  one_mem' := by show (1 : Wr 4) ∈ kStarList; decide +kernel
  inv_mem' {a} ha := kStarList_inv a ha

theorem mem_kQ {a : Wr 4} : a ∈ kQ ↔ a ∈ kList := Iff.rfl

theorem mem_kQStar {a : Wr 4} : a ∈ kQStar ↔ a ∈ kStarList := Iff.rfl

theorem comm_kQ_kQStar : ∀ a ∈ kQ, ∀ b ∈ kQStar, a * b = b * a :=
  (by decide +kernel : ∀ a ∈ kList, ∀ b ∈ kStarList, a * b = b * a)

theorem inf_kQ_kQStar : ∀ a ∈ kQ, a ∈ kQStar → a = 1 ∨ a = zQ :=
  (by decide +kernel : ∀ a ∈ kList, a ∈ kStarList → a = 1 ∨ a = zQ)

theorem zQ_mem_kQ : zQ ∈ kQ := (by decide +kernel : zQ ∈ kList)

theorem zQ_mem_kQStar : zQ ∈ kQStar := (by decide +kernel : zQ ∈ kStarList)

theorem eq_of_mem_kQ_mul_self : ∀ a ∈ kQ, a * a = 1 → a = 1 ∨ a = zQ :=
  (by decide +kernel : ∀ a ∈ kList, a * a = 1 → a = 1 ∨ a = zQ)

theorem eq_of_mem_kQStar_mul_self : ∀ a ∈ kQStar, a * a = 1 → a = 1 ∨ a = zQ :=
  (by decide +kernel : ∀ a ∈ kStarList, a * a = 1 → a = 1 ∨ a = zQ)

@[expose] def yQ : Wr 4 := ⟨0, Equiv.swap 0 1 * Equiv.swap 1 2⟩

theorem yQ_pow_three : yQ * yQ * yQ = 1 := by decide +kernel

theorem yQ_comm_zQ : yQ * zQ = zQ * yQ := by decide +kernel

theorem yQ_conj_mem_kQ : ∀ a ∈ kQ, yQ * a * yQ⁻¹ ∈ kQ :=
  (by decide +kernel : ∀ a ∈ kList, yQ * a * yQ⁻¹ ∈ kList)

theorem yQ_conj_mem_kQStar : ∀ a ∈ kQStar, yQ * a * yQ⁻¹ ∈ kQStar :=
  (by decide +kernel : ∀ a ∈ kStarList, yQ * a * yQ⁻¹ ∈ kStarList)

theorem yQ_not_comm_kQ : ∃ a ∈ kQ, yQ * a ≠ a * yQ :=
  ⟨⟨vec4 [0, 2], d₁⟩, (by decide +kernel : _ ∈ kList), by decide +kernel⟩

theorem yQ_not_comm_kQStar : ∃ a ∈ kQStar, yQ * a ≠ a * yQ :=
  ⟨⟨vec4 [0, 3], d₁⟩, (by decide +kernel : _ ∈ kStarList), by decide +kernel⟩

theorem kQ_mul_vec : (∀ a ∈ kQ, ∃ b ∈ kQStar, (a⁻¹ * b).perm = 1) ∧
    (∀ b ∈ kQStar, ∃ a ∈ kQ, (b⁻¹ * a).perm = 1) := by
  exact ⟨(by decide +kernel : ∀ a ∈ kList, ∃ b ∈ kStarList, (a⁻¹ * b).perm = 1),
    (by decide +kernel : ∀ b ∈ kStarList, ∃ a ∈ kList, (b⁻¹ * a).perm = 1)⟩

@[expose] def iQ : Wr 4 := ⟨vec4 [0, 2], d₁⟩

@[expose] def jQ : Wr 4 := ⟨vec4 [0, 3], d₂⟩

@[expose] def kQHom : QuaternionGroup 2 → Wr 4 := fun q =>
  match q with
  | .a k => iQ ^ k.val
  | .xa k => jQ * iQ ^ k.val

theorem kQHom_mul : ∀ p q : QuaternionGroup 2, kQHom (p * q) = kQHom p * kQHom q := by
  decide +kernel

theorem kQHom_injective : Function.Injective kQHom := by
  intro p q h
  revert p q
  decide +kernel

theorem kQHom_mem : ∀ q : QuaternionGroup 2, kQHom q ∈ kQ :=
  (by decide +kernel : ∀ q : QuaternionGroup 2, kQHom q ∈ kList)

@[expose] def iQStar : Wr 4 := ⟨vec4 [0, 3], d₁⟩

@[expose] def jQStar : Wr 4 := ⟨vec4 [0, 1], d₂⟩

@[expose] def kQStarHom : QuaternionGroup 2 → Wr 4 := fun q =>
  match q with
  | .a k => iQStar ^ k.val
  | .xa k => jQStar * iQStar ^ k.val

theorem kQStarHom_mul : ∀ p q : QuaternionGroup 2,
    kQStarHom (p * q) = kQStarHom p * kQStarHom q := by
  decide +kernel

theorem kQStarHom_injective : Function.Injective kQStarHom := by
  intro p q h
  revert p q
  decide +kernel

theorem kQStarHom_mem : ∀ q : QuaternionGroup 2, kQStarHom q ∈ kQStar :=
  (by decide +kernel : ∀ q : QuaternionGroup 2, kQStarHom q ∈ kStarList)

theorem kQStarHom_surj : ∀ a ∈ kQStar, ∃ q : QuaternionGroup 2, kQStarHom q = a :=
  (by decide +kernel : ∀ a ∈ kStarList, ∃ q : QuaternionGroup 2, kQStarHom q = a)

theorem kQHom_surj : ∀ a ∈ kQ, ∃ q : QuaternionGroup 2, kQHom q = a :=
  (by decide +kernel : ∀ a ∈ kList, ∃ q : QuaternionGroup 2, kQHom q = a)

end CFSG.ClassicalInvolution.Q3.AE
