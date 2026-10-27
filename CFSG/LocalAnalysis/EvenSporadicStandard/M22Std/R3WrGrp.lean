module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutProp21

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup

@[ext] structure Wr where
  a : Equiv.Perm (Fin 6)
  b : Equiv.Perm (Fin 6)
  e : Bool

namespace Wr

instance : Mul Wr :=
  ⟨fun x y => if x.e then ⟨x.a * y.b, x.b * y.a, !y.e⟩ else ⟨x.a * y.a, x.b * y.b, y.e⟩⟩

instance : One Wr := ⟨⟨1, 1, false⟩⟩

instance : Inv Wr :=
  ⟨fun x => if x.e then ⟨x.b⁻¹, x.a⁻¹, true⟩ else ⟨x.a⁻¹, x.b⁻¹, false⟩⟩

theorem mul_def (x y : Wr) : x * y =
    if x.e then ⟨x.a * y.b, x.b * y.a, !y.e⟩ else ⟨x.a * y.a, x.b * y.b, y.e⟩ := rfl

@[simp] theorem mul_ff (a b a' b' : Equiv.Perm (Fin 6)) (e' : Bool) :
    (⟨a, b, false⟩ : Wr) * ⟨a', b', e'⟩ = ⟨a * a', b * b', e'⟩ := rfl

@[simp] theorem mul_tt (a b a' b' : Equiv.Perm (Fin 6)) (e' : Bool) :
    (⟨a, b, true⟩ : Wr) * ⟨a', b', e'⟩ = ⟨a * b', b * a', !e'⟩ := rfl

@[simp] theorem one_def : (1 : Wr) = ⟨1, 1, false⟩ := rfl

@[simp] theorem inv_f (a b : Equiv.Perm (Fin 6)) : (⟨a, b, false⟩ : Wr)⁻¹ = ⟨a⁻¹, b⁻¹, false⟩ := rfl

@[simp] theorem inv_t (a b : Equiv.Perm (Fin 6)) : (⟨a, b, true⟩ : Wr)⁻¹ = ⟨b⁻¹, a⁻¹, true⟩ := rfl

instance : Group Wr where
  mul_assoc := by
    rintro ⟨a, b, e⟩ ⟨a', b', e'⟩ ⟨a'', b'', e''⟩
    cases e <;> cases e' <;> cases e'' <;> simp [mul_assoc]
  one_mul := by
    rintro ⟨a, b, e⟩
    simp
  mul_one := by
    rintro ⟨a, b, e⟩
    cases e <;> simp
  inv_mul_cancel := by
    rintro ⟨a, b, e⟩
    cases e <;> simp

end Wr

@[expose] def pairPerm (a b : Equiv.Perm (Fin 6)) : Equiv.Perm (Fin 2 × Fin 6) where
  toFun x := (x.1, if x.1 = 0 then a x.2 else b x.2)
  invFun x := (x.1, if x.1 = 0 then a⁻¹ x.2 else b⁻¹ x.2)
  left_inv x := by
    obtain ⟨i, j⟩ := x
    fin_cases i <;> simp
  right_inv x := by
    obtain ⟨i, j⟩ := x
    fin_cases i <;> simp

@[expose] def swapPerm : Equiv.Perm (Fin 2 × Fin 6) :=
  Equiv.prodCongr (Equiv.swap 0 1) (Equiv.refl _)

theorem pairPerm_apply_zero (a b : Equiv.Perm (Fin 6)) (j : Fin 6) :
    pairPerm a b (0, j) = (0, a j) := by
  simp [pairPerm]

theorem pairPerm_apply_one (a b : Equiv.Perm (Fin 6)) (j : Fin 6) :
    pairPerm a b (1, j) = (1, b j) := by
  simp [pairPerm]

theorem swapPerm_apply (i : Fin 2) (j : Fin 6) : swapPerm (i, j) = (Equiv.swap 0 1 i, j) := rfl

theorem pairPerm_mul (a b a' b' : Equiv.Perm (Fin 6)) :
    pairPerm (a * a') (b * b') = pairPerm a b * pairPerm a' b' := by
  ext ⟨i, j⟩ <;> fin_cases i <;> simp [pairPerm]

theorem pairPerm_one : pairPerm 1 1 = 1 := by
  ext ⟨i, j⟩ <;> fin_cases i <;> simp [pairPerm]

theorem swapPerm_mul_self : swapPerm * swapPerm = 1 := by
  ext ⟨i, j⟩ <;> fin_cases i <;> simp [swapPerm]

theorem swapPerm_mul_pairPerm (a b : Equiv.Perm (Fin 6)) :
    swapPerm * pairPerm a b = pairPerm b a * swapPerm := by
  ext ⟨i, j⟩ <;> fin_cases i <;> simp [swapPerm, pairPerm]

theorem swapPerm_mul_pairPerm_mul_swapPerm (a b : Equiv.Perm (Fin 6)) :
    swapPerm * pairPerm a b * swapPerm = pairPerm b a := by
  rw [swapPerm_mul_pairPerm, mul_assoc, swapPerm_mul_self, mul_one]

@[expose] def wrPerm : Wr →* Equiv.Perm (Fin 2 × Fin 6) where
  toFun x := pairPerm x.a x.b * (if x.e then swapPerm else 1)
  map_one' := by simp [pairPerm_one]
  map_mul' := by
    rintro ⟨a, b, e⟩ ⟨a', b', e'⟩
    cases e <;> cases e'
    · simp [pairPerm_mul]
    · simp [pairPerm_mul, mul_assoc]
    · simp [pairPerm_mul, mul_assoc, swapPerm_mul_pairPerm]
    · simp only [Wr.mul_tt, Bool.not_true, ite_true, ite_false, mul_one, Bool.false_eq_true]
      rw [pairPerm_mul]
      calc pairPerm a b * pairPerm b' a'
          = pairPerm a b * (swapPerm * pairPerm a' b' * swapPerm) := by
            rw [swapPerm_mul_pairPerm_mul_swapPerm]
        _ = pairPerm a b * swapPerm * pairPerm a' b' * swapPerm := by simp only [mul_assoc]

theorem wrPerm_apply_f (a b : Equiv.Perm (Fin 6)) (i : Fin 2) (j : Fin 6) :
    wrPerm ⟨a, b, false⟩ (i, j) = (i, if i = 0 then a j else b j) := rfl

theorem wrPerm_apply_t (a b : Equiv.Perm (Fin 6)) (i : Fin 2) (j : Fin 6) :
    wrPerm ⟨a, b, true⟩ (i, j) = (Equiv.swap 0 1 i,
      if Equiv.swap 0 1 i = 0 then a j else b j) := rfl

theorem wrPerm_injective : Function.Injective wrPerm := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b, e⟩ h
  cases e
  · have h0 : ∀ j, a j = j := fun j => by
      have := congrArg (fun τ : Equiv.Perm (Fin 2 × Fin 6) => (τ (0, j)).2) h
      simpa [wrPerm_apply_f] using this
    have h1 : ∀ j, b j = j := fun j => by
      have := congrArg (fun τ : Equiv.Perm (Fin 2 × Fin 6) => (τ (1, j)).2) h
      simpa [wrPerm_apply_f] using this
    have : a = 1 := Equiv.ext h0
    have : b = 1 := Equiv.ext h1
    subst a b
    rfl
  · exfalso
    have := congrArg (fun τ : Equiv.Perm (Fin 2 × Fin 6) => (τ (0, 0)).1) h
    simp [wrPerm_apply_t] at this

theorem swapPerm_mem : swapPerm ∈ wreathS6Z2 := by
  intro x y
  show x.1 = y.1 ↔ Equiv.swap 0 1 x.1 = Equiv.swap 0 1 y.1
  exact (Equiv.swap (0 : Fin 2) 1).injective.eq_iff.symm

theorem exists_wr_of_block_zero {τ : Equiv.Perm (Fin 2 × Fin 6)} (hτ : τ ∈ wreathS6Z2)
    (h0 : (τ (0, 0)).1 = 0) : ∃ x : Wr, wrPerm x = τ := by
  have hblk : ∀ x : Fin 2 × Fin 6, (τ x).1 = (τ (x.1, 0)).1 := fun x => (hτ x (x.1, 0)).1 rfl
  have hb0 : ∀ j, (τ (0, j)).1 = 0 := fun j => (hblk (0, j)).trans h0
  have hb1 : ∀ j, (τ (1, j)).1 = 1 := by
    intro j
    have hne : (τ (1, j)).1 ≠ 0 := fun h => by
      have h10 : (1 : Fin 2) = 0 := (hτ (1, j) (0, 0)).2 (h.trans h0.symm)
      exact absurd h10 (by decide)
    omega
  have hai : Function.Injective (fun j : Fin 6 => (τ (0, j)).2) := fun j j' h => by
    have : τ (0, j) = τ (0, j') := Prod.ext ((hb0 j).trans (hb0 j').symm) h
    exact (Prod.ext_iff.1 (τ.injective this)).2
  have hbi : Function.Injective (fun j : Fin 6 => (τ (1, j)).2) := fun j j' h => by
    have : τ (1, j) = τ (1, j') := Prod.ext ((hb1 j).trans (hb1 j').symm) h
    exact (Prod.ext_iff.1 (τ.injective this)).2
  let A : Equiv.Perm (Fin 6) := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hai)
  let B : Equiv.Perm (Fin 6) := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hbi)
  refine ⟨⟨A, B, false⟩, ?_⟩
  ext ⟨i, j⟩ <;> fin_cases i
  · simp [wrPerm_apply_f, hb0]
  · simp [wrPerm_apply_f, hb1]
  · simp [wrPerm_apply_f, A]
  · simp [wrPerm_apply_f, B]

theorem exists_wr_of_mem_wreathS6Z2 {τ : Equiv.Perm (Fin 2 × Fin 6)} (hτ : τ ∈ wreathS6Z2) :
    ∃ x : Wr, wrPerm x = τ := by
  have hblk : ∀ x : Fin 2 × Fin 6, (τ x).1 = (τ (x.1, 0)).1 := fun x => (hτ x (x.1, 0)).1 rfl
  rcases Fin.exists_fin_two.1 ⟨(τ (0, 0)).1, rfl⟩ with h | h
  · exact exists_wr_of_block_zero hτ h
  · have hτ' : swapPerm * τ ∈ wreathS6Z2 := (wreathS6Z2).mul_mem swapPerm_mem hτ
    have h' : ((swapPerm * τ) (0, 0)).1 = 0 := by
      show (swapPerm (τ (0, 0))).1 = 0
      rw [show swapPerm (τ (0, 0)) = (Equiv.swap 0 1 (τ (0, 0)).1, (τ (0, 0)).2) from rfl]
      simp [h]
    obtain ⟨x, hx⟩ := exists_wr_of_block_zero hτ' h'
    refine ⟨⟨1, 1, true⟩ * x, ?_⟩
    rw [map_mul, hx]
    have : wrPerm ⟨1, 1, true⟩ = swapPerm := by simp [wrPerm, pairPerm_one]
    rw [this, ← mul_assoc, swapPerm_mul_self, one_mul]

end CFSG.EvenSporadicStandard.M22Std
