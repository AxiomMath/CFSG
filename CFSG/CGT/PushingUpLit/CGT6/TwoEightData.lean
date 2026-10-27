module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.CGT.PushingUpLit.CGT6.TwoEight

structure Data (F L : Type) [Field F] [AddCommGroup L] [Module F L] where
  B : LinearMap.BilinForm F L
  Q : L → F
  alt : ∀ x, B x x = 0
  nondeg : B.Nondegenerate
  Q_smul : ∀ (c : F) (x : L), Q (c • x) = c ^ 2 * Q x
  Q_add : ∀ x y : L, Q (x + y) = Q x + Q y + B x y

abbrev Wd (F L : Type) [Field F] [AddCommGroup L] [Module F L] : Type := F × L × F

theorem add_self_L (F : Type) [Field F] [CharP F 2] {L : Type} [AddCommGroup L] [Module F L]
    (x : L) : x + x = 0 := by
  rw [← two_smul F x]
  have : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [this, zero_smul]

section Basic

variable {F L : Type} [Field F] [AddCommGroup L] [Module F L] (D : Data F L)

theorem B_symm [CharP F 2] (x y : L) : D.B x y = D.B y x := by
  have h := D.alt (x + y)
  simp only [map_add, LinearMap.add_apply, D.alt, zero_add, add_zero] at h
  have h2 : D.B y x = - D.B x y := by linear_combination h
  rw [h2, CharTwo.neg_eq]

theorem B_surj {x : L} (hx : x ≠ 0) (t : F) : ∃ y, D.B x y = t := by
  by_contra hne
  push Not at hne
  apply hx
  apply D.nondeg.1 x
  intro y
  by_contra hy
  obtain ⟨y', hy'⟩ : ∃ y', D.B x y' = t := by
    refine ⟨(t / D.B x y) • y, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hy]
  exact hne y' hy'

theorem B_smul_right (c : F) (x y : L) : D.B x (c • y) = c * D.B x y := by
  rw [map_smul, smul_eq_mul]

theorem B_smul_left (c : F) (x y : L) : D.B (c • x) y = c * D.B x y := by
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem B_eq_zero_of_ne {x : L} (hx : x ≠ 0) : ∃ y, D.B x y ≠ 0 := by
  obtain ⟨y, hy⟩ := B_surj D hx 1
  exact ⟨y, by rw [hy]; exact one_ne_zero⟩

theorem Q_zero : D.Q 0 = 0 := by
  have h := D.Q_smul 0 0
  rw [zero_smul] at h
  simpa using h

end Basic

section Flag

variable {F L : Type} [Field F] [AddCommGroup L] [Module F L] (D : Data F L)

@[expose] def sigFun (x : L) (w : Wd F L) : Wd F L :=
  (w.1 + D.B x w.2.1 + D.Q x * w.2.2, w.2.1 + w.2.2 • x, w.2.2)

@[expose] def lamFun (x : L) (w : Wd F L) : Wd F L :=
  (w.1, w.2.1 + w.1 • x, w.2.2 + D.B x w.2.1 + D.Q x * w.1)

@[expose] def Qt (w : Wd F L) : F := w.1 * w.2.2 + D.Q w.2.1

theorem sigFun_zero (w : Wd F L) : sigFun D 0 w = w := by
  rcases w with ⟨p, y, s⟩
  simp [sigFun, Q_zero]

theorem sigFun_sigFun (x y : L) (w : Wd F L) :
    sigFun D x (sigFun D y w) = sigFun D (x + y) w := by
  rcases w with ⟨p, y₀, s⟩
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · simp only [sigFun, map_add, LinearMap.add_apply, map_smul, smul_eq_mul, D.Q_add]
    ring
  · simp only [sigFun, smul_add]
    rw [add_assoc, add_comm (s • y) (s • x)]

variable [CharP F 2]

theorem lamFun_lamFun (x : L) (w : Wd F L) : lamFun D x (lamFun D x w) = w := by
  rcases w with ⟨p, y, s⟩
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · simp only [lamFun]
    rw [add_assoc, add_self_L F (p • x), add_zero]
  · simp only [lamFun, map_add, map_smul, smul_eq_mul, D.alt]
    have h2 : D.Q x * p + D.Q x * p = 0 := by
      rw [← two_mul]
      have : (2 : F) = 0 := CharP.cast_eq_zero F 2
      rw [this, zero_mul]
    have h3 : D.B x y + D.B x y = 0 := by
      rw [← two_mul]
      have : (2 : F) = 0 := CharP.cast_eq_zero F 2
      rw [this, zero_mul]
    linear_combination h2 + h3

@[expose] def sigPerm (x : L) : Equiv.Perm (Wd F L) where
  toFun := sigFun D x
  invFun := sigFun D x
  left_inv w := by rw [sigFun_sigFun, add_self_L F, sigFun_zero]
  right_inv w := by rw [sigFun_sigFun, add_self_L F, sigFun_zero]

@[expose] def lamPerm (x : L) : Equiv.Perm (Wd F L) where
  toFun := lamFun D x
  invFun := lamFun D x
  left_inv w := lamFun_lamFun D x w
  right_inv w := lamFun_lamFun D x w

theorem sigPerm_apply (x : L) (w : Wd F L) : sigPerm D x w = sigFun D x w := rfl

theorem lamPerm_apply (x : L) (w : Wd F L) : lamPerm D x w = lamFun D x w := rfl

theorem sigPerm_mul (x y : L) : sigPerm D x * sigPerm D y = sigPerm D (x + y) := by
  ext w : 1
  exact sigFun_sigFun D x y w

theorem sigPerm_zero : sigPerm D 0 = 1 := by
  ext w : 1
  exact sigFun_zero D w

theorem sigPerm_inv (x : L) : (sigPerm D x)⁻¹ = sigPerm D x := by
  rw [inv_eq_iff_mul_eq_one, sigPerm_mul, add_self_L F, sigPerm_zero]

@[expose] def S0 : Subgroup (Equiv.Perm (Wd F L)) where
  carrier := Set.range (sigPerm D)
  one_mem' := ⟨0, sigPerm_zero D⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, (sigPerm_mul D x y).symm⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, (sigPerm_inv D x).symm⟩

theorem mem_S0 {g : Equiv.Perm (Wd F L)} : g ∈ S0 D ↔ ∃ x, sigPerm D x = g := Iff.rfl

theorem sigPerm_injective : Function.Injective (sigPerm D) := by
  intro x y h
  have := congrArg (fun g : Equiv.Perm (Wd F L) => (g (0, 0, 1)).2.1) h
  simpa [sigPerm_apply, sigFun] using this

@[expose] def IsAddPerm (a : Equiv.Perm (Wd F L)) : Prop := ∀ w w', a (w + w') = a w + a w'

theorem sigPerm_isAdd (x : L) : IsAddPerm (sigPerm D x) := by
  intro w w'
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [sigPerm_apply, sigFun, Prod.fst_add, Prod.snd_add, map_add, mul_add]
    ring
  · simp only [sigPerm_apply, sigFun, Prod.fst_add, Prod.snd_add, add_smul]
    abel
  · simp [sigPerm_apply, sigFun]

@[expose] def Fix (G : Subgroup (Equiv.Perm (Wd F L))) : Set (Wd F L) := {w | ∀ a ∈ G, a w = w}

theorem lamPerm_isAdd (x : L) : IsAddPerm (lamPerm D x) := by
  intro w w'
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp [lamPerm_apply, lamFun]
  · simp only [lamPerm_apply, lamFun, Prod.fst_add, Prod.snd_add, add_smul]
    abel
  · simp only [lamPerm_apply, lamFun, Prod.fst_add, Prod.snd_add, map_add, mul_add]
    ring

end Flag

end CFSG.CGT.PushingUpLit.CGT6.TwoEight
