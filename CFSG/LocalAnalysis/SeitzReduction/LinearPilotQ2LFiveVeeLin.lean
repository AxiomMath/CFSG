module

public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.SeitzReduction.LinearPilot

open scoped IsMulCommutative

section RingIdentities

variable {R : Type*} [Ring R]

theorem exists_isMulCommutative_subring_pair {a b : R} (hab : a * b = b * a) :
    ∃ S : Subring R, IsMulCommutative S ∧ a ∈ S ∧ b ∈ S := by
  have hcomm : ({a, b} : Set R).Pairwise Commute := by
    intro x hx y hy _
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact Commute.refl _
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hab
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hab.symm
    · rw [Set.mem_singleton_iff] at hx hy
      subst hx hy
      exact Commute.refl _
  exact ⟨Subring.closure {a, b}, Subring.isMulCommutative_closure hcomm,
    Subring.subset_closure (by simp), Subring.subset_closure (by simp)⟩

theorem mul_sub_one_mul_mul_eq_zero_of_pow_three {a b : R} (hab : a * b = b * a)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    (a * b - 1) * (a * b * b - 1) * (b - 1) * (a - 1) = 0 := by
  obtain ⟨S, hS, haS, hbS⟩ := exists_isMulCommutative_subring_pair hab
  let a' : S := ⟨a, haS⟩
  let b' : S := ⟨b, hbS⟩
  have ha' : a' ^ 3 = 1 := Subtype.ext (by simp [a', ha])
  have hb' : b' ^ 3 = 1 := Subtype.ext (by simp [b', hb])
  have h : (a' * b' - 1) * (a' * b' * b' - 1) * (b' - 1) * (a' - 1) = 0 := by
    linear_combination (b' ^ 4 - b' ^ 3) * ha' + (-a' ^ 2 * b' + a' + b' - 1) * hb'
  simpa [a', b'] using congrArg Subtype.val h

theorem idempotent_identities_of_sq_add_self_add_one {z b : R} (hzb : z * b = b * z)
    (hz : z * z + z + 1 = 0) (hb : b ^ 3 = 1) (h2 : (2 : R) = 0) :
    (b - 1) * ((z * z * b - 1) * (z * b - 1)) = 0 ∧
      (z * b - 1) * ((b - 1) * (z * z * b - 1)) = 0 ∧
      (z * z * b - 1) * ((b - 1) * (z * b - 1)) = 0 ∧
      (z * z * b - 1) * (z * b - 1) + (b - 1) * (z * z * b - 1) + (b - 1) * (z * b - 1) = 1 ∧
      (z * z * b - 1) * (z * b - 1) = (z * b - 1) * (z * z * b - 1) ∧
      (b - 1) * (z * z * b - 1) = (z * z * b - 1) * (b - 1) ∧
      (b - 1) * (z * b - 1) = (z * b - 1) * (b - 1) := by
  obtain ⟨S, hS, hzS, hbS⟩ := exists_isMulCommutative_subring_pair hzb
  let z' : S := ⟨z, hzS⟩
  let b' : S := ⟨b, hbS⟩
  have hz' : z' * z' + z' + 1 = 0 := Subtype.ext (by simp [z', hz])
  have hb' : b' ^ 3 = 1 := Subtype.ext (by simp [b', hb])
  have h2' : (2 : S) = 0 := Subtype.ext (by push_cast; exact h2)
  have e1 : (b' - 1) * ((z' * z' * b' - 1) * (z' * b' - 1)) = 0 := by
    linear_combination (b' ^ 3 * z' - b' ^ 3 - b' ^ 2 * z' + b') * hz' + hb'
  have e2 : (z' * b' - 1) * ((b' - 1) * (z' * z' * b' - 1)) = 0 := by
    linear_combination (b' ^ 3 * z' - b' ^ 3 - b' ^ 2 * z' + b') * hz' + hb'
  have e3 : (z' * z' * b' - 1) * ((b' - 1) * (z' * b' - 1)) = 0 := by
    linear_combination (b' ^ 3 * z' - b' ^ 3 - b' ^ 2 * z' + b') * hz' + hb'
  have e4 : (z' * z' * b' - 1) * (z' * b' - 1) + (b' - 1) * (z' * z' * b' - 1) +
      (b' - 1) * (z' * b' - 1) = 1 := by
    linear_combination (b' ^ 2 * z' - 2 * b') * hz' + h2'
  have e5 : (z' * z' * b' - 1) * (z' * b' - 1) = (z' * b' - 1) * (z' * z' * b' - 1) := by ring
  have e6 : (b' - 1) * (z' * z' * b' - 1) = (z' * z' * b' - 1) * (b' - 1) := by ring
  have e7 : (b' - 1) * (z' * b' - 1) = (z' * b' - 1) * (b' - 1) := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [z', b'] using congrArg Subtype.val e1
  · simpa [z', b'] using congrArg Subtype.val e2
  · simpa [z', b'] using congrArg Subtype.val e3
  · simpa [z', b'] using congrArg Subtype.val e4
  · simpa [z', b'] using congrArg Subtype.val e5
  · simpa [z', b'] using congrArg Subtype.val e6
  · simpa [z', b'] using congrArg Subtype.val e7

end RingIdentities

section Endomorphisms

variable {E : Type*} [AddCommGroup E]

theorem card_ker_mul_card_range_addMonoidHom [Finite E] (f : E →+ E) :
    Nat.card f.ker * Nat.card f.range = Nat.card E := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker, mul_comm,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv]

theorem addMonoidEnd_two_eq_zero (h2 : ∀ x : E, x + x = 0) : (2 : AddMonoid.End E) = 0 := by
  ext x
  rw [show (2 : AddMonoid.End E) = 1 + 1 from one_add_one_eq_two.symm]
  exact h2 x

theorem addMonoidEnd_mul_apply (f g : AddMonoid.End E) (x : E) : (f * g) x = f (g x) := rfl

theorem addMonoidEnd_sub_one_apply (f : AddMonoid.End E) (x : E) : (f - 1) x = f x - x := rfl

theorem apply_eq_of_injective_mul_sub_one {a b : AddMonoid.End E} (hab : a * b = b * a)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (h1 : Function.Injective ⇑(a * b - 1 : AddMonoid.End E))
    (h2 : Function.Injective ⇑(a * b * b - 1 : AddMonoid.End E)) (x : E) : b ((a - 1) x) = (a - 1) x := by
  have key := congrArg (fun f : AddMonoid.End E => f x)
    (mul_sub_one_mul_mul_eq_zero_of_pow_three hab ha hb)
  simp only [addMonoidEnd_mul_apply] at key
  have k1 : (a * b * b - 1) ((b - 1) ((a - 1) x)) = 0 := h1 (by rw [key, map_zero]; rfl)
  have k2 : (b - 1) ((a - 1) x) = 0 := h2 (by rw [k1, map_zero])
  rw [addMonoidEnd_sub_one_apply] at k2
  exact sub_eq_zero.1 k2

theorem mul_add_add_eq_zero_of_injective {h : AddMonoid.End E} (hh : h ^ 3 = 1)
    (hinj : Function.Injective ⇑(h - 1 : AddMonoid.End E)) : h * h + h + 1 = 0 := by
  ext x
  have key : (h - 1) ((h * h + h + 1) x) = 0 := by
    have e : (h - 1) * (h * h + h + 1) = h ^ 3 - 1 := by noncomm_ring
    rw [← addMonoidEnd_mul_apply, e, hh, sub_self]
    rfl
  exact hinj (by rw [key]; exact (map_zero _).symm)

theorem card_eq_card_fixed_mul_card_fixed_mul_card_fixed [Finite E] (h2 : ∀ x : E, x + x = 0)
    {z b : AddMonoid.End E} (hzb : z * b = b * z) (hz : z * z + z + 1 = 0) (hb : b ^ 3 = 1) :
    Nat.card E = Nat.card {x : E // b x = x} * Nat.card {x : E // (z * b) x = x} *
      Nat.card {x : E // (z * z * b) x = x} := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ :=
    idempotent_identities_of_sq_add_self_add_one hzb hz hb (addMonoidEnd_two_eq_zero h2)
  have hfix : ∀ (f : AddMonoid.End E) (x : E), f x = x → (f - 1) x = 0 := fun f x hx => by
    rw [addMonoidEnd_sub_one_apply, hx, sub_self]
  have hfix' : ∀ (f : AddMonoid.End E) (x : E), (f - 1) x = 0 → f x = x := fun f x hx => by
    rw [addMonoidEnd_sub_one_apply] at hx
    exact sub_eq_zero.1 hx
  set e₁ : AddMonoid.End E := (z * z * b - 1) * (z * b - 1) with he₁def
  set e₂ : AddMonoid.End E := (b - 1) * (z * z * b - 1) with he₂def
  set e₃ : AddMonoid.End E := (b - 1) * (z * b - 1) with he₃def
  have he₁ : ∀ v, b (e₁ v) = e₁ v := fun v => hfix' _ _ (by
    rw [← addMonoidEnd_mul_apply, i1]
    rfl)
  have he₂ : ∀ v, (z * b) (e₂ v) = e₂ v := fun v => hfix' _ _ (by
    rw [← addMonoidEnd_mul_apply, i2]
    rfl)
  have he₃ : ∀ v, (z * z * b) (e₃ v) = e₃ v := fun v => hfix' _ _ (by
    rw [← addMonoidEnd_mul_apply, i3]
    rfl)
  have k12 : ∀ y, (z * b) y = y → e₁ y = 0 := fun y hy => by
    rw [he₁def, addMonoidEnd_mul_apply, hfix _ _ hy, map_zero]
  have k13 : ∀ w, (z * z * b) w = w → e₁ w = 0 := fun w hw => by
    rw [i5, addMonoidEnd_mul_apply, hfix _ _ hw, map_zero]
  have k21 : ∀ x, b x = x → e₂ x = 0 := fun x hx => by
    rw [i6, addMonoidEnd_mul_apply, hfix _ _ hx, map_zero]
  have k23 : ∀ w, (z * z * b) w = w → e₂ w = 0 := fun w hw => by
    rw [he₂def, addMonoidEnd_mul_apply, hfix _ _ hw, map_zero]
  have k31 : ∀ x, b x = x → e₃ x = 0 := fun x hx => by
    rw [i7, addMonoidEnd_mul_apply, hfix _ _ hx, map_zero]
  have k32 : ∀ y, (z * b) y = y → e₃ y = 0 := fun y hy => by
    rw [he₃def, addMonoidEnd_mul_apply, hfix _ _ hy, map_zero]
  have hsum : ∀ v, e₁ v + e₂ v + e₃ v = v := fun v => by
    have h := congrArg (fun f : AddMonoid.End E => f v) i4
    exact h
  have f1 : ∀ x, b x = x → e₁ x = x := fun x hx => by
    have h := hsum x
    rwa [k21 x hx, k31 x hx, add_zero, add_zero] at h
  have f2 : ∀ y, (z * b) y = y → e₂ y = y := fun y hy => by
    have h := hsum y
    rwa [k12 y hy, k32 y hy, zero_add, add_zero] at h
  have f3 : ∀ w, (z * z * b) w = w → e₃ w = w := fun w hw => by
    have h := hsum w
    rwa [k13 w hw, k23 w hw, zero_add, zero_add] at h
  let Φ : E ≃ {x : E // b x = x} × {x : E // (z * b) x = x} × {x : E // (z * z * b) x = x} :=
    { toFun := fun v => (⟨e₁ v, he₁ v⟩, ⟨e₂ v, he₂ v⟩, ⟨e₃ v, he₃ v⟩)
      invFun := fun p => (p.1 : E) + (p.2.1 : E) + (p.2.2 : E)
      left_inv := fun v => hsum v
      right_inv := fun p => by
        obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨w, hw⟩⟩ := p
        refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
        · change e₁ (x + y + w) = x
          rw [map_add, map_add, f1 x hx, k12 y hy, k13 w hw, add_zero, add_zero]
        · change e₂ (x + y + w) = y
          rw [map_add, map_add, k21 x hx, f2 y hy, k23 w hw, zero_add, add_zero]
        · change e₃ (x + y + w) = w
          rw [map_add, map_add, k31 x hx, k32 y hy, f3 w hw, zero_add, zero_add] }
  rw [Nat.card_congr Φ, Nat.card_prod, Nat.card_prod]
  exact (Nat.mul_assoc _ _ _).symm

theorem card_fixed_mul_card_range_sub [Finite E] (f : AddMonoid.End E) :
    Nat.card {x : E // f x = x} * Nat.card (Set.range fun x => f x - x) = Nat.card E := by
  let g : E →+ E :=
    { toFun := fun x => f x - x
      map_zero' := by rw [map_zero, sub_zero]
      map_add' := fun x y => by rw [map_add]; abel }
  have h := card_ker_mul_card_range_addMonoidHom g
  have h1 : Nat.card g.ker = Nat.card {x : E // f x = x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      change f x - x = 0 ↔ f x = x
      exact sub_eq_zero)
  have h2 : Nat.card g.range = Nat.card (Set.range fun x => f x - x) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y => by
      change (∃ x, f x - x = y) ↔ ∃ x, f x - x = y
      exact Iff.rfl)
  rw [← h1, ← h2, h]
end Endomorphisms

end CFSG.SeitzReduction.LinearPilot
