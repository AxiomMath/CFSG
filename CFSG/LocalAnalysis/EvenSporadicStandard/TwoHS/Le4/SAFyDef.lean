module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

abbrev Z3 : Type := Multiplicative (ZMod 3)

abbrev HModel : Type := DihedralGroup 4 × Z3 × Equiv.Perm (Fin 5)

@[expose] def v0 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def dihChar (b : ℤˣ) : DihedralGroup 4 → ℤˣ
  | .r k => (-1) ^ k.val
  | .sr k => b * (-1) ^ k.val

structure FyConf {G : Type} [Group G] (t r : G) (Θ : HModel →* G) : Prop where
  inj : Function.Injective Θ
  mem_range : ∀ x : G, (x * t = t * x ∧ x * r = r * x) ↔ x ∈ Θ.range
  t_eq : Θ (DihedralGroup.r 2, 1, 1) = t
  r_eq : Θ (1, Multiplicative.ofAdd 1, 1) = r
  v_conj : ∃ δ : DihedralGroup 4, (δ = 1 ∨ δ = DihedralGroup.r 2) ∧
    (∃ g : G, Θ (δ, 1, v0) = g * t * g⁻¹) ∧ ¬ ∃ g : G, t * Θ (δ, 1, v0) = g * t * g⁻¹
  one_class : ∀ a : G, a * t = t * a → orderOf a = 3 →
    ∃ n : G, n * t = t * n ∧ n * a * n⁻¹ = r
  fusion : ∃ n : G, n * t = t * n ∧
    n * Θ (DihedralGroup.sr 0, 1, 1) * n⁻¹ = Θ (DihedralGroup.sr 1, 1, Equiv.swap 0 1)

structure FyCoset {G : Type} [Group G] (L : Subgroup G) (f y : G) (Θ : HModel →* G) : Prop where
  mem_f : ∀ (d : DihedralGroup 4) (c : Z3) (σ : Equiv.Perm (Fin 5)),
    Θ (d, c, σ) ∈ L ⊔ zpowers f ↔ ∃ k : ZMod 4, d = DihedralGroup.r k
  mem_y : ∀ (d : DihedralGroup 4) (c : Z3) (σ : Equiv.Perm (Fin 5)),
    Θ (d, c, σ) ∈ L ⊔ zpowers y ↔ dihChar 1 d * Equiv.Perm.sign σ = 1

structure FyModelFacts {G : Type} [Group G] (L : Subgroup G) (f y : G) : Prop where
  conf : ∃ (r : G) (Θ : HModel →* G), FyConf (f ^ 2) r Θ ∧ FyCoset L f y Θ
  outer3 : ∀ w : G, w * w = 1 → w * f ^ 2 = f ^ 2 * w → w ∉ L ⊔ zpowers f →
    ∃ r : G, r ∈ L ∧ orderOf r = 3 ∧ r * w = w * r

theorem dihChar_r (b : ℤˣ) (k : ZMod 4) : dihChar b (DihedralGroup.r k) = (-1) ^ k.val := rfl

theorem dihChar_sr (b : ℤˣ) (k : ZMod 4) :
    dihChar b (DihedralGroup.sr k) = b * (-1) ^ k.val := rfl

theorem dihChar_sr_eq (b : ℤˣ) (k : ZMod 4) :
    dihChar b (DihedralGroup.sr k) = b * dihChar 1 (DihedralGroup.sr k) := by
  simp [dihChar]

theorem dihChar_r_two (b : ℤˣ) : dihChar b (DihedralGroup.r 2) = 1 := by
  simp [dihChar]
  decide

end CFSG.EvenSporadicStandard.TwoHS
