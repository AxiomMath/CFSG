module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.SeitzReduction.RankOne

variable {V : Type*} [AddCommGroup V]

theorem affine_of_eq_add {x : Equiv.Perm V} (φ : V →+ V) (b : V) (hx : ∀ v, x v = φ v + b) :
    ∀ v w, x (v + w) + x 0 = x v + x w := by
  intro v w
  simp only [hx, map_add, map_zero, zero_add]
  abel

@[expose] def affineLinearPart (x : Equiv.Perm V) (hx : ∀ v w, x (v + w) + x 0 = x v + x w) :
    AddAut V where
  toFun v := x v - x 0
  invFun w := x.symm (w + x 0)
  left_inv v := by simp
  right_inv w := by simp
  map_add' v w := by
    rw [eq_sub_of_add_eq (hx v w)]
    abel

theorem affineLinearPart_apply (x : Equiv.Perm V) (hx : ∀ v w, x (v + w) + x 0 = x v + x w)
    (v : V) : affineLinearPart x hx v = x v - x 0 :=
  rfl

@[expose] def affineLinearPartHom (N : Subgroup (Equiv.Perm V))
    (haff : ∀ x ∈ N, ∀ v w, x (v + w) + x 0 = x v + x w) : N →* Multiplicative (AddAut V) where
  toFun x := Multiplicative.ofAdd (affineLinearPart (x : Equiv.Perm V) (haff x x.2))
  map_one' := by
    apply Multiplicative.toAdd.injective
    ext v
    simp [affineLinearPart_apply]
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    ext v
    simp only [toAdd_ofAdd, toAdd_mul, AddAut.add_apply, affineLinearPart_apply, Subgroup.coe_mul,
      Equiv.Perm.mul_apply]
    rw [sub_eq_sub_iff_add_eq_add]
    simpa only [sub_add_cancel] using
      haff x x.2 ((y : Equiv.Perm V) v - (y : Equiv.Perm V) 0) ((y : Equiv.Perm V) 0)

theorem affineLinearPartHom_apply (N : Subgroup (Equiv.Perm V))
    (haff : ∀ x ∈ N, ∀ v w, x (v + w) + x 0 = x v + x w) (x : N) (v : V) :
    Multiplicative.toAdd (affineLinearPartHom N haff x) v = (x : Equiv.Perm V) v -
      (x : Equiv.Perm V) 0 :=
  rfl

theorem affineLinearPartHom_injective [Finite V] (N : Subgroup (Equiv.Perm V))
    (haff : ∀ x ∈ N, ∀ v w, x (v + w) + x 0 = x v + x w) (hs : IsSimpleGroup N)
    (hlt : Nat.card V < Nat.card N) : Function.Injective (affineLinearPartHom N haff) := by
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs (affineLinearPartHom N haff).ker
    inferInstance with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).1 h
  · exfalso
    have htr : ∀ x : N, ∀ v, (x : Equiv.Perm V) v = v + (x : Equiv.Perm V) 0 := by
      intro x v
      have hx : x ∈ (affineLinearPartHom N haff).ker := h ▸ Subgroup.mem_top x
      have hv := congrArg (fun f : Multiplicative (AddAut V) => Multiplicative.toAdd f v)
        (MonoidHom.mem_ker.1 hx)
      simp only [affineLinearPartHom_apply, toAdd_one, AddAut.zero_apply] at hv
      exact eq_add_of_sub_eq hv
    have hinj : Function.Injective (fun x : N => (x : Equiv.Perm V) 0) := by
      intro x y hxy
      apply Subtype.ext
      ext v
      rw [htr x v, htr y v]
      exact congrArg (v + ·) hxy
    have := Nat.card_le_card_of_injective _ hinj
    omega

end CFSG.SeitzReduction.RankOne
