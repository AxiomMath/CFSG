module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

variable {G : Type*} [Group G] {V M : Subgroup G}

@[expose] def conjV (hMV : ∀ m ∈ M, ∀ v ∈ V, m * v * m⁻¹ ∈ V) (m : M) : V →* V where
  toFun v := ⟨(m : G) * v * (m : G)⁻¹, hMV m m.2 v v.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

@[expose] def conjEnd (hMV : ∀ m ∈ M, ∀ v ∈ V, m * v * m⁻¹ ∈ V) :
    M →* AddMonoid.End (Additive V) where
  toFun m := AddMonoidHom.mk' (fun v : Additive V => Additive.ofMul (conjV hMV m (Additive.toMul v)))
    (fun a b => by simp)
  map_one' := by
    apply AddMonoidHom.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    simp [conjV]
    rfl
  map_mul' m n := by
    apply AddMonoidHom.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((m * n : M) : G) * ((Additive.toMul v : V) : G) * ((m * n : M) : G)⁻¹ =
      (m : G) * ((n : G) * ((Additive.toMul v : V) : G) * (n : G)⁻¹) * (m : G)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev, mul_assoc]

theorem conjEnd_apply (hMV : ∀ m ∈ M, ∀ v ∈ V, m * v * m⁻¹ ∈ V) (m : M) (v : V) :
    (((conjEnd hMV m) (Additive.ofMul v) : Additive V).toMul : G) = (m : G) * v * (m : G)⁻¹ := rfl

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
