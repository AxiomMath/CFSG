module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocks

variable (k p m : ℕ)

abbrev Ω := (Fin k × ZMod p) ⊕ Fin m

variable {k p m}

@[expose] def blockPerm (π : Equiv.Perm (Fin k × ZMod p)) : Equiv.Perm (Ω k p m) :=
  Equiv.sumCongr π (Equiv.refl _)

@[expose] def blockPermHom : Equiv.Perm (Fin k × ZMod p) →* Equiv.Perm (Ω k p m) where
  toFun := blockPerm
  map_one' := by ext x; cases x <;> rfl
  map_mul' π σ := by ext x; cases x <;> rfl

@[simp] theorem blockPermHom_apply (π : Equiv.Perm (Fin k × ZMod p)) :
    (blockPermHom π : Equiv.Perm (Ω k p m)) = blockPerm π := rfl

@[simp] theorem blockPerm_inl (π : Equiv.Perm (Fin k × ZMod p)) (x : Fin k × ZMod p) :
    blockPerm (m := m) π (Sum.inl x) = Sum.inl (π x) := rfl

@[simp] theorem blockPerm_inr (π : Equiv.Perm (Fin k × ZMod p)) (y : Fin m) :
    blockPerm (m := m) π (Sum.inr y) = Sum.inr y := rfl

@[expose] def transl (f : Fin k → ZMod p) : Equiv.Perm (Fin k × ZMod p) where
  toFun x := (x.1, x.2 + f x.1)
  invFun x := (x.1, x.2 - f x.1)
  left_inv x := by simp
  right_inv x := by simp

@[simp] theorem transl_apply (f : Fin k → ZMod p) (x : Fin k × ZMod p) :
    transl f x = (x.1, x.2 + f x.1) := rfl

@[expose] def translHom : Multiplicative (Fin k → ZMod p) →* Equiv.Perm (Fin k × ZMod p) where
  toFun f := transl (Multiplicative.toAdd f)
  map_one' := by ext x <;> simp
  map_mul' f g := by
    ext x
    · rfl
    · simp only [transl_apply, toAdd_mul, Pi.add_apply, Equiv.Perm.coe_mul, Function.comp_apply]
      ring

@[expose] def baseHom : Multiplicative (Fin k → ZMod p) →* Equiv.Perm (Ω k p m) :=
  blockPermHom.comp translHom

theorem baseHom_apply (f : Multiplicative (Fin k → ZMod p)) :
    (baseHom f : Equiv.Perm (Ω k p m)) = blockPerm (transl (Multiplicative.toAdd f)) := rfl

@[expose] def base : Subgroup (Equiv.Perm (Ω k p m)) := (baseHom (k := k) (p := p) (m := m)).range

@[expose] def scale (i : Fin k) (r : (ZMod p)ˣ) : Equiv.Perm (Fin k × ZMod p) where
  toFun x := (x.1, if x.1 = i then (r : ZMod p) * x.2 else x.2)
  invFun x := (x.1, if x.1 = i then ((r⁻¹ : (ZMod p)ˣ) : ZMod p) * x.2 else x.2)
  left_inv x := by
    obtain ⟨j, y⟩ := x
    by_cases h : j = i <;> simp [h, ← mul_assoc]
  right_inv x := by
    obtain ⟨j, y⟩ := x
    by_cases h : j = i <;> simp [h, ← mul_assoc]

@[simp] theorem scale_apply (i : Fin k) (r : (ZMod p)ˣ) (x : Fin k × ZMod p) :
    scale i r x = (x.1, if x.1 = i then (r : ZMod p) * x.2 else x.2) := rfl

@[expose] def swapB (i j : Fin k) : Equiv.Perm (Fin k × ZMod p) :=
  Equiv.prodCongr (Equiv.swap i j) (Equiv.refl _)

@[simp] theorem swapB_apply (i j : Fin k) (x : Fin k × ZMod p) :
    swapB i j x = (Equiv.swap i j x.1, x.2) := rfl

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocks
