module

public import CFSG.HardMathSupport.Lang.E6Descent.MaxClassCore

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

universe u

open scoped commutatorElement

section

variable {P : Type u} [Group P] (N : Subgroup P) (hN : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)

@[expose] def NMod (N : Subgroup P) (_hN : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) : Type u := Additive ↥N

@[expose] instance NMod.instAddCommGroup : AddCommGroup (NMod N hN) :=
  letI : CommGroup ↥N :=
    { (inferInstance : Group ↥N) with mul_comm := fun a b => Subtype.ext (hN a a.2 b b.2) }
  inferInstanceAs (AddCommGroup (Additive ↥N))

instance NMod.instFinite [Finite P] : Finite (NMod N hN) :=
  Finite.of_equiv ↥N (Additive.ofMul : ↥N ≃ Additive ↥N)

variable {N hN}

@[expose] def NMod.toP (u : NMod N hN) : P := ((Additive.toMul u : ↥N) : P)

@[expose] def NMod.ofP (g : P) (hg : g ∈ N) : NMod N hN := Additive.ofMul (⟨g, hg⟩ : ↥N)

theorem NMod.toP_mem (u : NMod N hN) : u.toP ∈ N := (Additive.toMul u : ↥N).2

theorem NMod.toP_injective : Function.Injective (NMod.toP : NMod N hN → P) := by
  intro a b h
  exact Additive.toMul.injective (Subtype.ext h)

@[simp] theorem NMod.toP_add (u v : NMod N hN) : (u + v).toP = u.toP * v.toP := rfl

@[simp] theorem NMod.toP_zero : (0 : NMod N hN).toP = 1 := rfl

@[simp] theorem NMod.toP_neg (u : NMod N hN) : (-u).toP = u.toP⁻¹ := rfl

@[simp] theorem NMod.toP_sub (u v : NMod N hN) : (u - v).toP = u.toP * v.toP⁻¹ := by
  rw [sub_eq_add_neg]; rfl

@[simp] theorem NMod.toP_ofP (g : P) (hg : g ∈ N) : (NMod.ofP (hN := hN) g hg).toP = g := rfl

@[simp] theorem NMod.ofP_toP (u : NMod N hN) : NMod.ofP (hN := hN) u.toP u.toP_mem = u := rfl

theorem NMod.toP_nsmul (k : ℕ) (u : NMod N hN) : (k • u).toP = u.toP ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul, toP_add, ih, pow_succ]

variable [N.Normal]

@[expose] def conjEnd (g : P) : Module.End ℤ (NMod N hN) :=
  (AddMonoidHom.mk'
    (fun u : NMod N hN => NMod.ofP (hN := hN) (g * u.toP * g⁻¹)
      (Subgroup.Normal.conj_mem inferInstance _ u.toP_mem g))
    (fun u v => NMod.toP_injective (by simp [mul_assoc]))).toIntLinearMap

@[simp] theorem toP_conjEnd (g : P) (u : NMod N hN) :
    (conjEnd g u).toP = g * u.toP * g⁻¹ := rfl

theorem toP_conjEnd_sub (g : P) (u : NMod N hN) :
    ((conjEnd g - 1 : Module.End ℤ (NMod N hN)) u).toP = ⁅g, u.toP⁆ := by
  rw [LinearMap.sub_apply, Module.End.one_apply, NMod.toP_sub, toP_conjEnd, commutatorElement_def]

theorem conjEnd_mul (g h : P) : (conjEnd g * conjEnd h : Module.End ℤ (NMod N hN)) =
    conjEnd (g * h) := by
  ext u
  apply NMod.toP_injective
  simp [conjEnd, mul_assoc]

@[simp] theorem conjEnd_one : (conjEnd 1 : Module.End ℤ (NMod N hN)) = 1 := by
  ext u
  apply NMod.toP_injective
  simp [conjEnd]

@[expose] def GS (K : Subgroup P) : AddSubgroup (NMod N hN) where
  carrier := {u | u.toP ∈ K}
  zero_mem' := by simpa using K.one_mem
  add_mem' := fun {u v} hu hv => by
    show (u + v).toP ∈ K
    rw [NMod.toP_add]; exact K.mul_mem hu hv
  neg_mem' := fun {u} hu => by
    show (-u).toP ∈ K
    rw [NMod.toP_neg]; exact K.inv_mem hu

theorem mem_GS {K : Subgroup P} {u : NMod N hN} : u ∈ GS K ↔ u.toP ∈ K := Iff.rfl

theorem card_GS {K : Subgroup P} (hK : K ≤ N) : Nat.card (GS (N := N) (hN := hN) K) = Nat.card K :=
  Nat.card_congr
    { toFun := fun u => ⟨u.1.toP, u.2⟩
      invFun := fun k => ⟨NMod.ofP (hN := hN) k.1 (hK k.2), by
        show (NMod.ofP (hN := hN) k.1 (hK k.2)).toP ∈ K
        rw [NMod.toP_ofP]; exact k.2⟩
      left_inv := fun u => Subtype.ext (by simp)
      right_inv := fun k => Subtype.ext (by simp) }

end

end CFSG.HardMathSupport.Lang.E6Descent
