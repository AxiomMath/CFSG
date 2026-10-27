module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Algebra.Group.Subgroup.Ker

public section

namespace CFSG.ComponentClassification.HSFLit.KD8c

structure ExtData (G : Type*) [Group G] where
  φ : G → G
  s : G
  map_mul : ∀ a b, φ (a * b) = φ a * φ b
  φ_s : φ s = s
  φ_φ : ∀ b, φ (φ b) = s * b * s⁻¹

namespace ExtData

variable {G : Type*} [Group G] (D : ExtData G)

theorem map_one : D.φ 1 = 1 := by
  have h := D.map_mul 1 1
  rw [one_mul] at h
  exact (mul_eq_left.mp h.symm)

theorem map_inv (a : G) : D.φ a⁻¹ = (D.φ a)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← D.map_mul, inv_mul_cancel, D.map_one]

end ExtData

@[ext] structure Ext {G : Type*} [Group G] (D : ExtData G) where
  a : G
  e : Bool

namespace Ext

variable {G : Type*} [Group G] {D : ExtData G}

instance [DecidableEq G] : DecidableEq (Ext D) := fun x y =>
  if h : x.a = y.a ∧ x.e = y.e then isTrue (Ext.ext h.1 h.2)
  else isFalse fun h' => h ⟨congrArg Ext.a h', congrArg Ext.e h'⟩

@[expose] def equivProd (D : ExtData G) : Ext D ≃ G × Bool where
  toFun x := (x.a, x.e)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype G] : Fintype (Ext D) := Fintype.ofEquiv _ (equivProd D).symm

@[expose] def mul (x y : Ext D) : Ext D :=
  bif x.e then (bif y.e then ⟨x.a * D.φ y.a * D.s, false⟩ else ⟨x.a * D.φ y.a, true⟩)
  else ⟨x.a * y.a, y.e⟩

@[expose] def inv (x : Ext D) : Ext D :=
  bif x.e then ⟨D.s⁻¹ * (D.φ x.a)⁻¹, true⟩ else ⟨x.a⁻¹, false⟩

instance : Mul (Ext D) := ⟨mul⟩

instance : One (Ext D) := ⟨⟨1, false⟩⟩

instance : Inv (Ext D) := ⟨inv⟩

theorem mul_def (x y : Ext D) : x * y = mul x y := rfl

theorem one_def : (1 : Ext D) = ⟨1, false⟩ := rfl

theorem inv_def (x : Ext D) : x⁻¹ = inv x := rfl

theorem mul_assoc' (x y z : Ext D) : x * y * z = x * (y * z) := by
  obtain ⟨xa, xe⟩ := x
  obtain ⟨ya, ye⟩ := y
  obtain ⟨za, ze⟩ := z
  cases xe <;> cases ye <;> cases ze <;> refine Ext.ext ?_ rfl <;>
    simp only [mul_def, mul, Bool.cond_true, Bool.cond_false, D.map_mul, D.φ_φ, D.φ_s] <;> group

theorem one_mul' (x : Ext D) : 1 * x = x := by
  obtain ⟨xa, xe⟩ := x
  refine Ext.ext ?_ rfl
  simp [mul_def, one_def, mul]

theorem inv_mul' (x : Ext D) : x⁻¹ * x = 1 := by
  obtain ⟨xa, xe⟩ := x
  cases xe <;> refine Ext.ext ?_ rfl <;>
    simp only [mul_def, inv_def, one_def, mul, inv, Bool.cond_true, Bool.cond_false] <;> group

instance instGroup : Group (Ext D) := Group.ofLeftAxioms mul_assoc' one_mul' inv_mul'

@[expose] def incl (D : ExtData G) : G →* Ext D where
  toFun a := ⟨a, false⟩
  map_one' := rfl
  map_mul' a b := by simp [mul_def, mul]

@[expose] def q (D : ExtData G) : Ext D := ⟨1, true⟩

theorem card_eq [Finite G] : Nat.card (Ext D) = 2 * Nat.card G := by
  rw [Nat.card_congr (equivProd D), Nat.card_prod, Nat.card_eq_fintype_card (α := Bool),
    Fintype.card_bool, mul_comm]

variable {H : Type*} [Group H]

@[expose] def lift (ι : G →* H) (q : H) (hq : ∀ b, q * ι b * q⁻¹ = ι (D.φ b))
    (hs : q * q = ι D.s) : Ext D →* H where
  toFun x := ι x.a * bif x.e then q else 1
  map_one' := by
    show ι 1 * 1 = 1
    simp
  map_mul' x y := by
    obtain ⟨xa, xe⟩ := x
    obtain ⟨ya, ye⟩ := y
    have hc : ∀ b, q * ι b = ι (D.φ b) * q := fun b => by rw [← hq b]; group
    cases xe <;> cases ye
    · show ι (xa * ya) * 1 = ι xa * 1 * (ι ya * 1)
      simp
    · show ι (xa * ya) * q = ι xa * 1 * (ι ya * q)
      simp [mul_assoc]
    · show ι (xa * D.φ ya) * q = ι xa * q * (ι ya * 1)
      rw [map_mul, mul_one, mul_assoc (ι xa) q, hc, ← mul_assoc]
    · show ι (xa * D.φ ya * D.s) * 1 = ι xa * q * (ι ya * q)
      rw [show ι xa * q * (ι ya * q) = ι xa * (q * ι ya) * q by group, hc, map_mul, map_mul,
        ← hs]
      group

theorem lift_apply (ι : G →* H) (q : H) (hq : ∀ b, q * ι b * q⁻¹ = ι (D.φ b))
    (hs : q * q = ι D.s) (x : Ext D) :
    lift ι q hq hs x = ι x.a * bif x.e then q else 1 := rfl

theorem lift_injective (ι : G →* H) (q : H) (hq : ∀ b, q * ι b * q⁻¹ = ι (D.φ b))
    (hs : q * q = ι D.s) (hι : Function.Injective ι) (hqr : q ∉ ι.range) :
    Function.Injective (lift ι q hq hs) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨xa, xe⟩ h
  rw [lift_apply] at h
  cases xe
  · simp only [Bool.cond_false, mul_one] at h
    rw [show xa = 1 from hι (h.trans (map_one ι).symm)]
    rfl
  · exfalso
    simp only [Bool.cond_true] at h
    exact hqr ⟨xa⁻¹, by rw [map_inv, inv_eq_of_mul_eq_one_right h]⟩

end Ext

end CFSG.ComponentClassification.HSFLit.KD8c
