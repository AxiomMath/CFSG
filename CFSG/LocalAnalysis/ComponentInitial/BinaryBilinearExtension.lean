module

public import CFSG.LocalAnalysis.ComponentInitial.BinaryQuadraticRefinement
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open scoped commutatorElement

variable {U W : Type*} [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]

@[ext] structure BinExt (b : U →ₗ[ZMod 2] U →ₗ[ZMod 2] W) where
  fst : U
  snd : W

namespace BinExt

variable {b : U →ₗ[ZMod 2] U →ₗ[ZMod 2] W}

@[expose] def op (x y : BinExt b) : BinExt b :=
  ⟨x.fst + y.fst, x.snd + y.snd + b x.fst y.fst⟩

variable (b) in
@[expose] def zero : BinExt b := ⟨0, 0⟩

variable (b) in
@[expose] def iota (w : W) : BinExt b := ⟨0, w⟩

@[expose] def pi (x : BinExt b) : U := x.fst

variable (b) in
@[expose] def center0 : Set (BinExt b) := {x | x.fst = 0}

theorem add_self_zmod {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (x : V) : x + x = 0 :=
  two_smul_eq_zero_of_zmod x

instance : Group (BinExt b) where
  mul := op
  mul_assoc x y z := by
    ext
    · exact add_assoc _ _ _
    · change x.snd + y.snd + b x.fst y.fst + z.snd + b (x.fst + y.fst) z.fst =
        x.snd + (y.snd + z.snd + b y.fst z.fst) + b x.fst (y.fst + z.fst)
      simp only [map_add, LinearMap.add_apply]
      abel
  one := zero b
  one_mul x := by
    ext
    · exact zero_add _
    · change 0 + x.snd + b 0 x.fst = x.snd
      simp
  mul_one x := by
    ext
    · exact add_zero _
    · change x.snd + 0 + b x.fst 0 = x.snd
      simp
  inv x := ⟨x.fst, x.snd + b x.fst x.fst⟩
  inv_mul_cancel x := by
    ext
    · exact add_self_zmod x.fst
    · change x.snd + b x.fst x.fst + x.snd + b x.fst x.fst = 0
      rw [show x.snd + b x.fst x.fst + x.snd + b x.fst x.fst =
        (x.snd + x.snd) + (b x.fst x.fst + b x.fst x.fst) by abel, add_self_zmod, add_self_zmod,
        add_zero]

theorem mul_def (x y : BinExt b) : x * y = ⟨x.fst + y.fst, x.snd + y.snd + b x.fst y.fst⟩ := rfl

theorem one_def : (1 : BinExt b) = ⟨0, 0⟩ := rfl

theorem inv_def (x : BinExt b) : x⁻¹ = ⟨x.fst, x.snd + b x.fst x.fst⟩ := rfl

theorem sq_def (x : BinExt b) : x ^ 2 = ⟨0, b x.fst x.fst⟩ := by
  rw [sq, mul_def]
  ext
  · exact add_self_zmod _
  · change x.snd + x.snd + b x.fst x.fst = b x.fst x.fst
    rw [add_self_zmod, zero_add]

theorem commutator_def (x y : BinExt b) :
    x⁻¹ * y⁻¹ * x * y = ⟨0, b x.fst y.fst + b y.fst x.fst⟩ := by
  simp only [mul_def, inv_def]
  ext
  · change x.fst + y.fst + x.fst + y.fst = 0
    rw [show x.fst + y.fst + x.fst + y.fst = (x.fst + x.fst) + (y.fst + y.fst) by abel,
      add_self_zmod, add_self_zmod, add_zero]
  · change x.snd + b x.fst x.fst + (y.snd + b y.fst y.fst) + b x.fst y.fst + x.snd +
      b (x.fst + y.fst) x.fst + y.snd + b (x.fst + y.fst + x.fst) y.fst =
        b x.fst y.fst + b y.fst x.fst
    simp only [map_add, LinearMap.add_apply]
    have h1 := add_self_zmod x.snd
    have h2 := add_self_zmod y.snd
    have h3 := add_self_zmod (b x.fst x.fst)
    have h4 := add_self_zmod (b y.fst y.fst)
    have h5 := add_self_zmod (b x.fst y.fst)
    rw [← sub_eq_zero]
    have e : x.snd + b x.fst x.fst + (y.snd + b y.fst y.fst) + b x.fst y.fst + x.snd +
        (b x.fst x.fst + b y.fst x.fst) + y.snd + (b x.fst y.fst + b y.fst y.fst +
          b x.fst y.fst) - (b x.fst y.fst + b y.fst x.fst) =
        (x.snd + x.snd) + (y.snd + y.snd) + (b x.fst x.fst + b x.fst x.fst) +
          (b y.fst y.fst + b y.fst y.fst) + (b x.fst y.fst + b x.fst y.fst) := by abel
    rw [e, h1, h2, h3, h4, h5]
    simp

variable (b) in
@[expose] def iotaHom : Multiplicative W →* BinExt b where
  toFun w := iota b w.toAdd
  map_one' := rfl
  map_mul' w z := by
    ext
    · exact (add_zero 0).symm
    · change w.toAdd + z.toAdd = w.toAdd + z.toAdd + b 0 0
      simp

variable (b) in
@[expose] def piHom : BinExt b →* Multiplicative U where
  toFun x := Multiplicative.ofAdd x.fst
  map_one' := rfl
  map_mul' _ _ := rfl

variable (b) in
@[expose] def centerSub : Subgroup (BinExt b) := (piHom b).ker

instance : (centerSub b).Normal := (piHom b).normal_ker

theorem mem_centerSub {x : BinExt b} : x ∈ centerSub b ↔ x.fst = 0 := by
  rw [centerSub, MonoidHom.mem_ker]
  exact ⟨fun h => congrArg Multiplicative.toAdd h, fun h => congrArg Multiplicative.ofAdd h⟩

end BinExt

open BinExt

theorem binary_bilinear_extension_group [FiniteDimensional (ZMod 2) U]
    [FiniteDimensional (ZMod 2) W] (b : U →ₗ[ZMod 2] U →ₗ[ZMod 2] W) :
    (∀ x y : BinExt b, x * y = op x y) ∧
    Nat.card (BinExt b) = 2 ^ (Module.finrank (ZMod 2) U + Module.finrank (ZMod 2) W) ∧
    (1 : BinExt b) = zero b ∧
    (∀ x : BinExt b, x⁻¹ = ⟨x.fst, x.snd + b x.fst x.fst⟩) ∧
    Function.Injective (iotaHom b) ∧ (iotaHom b).range = centerSub b ∧
    ((centerSub b : Set (BinExt b)) = center0 b) ∧ centerSub b ≤ Subgroup.center (BinExt b) ∧
    (∀ x : BinExt b, piHom b x = Multiplicative.ofAdd (pi x)) ∧
    Function.Surjective (piHom b) ∧ (piHom b).ker = centerSub b ∧
    Nonempty (BinExt b ⧸ centerSub b ≃* Multiplicative U) ∧
    (∀ x : BinExt b, x ^ 4 = 1) ∧
    (∀ x : BinExt b, x ^ 2 = ⟨0, b x.fst x.fst⟩) ∧
    (∀ x y : BinExt b, x⁻¹ * y⁻¹ * x * y = ⟨0, b x.fst y.fst + b y.fst x.fst⟩) ∧
    ((Subgroup.center (BinExt b) : Set (BinExt b)) =
      {x | ∀ v : U, b x.fst v + b v x.fst = 0}) ∧
    ((∀ u, b u u = 0 → u = 0) →
      {x : BinExt b | x ^ 2 = 1} = (centerSub b : Set (BinExt b)) ∧
        (centerSub b).Characteristic) := by
  have hsq1 : ∀ x : BinExt b, x ^ 2 = 1 ↔ b x.fst x.fst = 0 := fun x => by
    rw [sq_def, one_def]
    exact ⟨fun h => congrArg BinExt.snd h, fun h => by rw [h]⟩
  have hcen : (Subgroup.center (BinExt b) : Set (BinExt b)) =
      {x | ∀ v : U, b x.fst v + b v x.fst = 0} := by
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_center_iff, Set.mem_ofPred_eq]
    constructor
    · intro h v
      have h1 := h ⟨v, 0⟩
      have h2 := congrArg BinExt.snd h1
      simp only [mul_def] at h2
      rw [← sub_eq_zero] at h2
      have : (0 : W) + x.snd + b v x.fst - (x.snd + 0 + b x.fst v) =
          b v x.fst - b x.fst v := by abel
      rw [this, sub_eq_zero] at h2
      rw [h2, add_self_zmod]
    · intro h y
      ext
      · exact add_comm _ _
      · change y.snd + x.snd + b y.fst x.fst = x.snd + y.snd + b x.fst y.fst
        have h1 := h y.fst
        have : b y.fst x.fst = b x.fst y.fst := by
          rw [← sub_eq_zero, sub_eq_add_neg, show -b x.fst y.fst = b x.fst y.fst from
            neg_eq_iff_add_eq_zero.2 (add_self_zmod _)]
          rw [add_comm]
          exact h1
        rw [this, add_comm y.snd]
  have hWc : centerSub b ≤ Subgroup.center (BinExt b) := by
    intro x hx
    rw [mem_centerSub] at hx
    rw [← SetLike.mem_coe, hcen]
    intro v
    simp [hx]
  have hrange : (iotaHom b).range = centerSub b := by
    ext x
    rw [MonoidHom.mem_range, mem_centerSub]
    constructor
    · rintro ⟨w, rfl⟩
      rfl
    · intro hx
      exact ⟨Multiplicative.ofAdd x.snd, BinExt.ext hx.symm rfl⟩
  have hsurj : Function.Surjective (piHom b) := fun u => ⟨⟨u.toAdd, 0⟩, rfl⟩
  have hcard : Nat.card (BinExt b) = Nat.card U * Nat.card W := by
    rw [← Nat.card_prod]
    exact Nat.card_congr ⟨fun x => (x.fst, x.snd), fun p => ⟨p.1, p.2⟩, fun _ => rfl,
      fun _ => rfl⟩
  have hU : Nat.card U = 2 ^ Module.finrank (ZMod 2) U := by
    have : Finite U := Module.finite_of_finite (ZMod 2)
    let _ := Fintype.ofFinite U
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have hW : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
    have : Finite W := Module.finite_of_finite (ZMod 2)
    let _ := Fintype.ofFinite W
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  refine ⟨fun _ _ => rfl, by rw [hcard, hU, hW, pow_add], rfl, inv_def,
    fun w z h => congrArg BinExt.snd h, hrange, ?_, hWc, fun _ => rfl, hsurj, rfl,
    ⟨QuotientGroup.quotientKerEquivOfSurjective _ hsurj⟩, fun x => ?_, sq_def,
    commutator_def, hcen, fun hb => ?_⟩
  · ext x
    exact mem_centerSub
  · rw [show 4 = 2 * 2 from rfl, pow_mul, sq_def, sq_def]
    ext
    · rfl
    · change b 0 0 = 0
      simp
  · have hset : {x : BinExt b | x ^ 2 = 1} = (centerSub b : Set (BinExt b)) := by
      ext x
      rw [Set.mem_ofPred_eq, hsq1, SetLike.mem_coe, mem_centerSub]
      exact ⟨hb _, fun h => by rw [h]; simp⟩
    refine ⟨hset, ⟨fun φ => ?_⟩⟩
    ext x
    rw [Subgroup.mem_comap]
    have key : ∀ y : BinExt b, y ∈ centerSub b ↔ y ^ 2 = 1 := fun y => by
      rw [← SetLike.mem_coe, ← hset, Set.mem_ofPred_eq]
    rw [key, key, ← map_pow]
    exact ⟨fun h => φ.injective (h.trans (map_one φ).symm), fun h => by rw [h, map_one]⟩

end CFSG.LocalAnalysis.ComponentInitial
