module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Module.ZMod
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWOne
import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix

structure ElemBasis {G : Type*} [Group G] (V : Subgroup G) (m : ℕ) where
  toFun : (Fin m → ZMod 2) → G
  map_add' : ∀ x y, toFun (x + y) = toFun x * toFun y
  mem' : ∀ x, toFun x ∈ V
  injective' : Function.Injective toFun
  surj' : ∀ v ∈ V, ∃ x, toFun x = v

namespace ElemBasis

variable {G : Type*} [Group G] {V : Subgroup G} {m : ℕ}

instance : CoeFun (ElemBasis V m) (fun _ => (Fin m → ZMod 2) → G) :=
  ⟨ElemBasis.toFun⟩

variable (b : ElemBasis V m)

theorem map_add (x y : Fin m → ZMod 2) : b (x + y) = b x * b y :=
  b.map_add' x y

theorem mem (x : Fin m → ZMod 2) : b x ∈ V :=
  b.mem' x

theorem injective : Function.Injective b :=
  b.injective'

theorem exists_eq {v : G} (hv : v ∈ V) : ∃ x, b x = v :=
  b.surj' v hv

theorem map_zero : b 0 = 1 := by
  have h := b.map_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem eq_one_iff {x : Fin m → ZMod 2} : b x = 1 ↔ x = 0 :=
  ⟨fun h => b.injective (h.trans b.map_zero.symm), fun h => h ▸ b.map_zero⟩

@[expose] noncomputable def mulEquiv : Multiplicative (Fin m → ZMod 2) ≃* V :=
  MulEquiv.ofBijective
    ({ toFun := fun x => ⟨b x.toAdd, b.mem _⟩
       map_one' := Subtype.ext b.map_zero
       map_mul' := fun x y => Subtype.ext (b.map_add x.toAdd y.toAdd) } :
      Multiplicative (Fin m → ZMod 2) →* V)
    ⟨fun x y h => b.injective (congrArg Subtype.val h), fun v => by
      obtain ⟨x, hx⟩ := b.exists_eq v.2
      exact ⟨Multiplicative.ofAdd x, Subtype.ext hx⟩⟩

theorem mulEquiv_symm_apply (x : Fin m → ZMod 2) :
    b.mulEquiv.symm ⟨b x, b.mem x⟩ = Multiplicative.ofAdd x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

@[expose] noncomputable def autOfAddEquiv (f : (Fin m → ZMod 2) ≃+ (Fin m → ZMod 2)) : V ≃* V :=
  b.mulEquiv.symm.trans ((AddEquiv.toMultiplicative f).trans b.mulEquiv)

theorem autOfAddEquiv_apply (f : (Fin m → ZMod 2) ≃+ (Fin m → ZMod 2)) (x : Fin m → ZMod 2) :
    ((b.autOfAddEquiv f ⟨b x, b.mem x⟩ : V) : G) = b (f x) := by
  simp only [autOfAddEquiv, MulEquiv.trans_apply, b.mulEquiv_symm_apply]
  rfl

end ElemBasis

@[expose] def mulVecAddEquiv {m : ℕ} (M M' : Matrix (Fin m) (Fin m) (ZMod 2)) (h : M * M' = 1)
    (h' : M' * M = 1) : (Fin m → ZMod 2) ≃+ (Fin m → ZMod 2) where
  toFun x := M *ᵥ x
  invFun x := M' *ᵥ x
  left_inv x := by simp only [Matrix.mulVec_mulVec, h', Matrix.one_mulVec]
  right_inv x := by simp only [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  map_add' x y := Matrix.mulVec_add M x y

namespace ElemBasis

variable {G : Type*} [Group G] {V : Subgroup G} {m : ℕ} (b : ElemBasis V m)

@[expose] noncomputable def autOfMatrix (M M' : Matrix (Fin m) (Fin m) (ZMod 2)) (h : M * M' = 1)
    (h' : M' * M = 1) : V ≃* V :=
  b.autOfAddEquiv (mulVecAddEquiv M M' h h')

theorem autOfMatrix_apply (M M' : Matrix (Fin m) (Fin m) (ZMod 2)) (h : M * M' = 1)
    (h' : M' * M = 1) (x : Fin m → ZMod 2) :
    ((b.autOfMatrix M M' h h' ⟨b x, b.mem x⟩ : V) : G) = b (M *ᵥ x) :=
  b.autOfAddEquiv_apply _ x

theorem exists_conj_eq_of_forall_mulEquiv {L₁ : Subgroup G}
    (haut : ∀ f : V ≃* V, ∃ l ∈ L₁, ∀ v : V, ((f v : V) : G) = l * v * l⁻¹)
    (M M' : Matrix (Fin m) (Fin m) (ZMod 2)) (h : M * M' = 1) (h' : M' * M = 1) :
    ∃ l ∈ L₁, ∀ x, l * b x * l⁻¹ = b (M *ᵥ x) := by
  obtain ⟨l, hl, hlf⟩ := haut (b.autOfMatrix M M' h h')
  exact ⟨l, hl, fun x => (hlf ⟨b x, b.mem x⟩).symm.trans (b.autOfMatrix_apply M M' h h' x)⟩

end ElemBasis

section Existence

variable {G : Type*} [Group G] {V : Subgroup G} {m : ℕ}

theorem exists_elemBasis (hV : Nat.card V = 2 ^ m) (h2 : ∀ v ∈ V, v * v = 1) :
    Nonempty (ElemBasis V m) := by
  let _ : CommGroup V :=
    { (inferInstance : Group V) with
      mul_comm := fun a b => Subtype.ext (mul_comm_of_forall_mul_self_eq_one h2 a.2 b.2) }
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    exact congrArg Additive.ofMul (Subtype.ext (h2 _ x.toMul.2))
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; positivity)
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod 2) (Additive V) = m := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod, show Nat.card (Additive V) = Nat.card V from rfl, hV] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  let bs := Module.finBasisOfFinrankEq (ZMod 2) (Additive V) hfr
  let e := bs.equivFun.symm
  exact ⟨{ toFun := fun x => ((Additive.toMul (e x) : V) : G)
           map_add' := fun x y => by rw [map_add]; rfl
           mem' := fun x => (Additive.toMul (e x)).2
           injective' := fun x y h => e.injective (Additive.toMul.injective (Subtype.ext h))
           surj' := fun v hv => ⟨e.symm (Additive.ofMul ⟨v, hv⟩), by
             rw [LinearEquiv.apply_symm_apply]
             rfl⟩ }⟩

theorem exists_linearEquiv_apply_eq_of_ne_zero {K E : Type*} [Field K] [AddCommGroup E]
    [Module K E] [FiniteDimensional K E] {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : E ≃ₗ[K] E, g x = y := by
  let f := (LinearEquiv.toSpanNonzeroSingleton K E x hx).symm.trans
    (LinearEquiv.toSpanNonzeroSingleton K E y hy)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g, ?_⟩
  have h1 : (LinearEquiv.toSpanNonzeroSingleton K E x hx).symm
      ⟨x, Submodule.mem_span_singleton_self x⟩ = 1 := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.toSpanNonzeroSingleton_apply]
    simp
  have h2 := hg ⟨x, Submodule.mem_span_singleton_self x⟩
  rw [← h2]
  simp only [f, LinearEquiv.trans_apply, h1, LinearEquiv.toSpanNonzeroSingleton_apply, one_smul]

theorem exists_mulEquiv_apply_eq (hV : Nat.card V = 2 ^ m) (h2 : ∀ v ∈ V, v * v = 1) {v w : G}
    (hv : v ∈ V) (hw : w ∈ V) (hv1 : v ≠ 1) (hw1 : w ≠ 1) :
    ∃ f : V ≃* V, ((f ⟨v, hv⟩ : V) : G) = w := by
  obtain ⟨b⟩ := exists_elemBasis hV h2
  obtain ⟨x, rfl⟩ := b.exists_eq hv
  obtain ⟨y, rfl⟩ := b.exists_eq hw
  have hx : x ≠ 0 := fun h => hv1 (b.eq_one_iff.2 h)
  have hy : y ≠ 0 := fun h => hw1 (b.eq_one_iff.2 h)
  obtain ⟨g, hg⟩ := exists_linearEquiv_apply_eq_of_ne_zero (K := ZMod 2) hx hy
  refine ⟨b.autOfAddEquiv g.toAddEquiv, ?_⟩
  rw [b.autOfAddEquiv_apply]
  exact congrArg b hg

theorem exists_conj_eq_of_forall_mulEquiv' (hV : Nat.card V = 2 ^ m) (h2 : ∀ v ∈ V, v * v = 1)
    {L₁ : Subgroup G} (haut : ∀ f : V ≃* V, ∃ l ∈ L₁, ∀ v : V, ((f v : V) : G) = l * v * l⁻¹)
    {v w : G} (hv : v ∈ V) (hw : w ∈ V) (hv1 : v ≠ 1) (hw1 : w ≠ 1) :
    ∃ l ∈ L₁, l * v * l⁻¹ = w := by
  obtain ⟨f, hf⟩ := exists_mulEquiv_apply_eq hV h2 hv hw hv1 hw1
  obtain ⟨l, hl, hlf⟩ := haut f
  exact ⟨l, hl, (hlf ⟨v, hv⟩).symm.trans hf⟩

end Existence

end CFSG.SeitzReduction.LinearPilot
