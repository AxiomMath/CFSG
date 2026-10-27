module

public import CFSG.Quasithin.Recognition.CertF8
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.AGLEmbedding.ChevOuter

open CFSG.Quasithin

structure GF64 where
  lo : GF8
  hi : GF8

namespace GF64

instance : DecidableEq GF64 := fun a b =>
  if h : a.lo = b.lo ∧ a.hi = b.hi then isTrue (by cases a; cases b; simp_all)
  else isFalse (fun e => h (by subst e; exact ⟨rfl, rfl⟩))

@[ext] theorem ext {a b : GF64} (h1 : a.lo = b.lo) (h2 : a.hi = b.hi) : a = b := by
  cases a; cases b; simp_all

instance : Zero GF64 := ⟨⟨0, 0⟩⟩

instance : One GF64 := ⟨⟨1, 0⟩⟩

instance : Add GF64 := ⟨fun a b => ⟨a.lo + b.lo, a.hi + b.hi⟩⟩

instance : Neg GF64 := ⟨fun a => ⟨-a.lo, -a.hi⟩⟩

instance : Mul GF64 :=
  ⟨fun a b => ⟨a.lo * b.lo + a.hi * b.hi, a.lo * b.hi + a.hi * b.lo + a.hi * b.hi⟩⟩

@[expose] def norm (a : GF64) : GF8 := a.lo * a.lo + a.lo * a.hi + a.hi * a.hi

instance : Inv GF64 :=
  ⟨fun a => ⟨(norm a)⁻¹ * (a.lo + a.hi), (norm a)⁻¹ * a.hi⟩⟩

instance : Fintype GF64 :=
  Fintype.ofEquiv (GF8 × GF8) ⟨fun p => ⟨p.1, p.2⟩, fun a => (a.lo, a.hi), fun _ => rfl,
    fun _ => rfl⟩

theorem lo_mul (a b : GF64) : (a * b).lo = a.lo * b.lo + a.hi * b.hi := rfl

theorem hi_mul (a b : GF64) : (a * b).hi = a.lo * b.hi + a.hi * b.lo + a.hi * b.hi := rfl

theorem lo_add (a b : GF64) : (a + b).lo = a.lo + b.lo := rfl

theorem hi_add (a b : GF64) : (a + b).hi = a.hi + b.hi := rfl

theorem mul_inv_cancel_aux :
    ∀ u v : GF8, (⟨u, v⟩ : GF64) ≠ 0 → (⟨u, v⟩ : GF64) * ⟨u, v⟩⁻¹ = 1 := by
  decide

instance : Field GF64 :=
  Field.ofMinimalAxioms GF64
    (fun a b c => ext (add_assoc _ _ _) (add_assoc _ _ _))
    (fun a => ext (zero_add _) (zero_add _))
    (fun a => ext (neg_add_cancel _) (neg_add_cancel _))
    (fun a b c => ext (by simp only [lo_mul, hi_mul]; ring) (by simp only [lo_mul, hi_mul]; ring))
    (fun a b => ext (by simp only [lo_mul]; ring) (by simp only [hi_mul]; ring))
    (fun a => ext (by show 1 * a.lo + 0 * a.hi = a.lo; ring)
      (by show 1 * a.hi + 0 * a.lo + 0 * a.hi = a.hi; ring))
    (fun a ha => by
      obtain ⟨u, v⟩ := a
      exact mul_inv_cancel_aux u v ha)
    (by decide)
    (fun a b c => ext (by simp only [lo_mul, lo_add, hi_add]; ring)
      (by simp only [hi_mul, lo_add, hi_add]; ring))
    ⟨0, 1, by decide⟩

theorem two_eq_zero8 : (2 : GF8) = 0 := by decide

theorem two_eq_zero : (2 : GF64) = 0 := by decide

instance : CharP GF64 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero two_eq_zero

theorem card_eq : Nat.card GF64 = 64 := by
  rw [Nat.card_congr (show GF64 ≃ GF8 × GF8 from
    ⟨fun a => (a.lo, a.hi), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩), Nat.card_prod,
    Nat.card_eq_fintype_card (α := GF8)]
  rfl

@[expose] def toNat (a : GF64) : ℕ := a.lo.toNat + 8 * a.hi.toNat

@[expose] def ofNat' (n : ℕ) : GF64 := ⟨GF8.ofNat' n, GF8.ofNat' (n / 8)⟩

theorem ofNat'_toNat : ∀ a : GF64, ofNat' a.toNat = a := by decide +kernel

theorem toNat_ofNat' : ∀ n : Fin 64, (ofNat' n.val).toNat = n.val := by decide +kernel

theorem toNat_lt : ∀ a : GF64, a.toNat < 64 := by decide +kernel

@[expose] def sq8 : GF8 →+* GF8 where
  toFun a := a * a
  map_one' := by decide
  map_mul' := by decide
  map_zero' := by decide
  map_add' := by decide

@[expose] def sigma2 : GF64 →+* GF64 where
  toFun a := ⟨sq8 (sq8 a.lo), sq8 (sq8 a.hi)⟩
  map_one' := by
    refine GF64.ext ?_ ?_ <;>
      simp [show (1 : GF64).lo = 1 from rfl, show (1 : GF64).hi = 0 from rfl]
  map_mul' a b := by
    refine GF64.ext ?_ ?_
    · simp only [GF64.lo_mul, map_add, map_mul]
    · simp only [GF64.hi_mul, map_add, map_mul]
  map_zero' := by
    refine GF64.ext ?_ ?_ <;>
      simp [show (0 : GF64).lo = 0 from rfl, show (0 : GF64).hi = 0 from rfl]
  map_add' a b := by
    refine GF64.ext ?_ ?_
    · simp only [GF64.lo_add, map_add]
    · simp only [GF64.hi_add, map_add]

@[expose] def barC : GF64 →+* GF64 where
  toFun a := ⟨a.lo + a.hi, a.hi⟩
  map_one' := by
    refine GF64.ext ?_ ?_ <;>
      simp [show (1 : GF64).lo = 1 from rfl, show (1 : GF64).hi = 0 from rfl]
  map_mul' a b := by
    refine GF64.ext ?_ ?_
    · simp only [GF64.lo_mul, GF64.hi_mul]
      ring
    · simp only [GF64.hi_mul]
      linear_combination (-(a.hi * b.hi)) * two_eq_zero8
  map_zero' := by
    refine GF64.ext ?_ ?_ <;>
      simp [show (0 : GF64).lo = 0 from rfl, show (0 : GF64).hi = 0 from rfl]
  map_add' a b := by
    refine GF64.ext ?_ ?_
    · simp only [GF64.lo_add, GF64.hi_add]
      ring
    · simp only [GF64.hi_add]

theorem barC_eq_pow : ∀ a : GF64, barC a = a ^ 8 := by decide +kernel

theorem sigma2_eq_pow : ∀ a : GF64, sigma2 a = a ^ 4 := by decide +kernel

theorem sigma2_cube : ∀ a : GF64, sigma2 (sigma2 (sigma2 a)) = a := by decide +kernel

@[expose] def sigma2Equiv : GF64 ≃+* GF64 :=
  RingEquiv.ofRingHom sigma2 (sigma2.comp sigma2) (RingHom.ext fun a => sigma2_cube a)
    (RingHom.ext fun a => sigma2_cube a)

end GF64

end CFSG.AGLEmbedding.ChevOuter
