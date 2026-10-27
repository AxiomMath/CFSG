module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

open scoped commutatorElement

namespace CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3

open CFSG

@[ext] structure Heis (F : Type*) where
  a : F
  b : F
  c : F

namespace Heis

section Group

variable {F : Type*} [CommRing F]

instance : Mul (Heis F) := ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c + x.a * y.b⟩⟩
instance : One (Heis F) := ⟨⟨0, 0, 0⟩⟩
instance : Inv (Heis F) := ⟨fun x => ⟨-x.a, -x.b, -x.c + x.a * x.b⟩⟩

@[simp] theorem mul_a (x y : Heis F) : (x * y).a = x.a + y.a := rfl
@[simp] theorem mul_b (x y : Heis F) : (x * y).b = x.b + y.b := rfl
@[simp] theorem mul_c (x y : Heis F) : (x * y).c = x.c + y.c + x.a * y.b := rfl
@[simp] theorem one_a : (1 : Heis F).a = 0 := rfl
@[simp] theorem one_b : (1 : Heis F).b = 0 := rfl
@[simp] theorem one_c : (1 : Heis F).c = 0 := rfl
@[simp] theorem inv_a (x : Heis F) : (x⁻¹).a = -x.a := rfl
@[simp] theorem inv_b (x : Heis F) : (x⁻¹).b = -x.b := rfl
@[simp] theorem inv_c (x : Heis F) : (x⁻¹).c = -x.c + x.a * x.b := rfl

instance : Group (Heis F) :=
  Group.ofLeftAxioms
    (fun x y z => by ext <;> simp <;> ring)
    (fun x => by ext <;> simp)
    (fun x => by ext <;> simp)

theorem commutator_eq (x y : Heis F) :
    ⁅x, y⁆ = (⟨0, 0, x.a * y.b - y.a * x.b⟩ : Heis F) := by
  rw [commutatorElement_def]
  ext <;> simp
  ring

theorem pow_a (x : Heis F) (k : ℕ) : (x ^ k).a = k * x.a := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; simp [ih]; ring

theorem pow_b (x : Heis F) (k : ℕ) : (x ^ k).b = k * x.b := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; simp [ih]; ring

theorem pow_c (x : Heis F) (k : ℕ) :
    (x ^ k).c = k * x.c + (Nat.choose k 2 : F) * (x.a * x.b) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    simp only [mul_c, ih, pow_a]
    rw [Nat.choose_succ_succ k 1]
    push_cast
    simp [Nat.choose_one_right]
    ring

theorem mem_center {x : Heis F} :
    x ∈ Subgroup.center (Heis F) ↔ x.a = 0 ∧ x.b = 0 := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h
    have h1 := congrArg Heis.c (h ⟨1, 0, 0⟩)
    have h2 := congrArg Heis.c (h ⟨0, 1, 0⟩)
    simp at h1 h2
    exact ⟨h2, h1⟩
  · rintro ⟨ha, hb⟩ g
    ext <;> simp [ha, hb]
    ring

theorem commutator_eq_center :
    ⁅(⊤ : Subgroup (Heis F)), ⊤⁆ = Subgroup.center (Heis F) := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x _ y _
    rw [mem_center, commutator_eq]
    simp
  · intro z hz
    rw [mem_center] at hz
    have : z = ⁅(⟨1, 0, 0⟩ : Heis F), ⟨0, z.c, 0⟩⁆ := by
      rw [commutator_eq]
      ext <;> simp [hz.1, hz.2]
    rw [this]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem pow_prime_eq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP F p] (x : Heis F) :
    x ^ p = 1 := by
  have hch : (Nat.choose p 2 : F) = 0 :=
    (CharP.cast_eq_zero_iff F p _).mpr
      (hp.dvd_choose_self (by norm_num) (by have := hp.two_le; omega))
  ext
  · simp [pow_a]
  · simp [pow_b]
  · simp [pow_c, hch]

end Group

section Card

variable {F : Type*}

def equivProd : Heis F ≃ F × F × F where
  toFun x := (x.a, x.b, x.c)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_eq : Nat.card (Heis F) = Nat.card F ^ 3 := by
  rw [Nat.card_congr equivProd, Nat.card_prod, Nat.card_prod]
  ring

end Card

section Center

variable {F : Type*} [CommRing F]

def centerEquiv : Subgroup.center (Heis F) ≃ F where
  toFun z := z.1.c
  invFun c := ⟨⟨0, 0, c⟩, by rw [mem_center]; simp⟩
  left_inv z := by
    apply Subtype.ext
    obtain ⟨z, hz⟩ := z
    rw [mem_center] at hz
    ext <;> simp [hz.1, hz.2]
  right_inv c := rfl

theorem card_center : Nat.card (Subgroup.center (Heis F)) = Nat.card F :=
  Nat.card_congr centerEquiv

end Center

section Field

variable {F : Type*} [Field F]

theorem exists_line (E : Subgroup (Heis F)) (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    ∃ v : F × F, ∀ x ∈ E, ∃ t : F, (x.a, x.b) = t • v := by
  by_cases h : ∃ x₀ ∈ E, (x₀.a, x₀.b) ≠ 0
  · obtain ⟨x₀, hx₀, hne⟩ := h
    refine ⟨(x₀.a, x₀.b), fun x hx => ?_⟩
    have hc := congrArg Heis.c (hE x hx x₀ hx₀)
    simp only [mul_c] at hc
    have key : x.a * x₀.b = x₀.a * x.b := by linear_combination hc
    by_cases ha : x₀.a = 0
    · have hb : x₀.b ≠ 0 := by
        intro hb
        exact hne (by simp [ha, hb])
      refine ⟨x.b / x₀.b, ?_⟩
      have hxa : x.a = 0 := by
        rw [ha, zero_mul] at key
        exact (mul_eq_zero.mp key).resolve_right hb
      ext
      · simp [ha, hxa]
      · simp; field_simp
    · refine ⟨x.a / x₀.a, ?_⟩
      ext
      · simp; field_simp
      · simp only [Prod.smul_mk, smul_eq_mul]
        field_simp
        linear_combination (-1 : F) * key
  · push Not at h
    refine ⟨0, fun x hx => ⟨0, ?_⟩⟩
    simpa using h x hx

theorem card_le_sq [Finite F] (E : Subgroup (Heis F)) (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    Nat.card E ≤ Nat.card F ^ 2 := by
  obtain ⟨v, hv⟩ := exists_line E hE
  choose t ht using hv
  let f : E → F × F := fun x => (t x.1 x.2, x.1.c)
  have hf : Function.Injective f := by
    intro x y hxy
    simp only [f, Prod.mk.injEq] at hxy
    apply Subtype.ext
    have h1 : ((x : Heis F).a, (x : Heis F).b) = ((y : Heis F).a, (y : Heis F).b) := by
      rw [ht _ x.2, ht _ y.2, hxy.1]
    ext
    · exact congrArg Prod.fst h1
    · exact congrArg Prod.snd h1
    · exact hxy.2
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, ← sq] at this

theorem le_index [Finite F] (E : Subgroup (Heis F)) (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    Nat.card F ≤ E.index := by
  have h1 := card_le_sq E hE
  have h2 := E.index_mul_card
  rw [card_eq] at h2
  have hq : 0 < Nat.card F := Nat.card_pos
  have : Nat.card F ^ 2 * Nat.card F ≤ Nat.card F ^ 2 * E.index := by
    calc Nat.card F ^ 2 * Nat.card F = Nat.card F ^ 3 := by ring
      _ = E.index * Nat.card E := h2.symm
      _ ≤ E.index * Nat.card F ^ 2 := Nat.mul_le_mul_left _ h1
      _ = Nat.card F ^ 2 * E.index := by ring
  exact Nat.le_of_mul_le_mul_left this (by positivity)

theorem frattini_eq_commutator {p : ℕ} (hp : p.Prime) [Finite F] (hQp : IsPGroup p (Heis F))
    (hexp : ∀ x : Heis F, x ^ p = 1) : frattini (Heis F) = _root_.commutator (Heis F) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p (Heis F)) := ⟨hQp⟩
  have : Finite (Heis F) := Finite.of_equiv _ equivProd.symm
  rw [CFSG.frattini_eq_closure_commutator_union_powers (p := p)]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro y (hy | ⟨x, rfl⟩)
    · exact hy
    · show x ^ p ∈ _root_.commutator (Heis F)
      rw [hexp x]
      exact one_mem _
  · exact fun y hy => Subgroup.subset_closure (Or.inl hy)

end Field

end Heis

@[expose] def SpecialP (p n : ℕ) (H : Type) [Group H] : Prop :=
  (∀ E : Subgroup H, IsElementaryAbelian p ↥E → p ^ n ≤ E.index ∧ Nat.card ↥E ≤ p ^ (2 * n)) ∧
    Subgroup.center H = ⁅(⊤ : Subgroup H), ⊤⁆ ∧ Subgroup.center H = frattini H ∧
      IsElementaryAbelian p ↥(Subgroup.center H) ∧ Nat.card ↥(Subgroup.center H) = p ^ n

theorem Heis.specialP {F : Type} [Field F] [Finite F] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    [CharP F p] (hF : Nat.card F = p ^ n) : SpecialP p n (Heis F) := by
  have hpg : IsPGroup p (Heis F) :=
    IsPGroup.of_card (n := n * 3) (by rw [Heis.card_eq, hF, pow_mul])
  refine ⟨fun E hE => ?_, Heis.commutator_eq_center.symm, ?_, ?_, ?_⟩
  · have := hE.toIsMulCommutative
    have hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
    refine ⟨?_, ?_⟩
    · rw [← hF]
      exact Heis.le_index E hc
    · rw [pow_mul', ← hF]
      exact Heis.card_le_sq E hc
  · rw [Heis.frattini_eq_commutator hp hpg (Heis.pow_prime_eq_one hp hp2), commutator_def,
      Heis.commutator_eq_center]
  · exact
      { toIsMulCommutative := inferInstance
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
          Subtype.ext (Heis.pow_prime_eq_one hp hp2 g.1) }
  · rw [Heis.card_center, hF]

theorem map_center_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (Subgroup.center A).map e.toMonoidHom = Subgroup.center B := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  simp only [Subgroup.mem_map, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨z, hz, hzx⟩ g
    obtain ⟨w, rfl⟩ := e.surjective g
    obtain rfl : z = x := e.injective hzx
    simpa using congrArg e (hz w)
  · intro h
    refine ⟨x, fun g => e.injective ?_, rfl⟩
    simpa using h (e g)

theorem map_frattini_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (frattini A).map e.toMonoidHom = frattini B :=
  OrderIso.map_radical (MulEquiv.mapSubgroup e)

theorem map_commutator_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Subgroup.map e.toMonoidHom ⁅(⊤ : Subgroup A), ⊤⁆ = ⁅(⊤ : Subgroup B), ⊤⁆ := by
  rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective]

theorem map_map_symm {A B : Type*} [Group A] [Group B] (e : A ≃* B) (E : Subgroup B) :
    (E.map e.symm.toMonoidHom).map e.toMonoidHom = E := by
  rw [Subgroup.map_map]
  have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id B := by ext x; simp
  rw [this, Subgroup.map_id]

theorem specialP_of_mulEquiv {p n : ℕ} [Fact p.Prime] {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (h : SpecialP p n A) : SpecialP p n B := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hc := map_center_mulEquiv e
  refine ⟨fun E' hE' => ?_, ?_, ?_, ?_, ?_⟩
  · have hE : IsElementaryAbelian p ↥(E'.map e.symm.toMonoidHom) := by
      have := hE'
      exact IsElementaryAbelian.map e.symm.toMonoidHom
    obtain ⟨i1, i2⟩ := h1 _ hE
    have hi : ((E'.map e.symm.toMonoidHom).map e.toMonoidHom).index =
        (E'.map e.symm.toMonoidHom).index := Subgroup.index_map_equiv _ e
    have hcard : Nat.card ((E'.map e.symm.toMonoidHom).map e.toMonoidHom) =
        Nat.card (E'.map e.symm.toMonoidHom) := Subgroup.card_map_of_injective e.injective
    rw [map_map_symm] at hi hcard
    exact ⟨hi ▸ i1, hcard ▸ i2⟩
  · rw [← hc, h2, map_commutator_mulEquiv e]
  · rw [← hc, h3, map_frattini_mulEquiv e]
  · rw [← hc]
    have := h4
    exact IsElementaryAbelian.map e.toMonoidHom
  · rw [← hc, Subgroup.card_map_of_injective e.injective, h5]

end CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3
