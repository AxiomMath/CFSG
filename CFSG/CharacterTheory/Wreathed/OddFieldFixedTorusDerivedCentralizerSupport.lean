module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SemidirectProduct
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Wreathed.OddFieldTorus

open Matrix

@[expose] def J₀ (L : Type*) [CommRing L] : Matrix.SpecialLinearGroup (Fin 2) L :=
  ⟨!![0, -1; 1, 0], by simp [det_fin_two]⟩

abbrev torus (L : Type*) [CommRing L] : Subgroup (Matrix.SpecialLinearGroup (Fin 2) L) :=
  Subgroup.centralizer {J₀ L}

section Torus

variable {L : Type*} [CommRing L]

theorem J₀_coe : (J₀ L : Matrix (Fin 2) (Fin 2) L) = !![0, -1; 1, 0] := rfl

theorem SL_coe_mul (A B : Matrix.SpecialLinearGroup (Fin 2) L) :
    ((A * B : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      (A : Matrix (Fin 2) (Fin 2) L) * (B : Matrix (Fin 2) (Fin 2) L) := rfl

theorem SL_coe_one :
    ((1 : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = 1 := rfl

theorem SL_ext {A B : Matrix.SpecialLinearGroup (Fin 2) L}
    (h : (A : Matrix (Fin 2) (Fin 2) L) = (B : Matrix (Fin 2) (Fin 2) L)) : A = B :=
  Subtype.ext h

theorem mem_torus_coord_iff (g : Matrix.SpecialLinearGroup (Fin 2) L) :
    g ∈ torus L ↔ (g : Matrix (Fin 2) (Fin 2) L) 1 1 = (g : Matrix (Fin 2) (Fin 2) L) 0 0 ∧
      (g : Matrix (Fin 2) (Fin 2) L) 0 1 = -(g : Matrix (Fin 2) (Fin 2) L) 1 0 := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hm := congrArg
      (fun M : Matrix.SpecialLinearGroup (Fin 2) L => (M : Matrix (Fin 2) (Fin 2) L)) h
    simp only [SL_coe_mul, J₀_coe] at hm
    have h00 := congrFun (congrFun hm 0) 0
    have h01 := congrFun (congrFun hm 0) 1
    simp only [mul_apply, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero, cons_val_one,
      empty_val', cons_val_fin_one] at h00 h01
    constructor
    · linear_combination h01
    · linear_combination h00
  · rintro ⟨h1, h2⟩
    apply SL_ext
    rw [SL_coe_mul, SL_coe_mul, J₀_coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [mul_apply, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero, cons_val_one,
        empty_val', cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue, h1, h2] <;> ring

theorem torus_sq_add_sq {g : Matrix.SpecialLinearGroup (Fin 2) L} (hg : g ∈ torus L) :
    (g : Matrix (Fin 2) (Fin 2) L) 0 0 ^ 2 + (g : Matrix (Fin 2) (Fin 2) L) 1 0 ^ 2 = 1 := by
  obtain ⟨h1, h2⟩ := (mem_torus_coord_iff g).mp hg
  have h := g.2
  rw [det_fin_two, h1, h2] at h
  linear_combination h

theorem mem_torus_iff (g : Matrix.SpecialLinearGroup (Fin 2) L) :
    g ∈ torus L ↔ ∃ v w : L, v ^ 2 + w ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) L) = !![v, -w; w, v] := by
  constructor
  · intro hg
    obtain ⟨h1, h2⟩ := (mem_torus_coord_iff g).mp hg
    refine ⟨_, _, torus_sq_add_sq hg, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, h2]
  · rintro ⟨v, w, -, hg⟩
    rw [mem_torus_coord_iff, hg]
    simp

@[expose] def rot (v w : L) (h : v ^ 2 + w ^ 2 = 1) : Matrix.SpecialLinearGroup (Fin 2) L :=
  ⟨!![v, -w; w, v], by rw [det_fin_two_of]; linear_combination h⟩

theorem rot_mem (v w : L) (h : v ^ 2 + w ^ 2 = 1) : rot v w h ∈ torus L :=
  (mem_torus_iff _).mpr ⟨v, w, h, rfl⟩

theorem rot_coe (v w : L) (h : v ^ 2 + w ^ 2 = 1) :
    (rot v w h : Matrix (Fin 2) (Fin 2) L) = !![v, -w; w, v] := rfl

theorem torus_mul_00 {g h : Matrix.SpecialLinearGroup (Fin 2) L} (hg : g ∈ torus L) :
    ((g * h : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 =
      (g : Matrix (Fin 2) (Fin 2) L) 0 0 * (h : Matrix (Fin 2) (Fin 2) L) 0 0 -
        (g : Matrix (Fin 2) (Fin 2) L) 1 0 * (h : Matrix (Fin 2) (Fin 2) L) 1 0 := by
  obtain ⟨-, h2⟩ := (mem_torus_coord_iff g).mp hg
  rw [SL_coe_mul, mul_apply, Fin.sum_univ_two, h2]
  ring

theorem torus_mul_10 {g h : Matrix.SpecialLinearGroup (Fin 2) L} (hg : g ∈ torus L) :
    ((g * h : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 =
      (g : Matrix (Fin 2) (Fin 2) L) 1 0 * (h : Matrix (Fin 2) (Fin 2) L) 0 0 +
        (g : Matrix (Fin 2) (Fin 2) L) 0 0 * (h : Matrix (Fin 2) (Fin 2) L) 1 0 := by
  obtain ⟨h1, -⟩ := (mem_torus_coord_iff g).mp hg
  rw [SL_coe_mul, mul_apply, Fin.sum_univ_two, h1]

theorem torus_ext {g h : Matrix.SpecialLinearGroup (Fin 2) L} (hg : g ∈ torus L)
    (hh : h ∈ torus L)
    (h0 : (g : Matrix (Fin 2) (Fin 2) L) 0 0 = (h : Matrix (Fin 2) (Fin 2) L) 0 0)
    (h1 : (g : Matrix (Fin 2) (Fin 2) L) 1 0 = (h : Matrix (Fin 2) (Fin 2) L) 1 0) : g = h := by
  obtain ⟨g1, g2⟩ := (mem_torus_coord_iff g).mp hg
  obtain ⟨k1, k2⟩ := (mem_torus_coord_iff h).mp hh
  apply SL_ext
  ext i j
  fin_cases i <;> fin_cases j
  · exact h0
  · simp only [Fin.zero_eta, Fin.mk_one]
    rw [g2, k2, h1]
  · exact h1
  · simp only [Fin.mk_one]
    rw [g1, k1, h0]

end Torus

section Structure

variable {L : Type*} [Field L]

@[expose] def torusToField (i : L) (hi : i * i = -1) : torus L →* L where
  toFun g := ((g : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 +
    i * ((g : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0
  map_one' := by simp
  map_mul' g h := by
    change ((g * h : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 +
        i * ((g * h : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = _
    rw [torus_mul_00 g.2, torus_mul_10 g.2]
    linear_combination
      (-(((g : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 *
        ((h : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0)) * hi

@[expose] def torusToQuad : torus L →* QuadraticAlgebra L (-1) 0 where
  toFun g := ⟨((g : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0,
    ((g : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0⟩
  map_one' := by
    ext
    · simp [QuadraticAlgebra.re_one]
    · simp [QuadraticAlgebra.im_one]
  map_mul' g h := by
    ext
    · change ((g * h : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = _
      rw [torus_mul_00 g.2, QuadraticAlgebra.re_mul]
      ring
    · change ((g * h : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = _
      rw [torus_mul_10 g.2, QuadraticAlgebra.im_mul]
      ring

theorem torusToQuad_injective : Function.Injective (torusToQuad (L := L)) := by
  intro g h hgh
  apply Subtype.ext
  exact torus_ext g.2 h.2 (congrArg QuadraticAlgebra.re hgh) (congrArg QuadraticAlgebra.im hgh)

theorem norm_torusToQuad (g : torus L) : QuadraticAlgebra.norm (torusToQuad g) = 1 := by
  rw [QuadraticAlgebra.norm_def]
  have h := torus_sq_add_sq g.2
  have hre : (torusToQuad g).re =
      ((g : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 := rfl
  have him : (torusToQuad g).im =
      ((g : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 := rfl
  rw [hre, him]
  linear_combination h

theorem torusToField_injective (h2 : (2 : L) ≠ 0) (i : L) (hi : i * i = -1) :
    Function.Injective (torusToField i hi) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hg' : ((g : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 +
      i * ((g : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 1 := hg
  have hsq := torus_sq_add_sq g.2
  have hminus : ((g : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 -
      i * ((g : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 1 := by
    linear_combination
      -(((g : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 -
        i * ((g : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0) * hg' +
      hsq - ((g : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 ^ 2 * hi
  have hv : ((g : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = 1 :=
    mul_left_cancel₀ h2 (by linear_combination hg' + hminus)
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  have hw : ((g : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
    have h : i * ((g : Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 =
        0 := by
      linear_combination hg' - hv
    exact (mul_eq_zero.mp h).resolve_left hi0
  apply Subtype.ext
  apply torus_ext g.2 (Subgroup.one_mem _)
  · rw [hv]
    simp
  · rw [hw]
    simp

theorem torus_comm {g h : Matrix.SpecialLinearGroup (Fin 2) L} (hg : g ∈ torus L)
    (hh : h ∈ torus L) : g * h = h * g := by
  apply torus_ext ((torus L).mul_mem hg hh) ((torus L).mul_mem hh hg)
  · rw [torus_mul_00 hg, torus_mul_00 hh]
    ring
  · rw [torus_mul_10 hg, torus_mul_10 hh]
    ring

@[expose] def torusToUnits (i : L) (hi : i * i = -1) : torus L →* Lˣ :=
  (torusToField i hi).toHomUnits

theorem torusToUnits_bijective (h2 : (2 : L) ≠ 0) (i : L) (hi : i * i = -1) :
    Function.Bijective (torusToUnits i hi) := by
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  refine ⟨fun g h hgh => torusToField_injective h2 i hi (congrArg Units.val hgh), fun t => ?_⟩
  have ht : (t : L) ≠ 0 := t.ne_zero
  set v := ((t : L) + (t : L)⁻¹) / 2
  set w := ((t : L) - (t : L)⁻¹) / (2 * i)
  have hvw : v ^ 2 + w ^ 2 = 1 := by
    have hi2 : i ^ 2 = -1 := by rw [sq]; exact hi
    simp only [v, w]
    field_simp
    linear_combination (-4 * (t : L) ^ 2 + (1 + (t : L) ^ 2) ^ 2) * hi2
  refine ⟨⟨rot v w hvw, rot_mem v w hvw⟩, Units.ext ?_⟩
  change (rot v w hvw : Matrix (Fin 2) (Fin 2) L) 0 0 +
    i * (rot v w hvw : Matrix (Fin 2) (Fin 2) L) 1 0 = t
  simp only [rot_coe, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one, v, w]
  field_simp
  ring

theorem ringChar_ne_two (h2 : (2 : L) ≠ 0) : ringChar L ≠ 2 := by
  intro h
  apply h2
  have := ringChar.Nat.cast_ringChar (R := L)
  rw [h] at this
  exact_mod_cast this

theorem torus_card_split [Finite L] (h2 : (2 : L) ≠ 0) (i : L) (hi : i * i = -1) :
    Nat.card (torus L) = Nat.card L - 1 := by
  rw [Nat.card_congr (Equiv.ofBijective _ (torusToUnits_bijective h2 i hi)), Nat.card_units]

theorem exists_sq_add_sq [Finite L] (h2 : (2 : L) ≠ 0) (c : L) :
    ∃ a b : L, a ^ 2 + b ^ 2 = c := by
  have : Fintype L := Fintype.ofFinite L
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.X ^ 2) (g := Polynomial.X ^ 2 - Polynomial.C c)
    (Polynomial.degree_X_pow 2) (Polynomial.degree_X_pow_sub_C (by decide) c)
    (FiniteField.odd_card_of_char_ne_two (ringChar_ne_two h2))
  refine ⟨a, b, ?_⟩
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub,
    Polynomial.eval_C] at hab
  linear_combination hab

theorem torus_card_nonsplit [Finite L] (h2 : (2 : L) ≠ 0) (hsq : ¬ IsSquare (-1 : L)) :
    Nat.card (torus L) = Nat.card L + 1 := by
  have : Fact (¬ IsSquare (-1 : L)) := ⟨hsq⟩
  have : Finite (QuadraticAlgebra L (-1) 0) :=
    Finite.of_equiv _ (QuadraticAlgebra.equivProd (-1 : L) 0).symm
  let normU : (QuadraticAlgebra L (-1) 0)ˣ →* Lˣ := Units.map QuadraticAlgebra.norm
  have hsurj : Function.Surjective normU := by
    intro c
    obtain ⟨a, b, hab⟩ := exists_sq_add_sq h2 (c : L)
    have hz : (⟨a, b⟩ : QuadraticAlgebra L (-1) 0) ≠ 0 := by
      intro h
      apply c.ne_zero
      have ha := congrArg QuadraticAlgebra.re h
      have hb := congrArg QuadraticAlgebra.im h
      simp only [QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero] at ha hb
      rw [← hab, ha, hb]
      ring
    refine ⟨Units.mk0 _ hz, Units.ext ?_⟩
    change QuadraticAlgebra.norm (⟨a, b⟩ : QuadraticAlgebra L (-1) 0) = c
    rw [QuadraticAlgebra.norm_def]
    change a * a + 0 * a * b - -1 * b * b = c
    linear_combination hab
  let f : torus L → normU.ker := fun g => ⟨torusToQuad.toHomUnits g, by
    rw [MonoidHom.mem_ker]
    apply Units.ext
    exact norm_torusToQuad g⟩
  have hf : Function.Bijective f := by
    refine ⟨fun g h hgh => torusToQuad_injective
      (congrArg Units.val (congrArg Subtype.val hgh)), fun u => ?_⟩
    have hu := congrArg Units.val (MonoidHom.mem_ker.mp u.2)
    change QuadraticAlgebra.norm ((u : (QuadraticAlgebra L (-1) 0)ˣ) :
      QuadraticAlgebra L (-1) 0) = 1 at hu
    rw [QuadraticAlgebra.norm_def] at hu
    have hvw : ((u : (QuadraticAlgebra L (-1) 0)ˣ) : QuadraticAlgebra L (-1) 0).re ^ 2 +
        ((u : (QuadraticAlgebra L (-1) 0)ˣ) : QuadraticAlgebra L (-1) 0).im ^ 2 = 1 := by
      linear_combination hu
    refine ⟨⟨rot _ _ hvw, rot_mem _ _ hvw⟩, Subtype.ext (Units.ext ?_)⟩
    ext
    · rfl
    · rfl
  have hker := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [Nat.card_units, Nat.card_units, Nat.card_congr (QuadraticAlgebra.equivProd (-1 : L) 0),
    Nat.card_prod, ← Nat.card_congr (Equiv.ofBijective f hf)] at hker
  have hL : 2 ≤ Nat.card L := Finite.one_lt_card
  have h1 : Nat.card L * Nat.card L - 1 = (Nat.card L + 1) * (Nat.card L - 1) := by
    obtain ⟨r, hr⟩ : ∃ r, Nat.card L = r + 1 := ⟨Nat.card L - 1, by omega⟩
    rw [hr, Nat.add_sub_cancel]
    ring_nf
    omega
  rw [h1] at hker
  exact Nat.eq_of_mul_eq_mul_right (by omega) hker

theorem torus_isCyclic [Finite L] (h2 : (2 : L) ≠ 0) : IsCyclic (torus L) := by
  by_cases hsq : IsSquare (-1 : L)
  · obtain ⟨i, hi⟩ := hsq
    exact isCyclic_of_injective_ringHom (torusToField i hi.symm)
      (torusToField_injective h2 i hi.symm)
  · have : Fact (¬ IsSquare (-1 : L)) := ⟨hsq⟩
    exact isCyclic_of_injective_ringHom torusToQuad torusToQuad_injective

theorem torus_card [Finite L] (h2 : (2 : L) ≠ 0) :
    (Nat.card (torus L) : ℤ) = Nat.card L - if Nat.card L % 4 = 1 then 1 else -1 := by
  have : Fintype L := Fintype.ofFinite L
  have hodd := FiniteField.odd_card_of_char_ne_two (ringChar_ne_two h2)
  have hsq := FiniteField.isSquare_neg_one_iff (F := L)
  rw [Fintype.card_eq_nat_card] at hodd hsq
  by_cases h1 : Nat.card L % 4 = 1
  · obtain ⟨i, hi⟩ : IsSquare (-1 : L) := hsq.mpr (by omega)
    have hpos : 1 ≤ Nat.card L := Nat.card_pos
    rw [torus_card_split h2 i hi.symm]
    simp only [h1, ↓reduceIte]
    push_cast [hpos]
    ring
  · have hns : ¬ IsSquare (-1 : L) := fun h => (hsq.mp h) (by omega)
    rw [torus_card_nonsplit h2 hns]
    simp only [h1, ↓reduceIte]
    push_cast
    ring

end Structure

theorem card_odd_orderOf {G : Type*} [Group G] [Finite G] [IsCyclic G] (a h : ℕ)
    (hcard : Nat.card G = 2 ^ a * h) (hh : Odd h) :
    Nat.card {g : G // Odd (orderOf g)} = h := by
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
  have hpos : 0 < 2 ^ a := by positivity
  have hc : orderOf (g₀ ^ 2 ^ a) = h := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (by rw [hg₀, hcard]; exact Dvd.intro _ rfl),
      hg₀, hcard, Nat.mul_div_cancel_left _ hpos]
  have htop : Subgroup.zpowers g₀ = ⊤ :=
    (Subgroup.card_eq_iff_eq_top _).mp (by rw [Nat.card_zpowers, hg₀])
  have hiff : ∀ g : G, Odd (orderOf g) ↔ g ∈ Subgroup.zpowers (g₀ ^ 2 ^ a) := by
    intro g
    constructor
    · intro hg
      have hdvd : orderOf g ∣ h := by
        have h1 : orderOf g ∣ 2 ^ a * h := hcard ▸ orderOf_dvd_natCard g
        exact (Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hg)).dvd_of_dvd_mul_left h1
      have hgz : g ∈ Subgroup.zpowers g₀ := by
        rw [htop]
        exact Subgroup.mem_top g
      obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hgz)
      have hk : 2 ^ a * h ∣ k * h := by
        rw [← hcard, ← hg₀, orderOf_dvd_iff_pow_eq_one, pow_mul]
        exact orderOf_dvd_iff_pow_eq_one.mp hdvd
      have hk' : 2 ^ a ∣ k := by
        rw [mul_comm k h, mul_comm (2 ^ a) h] at hk
        exact Nat.dvd_of_mul_dvd_mul_left hh.pos hk
      obtain ⟨k', rfl⟩ := hk'
      rw [pow_mul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    · intro hg
      apply Odd.of_dvd_nat hh
      rw [← hc]
      exact orderOf_dvd_of_mem_zpowers hg
  rw [← hc, ← Nat.card_zpowers]
  exact Nat.card_congr (Equiv.subtypeEquivRight hiff)

section Fixed

variable {F : Type*} [Field F]

@[expose] def fieldAction (F : Type*) [Field F] :
    (F ≃+* F) →* MulAut (Matrix.SpecialLinearGroup (Fin 2) F) where
  toFun σ :=
    { toFun := Matrix.SpecialLinearGroup.map σ.toRingHom
      invFun := Matrix.SpecialLinearGroup.map σ.symm.toRingHom
      left_inv := fun g => SL_ext (by
        ext i j
        simp [Matrix.SpecialLinearGroup.map_apply_coe])
      right_inv := fun g => SL_ext (by
        ext i j
        simp [Matrix.SpecialLinearGroup.map_apply_coe])
      map_mul' := map_mul _ }
  map_one' := MulEquiv.ext fun g => SL_ext (by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe])
  map_mul' σ τ := MulEquiv.ext fun g => SL_ext (by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe])

theorem fieldAction_apply (σ : F ≃+* F) (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    fieldAction F σ g = Matrix.SpecialLinearGroup.map σ.toRingHom g := rfl

theorem fieldAction_coe (σ : F ≃+* F) (g : Matrix.SpecialLinearGroup (Fin 2) F) (i j : Fin 2) :
    ((fieldAction F σ g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j =
      σ ((g : Matrix (Fin 2) (Fin 2) F) i j) := by
  simp [fieldAction_apply, Matrix.SpecialLinearGroup.map_apply_coe]

theorem fieldAction_J₀ (σ : F ≃+* F) : fieldAction F σ (J₀ F) = J₀ F := by
  apply SL_ext
  ext i j
  rw [fieldAction_coe, J₀_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem fieldAction_mem_torus (σ : F ≃+* F) {g : Matrix.SpecialLinearGroup (Fin 2) F}
    (hg : g ∈ torus F) : fieldAction F σ g ∈ torus F := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
  rw [← fieldAction_J₀ σ, ← map_mul, hg, map_mul]

section OddTorus

variable (W : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
  (hW : ∀ g, g ∈ W ↔ g ∈ torus F ∧ Odd (orderOf g))

include hW in
theorem fieldAction_mem (σ : F ≃+* F) {g : Matrix.SpecialLinearGroup (Fin 2) F} (hg : g ∈ W) :
    fieldAction F σ g ∈ W := by
  rw [hW] at hg ⊢
  exact ⟨fieldAction_mem_torus σ hg.1, by rw [MulEquiv.orderOf_eq]; exact hg.2⟩

@[expose] def oddTorusAction : (F ≃+* F) →* MulAut W where
  toFun σ :=
    { toFun := fun w => ⟨fieldAction F σ w, fieldAction_mem W hW σ w.2⟩
      invFun := fun w => ⟨fieldAction F σ⁻¹ w, fieldAction_mem W hW σ⁻¹ w.2⟩
      left_inv := fun w => Subtype.ext (by
        change fieldAction F σ⁻¹ (fieldAction F σ w) = w
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
      right_inv := fun w => Subtype.ext (by
        change fieldAction F σ (fieldAction F σ⁻¹ w) = w
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply])
      map_mul' := fun a b => Subtype.ext
        (map_mul (fieldAction F σ) (a : Matrix.SpecialLinearGroup (Fin 2) F) b) }
  map_one' := MulEquiv.ext fun w => Subtype.ext (by
    change fieldAction F 1 w = w
    rw [map_one, MulAut.one_apply])
  map_mul' σ τ := MulEquiv.ext fun w => Subtype.ext (by
    change fieldAction F (σ * τ) w = fieldAction F σ (fieldAction F τ w)
    rw [map_mul, MulAut.mul_apply])

theorem oddTorusAction_coe (σ : F ≃+* F) (w : W) :
    ((oddTorusAction W hW σ w : W) : Matrix.SpecialLinearGroup (Fin 2) F) =
      Matrix.SpecialLinearGroup.map σ.toRingHom w := rfl

end OddTorus

@[expose] def fixedField (σ : F ≃+* F) : Subfield F :=
  (σ : F →+* F).eqLocusField (RingHom.id F)

theorem mem_fixedField {σ : F ≃+* F} {a : F} : a ∈ fixedField σ ↔ σ a = a :=
  RingHom.mem_eqLocusField

@[expose] def fixedIncl (σ : F ≃+* F) :
    Matrix.SpecialLinearGroup (Fin 2) (fixedField σ) →* Matrix.SpecialLinearGroup (Fin 2) F :=
  Matrix.SpecialLinearGroup.map (fixedField σ).subtype

theorem fixedIncl_coe (σ : F ≃+* F) (g : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ))
    (i j : Fin 2) :
    ((fixedIncl σ g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j =
      ((g : Matrix (Fin 2) (Fin 2) (fixedField σ)) i j : F) := by
  simp [fixedIncl, Matrix.SpecialLinearGroup.map_apply_coe]

theorem fixedIncl_injective (σ : F ≃+* F) : Function.Injective (fixedIncl σ) := by
  intro g h hgh
  apply SL_ext
  ext i j
  have := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F =>
    (M : Matrix (Fin 2) (Fin 2) F) i j) hgh
  simp only [fixedIncl_coe] at this
  exact this

theorem fixedIncl_J₀ (σ : F ≃+* F) : fixedIncl σ (J₀ (fixedField σ)) = J₀ F := by
  apply SL_ext
  ext i j
  rw [fixedIncl_coe, J₀_coe, J₀_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem fixedIncl_mem_torus_iff (σ : F ≃+* F)
    (g : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)) :
    fixedIncl σ g ∈ torus F ↔ g ∈ torus (fixedField σ) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
    ← fixedIncl_J₀ σ, ← map_mul, ← map_mul]
  exact (fixedIncl_injective σ).eq_iff

theorem fieldAction_fixedIncl (σ : F ≃+* F)
    (g : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)) :
    fieldAction F σ (fixedIncl σ g) = fixedIncl σ g := by
  apply SL_ext
  ext i j
  rw [fieldAction_coe, fixedIncl_coe]
  exact mem_fixedField.mp ((g : Matrix (Fin 2) (Fin 2) (fixedField σ)) i j).2

theorem exists_fixedIncl (σ : F ≃+* F) {g : Matrix.SpecialLinearGroup (Fin 2) F}
    (hg : fieldAction F σ g = g) : ∃ g', fixedIncl σ g' = g := by
  have hfix : ∀ i j, (g : Matrix (Fin 2) (Fin 2) F) i j ∈ fixedField σ := by
    intro i j
    rw [mem_fixedField, ← fieldAction_coe, hg]
  let M : Matrix (Fin 2) (Fin 2) (fixedField σ) := Matrix.of fun i j => ⟨_, hfix i j⟩
  have hM : (fixedField σ).subtype.mapMatrix M = (g : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    rfl
  have hdet : M.det = 1 := by
    apply Subtype.ext
    have h := RingHom.map_det (fixedField σ).subtype M
    rw [hM, Matrix.SpecialLinearGroup.det_coe] at h
    exact h
  let g' : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ) := ⟨M, hdet⟩
  refine ⟨g', SL_ext ?_⟩
  ext i j
  rw [fixedIncl_coe]
  rfl

theorem card_fixedField_eq (σ : F ≃+* F) :
    Nat.card (fixedField σ) = Nat.card {a : F // σ a = a} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_fixedField)

theorem card_fixedField {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (σ : F ≃+* F) : orderOf σ ∣ f ∧ Nat.card (fixedField σ) = p ^ (f / orderOf σ) := by
  obtain ⟨-, -, -, -, -, hA⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp hf hF
  obtain ⟨hdvd, S, hS, hcard⟩ := hA (Subgroup.zpowers σ)
  rw [Nat.card_zpowers] at hdvd hcard
  refine ⟨hdvd, ?_⟩
  rw [← hcard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)
  rw [mem_fixedField, ← SetLike.mem_coe, hS, Set.mem_ofPred_eq]
  constructor
  · intro ha τ hτ
    have hstab : σ ∈ MulAction.stabilizer (F ≃+* F) a := by
      rw [MulAction.mem_stabilizer_iff, RingAut.smul_def]
      exact ha
    have h := Subgroup.zpowers_le.mpr hstab hτ
    rwa [MulAction.mem_stabilizer_iff, RingAut.smul_def] at h
  · intro ha
    exact ha σ (Subgroup.mem_zpowers σ)

section OddTorusCard

variable (W : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
  (hW : ∀ g, g ∈ W ↔ g ∈ torus F ∧ Odd (orderOf g))

include hW in
theorem card_fixed_oddTorus (σ : F ≃+* F) :
    Nat.card {g // g ∈ W ∧ Matrix.SpecialLinearGroup.map σ.toRingHom g = g} =
      Nat.card {g : torus (fixedField σ) // Odd (orderOf g)} := by
  symm
  have hord : ∀ g : torus (fixedField σ),
      orderOf (fixedIncl σ (g : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ))) =
        orderOf g := fun g => by
    rw [orderOf_injective (fixedIncl σ) (fixedIncl_injective σ), Subgroup.orderOf_coe]
  let f : {g : torus (fixedField σ) // Odd (orderOf g)} →
      {g // g ∈ W ∧ Matrix.SpecialLinearGroup.map σ.toRingHom g = g} := fun g =>
    ⟨fixedIncl σ (g.1 : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)),
      (hW _).mpr ⟨(fixedIncl_mem_torus_iff σ _).mpr g.1.2, by rw [hord]; exact g.2⟩,
      fieldAction_fixedIncl σ _⟩
  refine Nat.card_congr (Equiv.ofBijective f ⟨fun g h hgh => ?_, fun g => ?_⟩)
  · apply Subtype.ext
    apply Subtype.ext
    exact fixedIncl_injective σ (congrArg Subtype.val hgh)
  · obtain ⟨g, hgW, hgfix⟩ := g
    obtain ⟨g', rfl⟩ := exists_fixedIncl σ hgfix
    obtain ⟨hgT, hgo⟩ := (hW _).mp hgW
    have hg'T := (fixedIncl_mem_torus_iff σ g').mp hgT
    refine ⟨⟨⟨g', hg'T⟩, ?_⟩, rfl⟩
    have h := hord ⟨g', hg'T⟩
    rw [← h]
    exact hgo

include hW in
theorem card_W :
    Nat.card W = Nat.card {g : torus F // Odd (orderOf g)} := by
  refine Nat.card_congr ⟨fun w => ⟨⟨w, ((hW w).mp w.2).1⟩, by
      rw [Subgroup.orderOf_mk]; exact ((hW w).mp w.2).2⟩,
    fun g => ⟨g.1, (hW _).mpr ⟨g.1.2, by rw [Subgroup.orderOf_coe]; exact g.2⟩⟩,
    fun w => rfl, fun g => rfl⟩

include hW in
theorem W_le_torus : W ≤ torus F := fun g hg => ((hW g).mp hg).1

include hW in
theorem W_comm (a b : W) : a * b = b * a := by
  apply Subtype.ext
  exact torus_comm (W_le_torus W hW a.2) (W_le_torus W hW b.2)

end OddTorusCard

end Fixed

section Semidirect

open scoped commutatorElement

variable {N G : Type*} [Group N] [Group G] [Finite N] [Finite G]

theorem semidirect_cyclic_derived (φ : G →* MulAut N) (hN : ∀ a b : N, a * b = b * a)
    (g₀ : G) (hg₀ : Subgroup.zpowers g₀ = ⊤)
    (hsmall : ∀ s : G, s ≠ 1 → Nat.card {n : N // φ s n = n} ^ 2 < Nat.card N) :
    commutator (N ⋊[φ] G) =
        ⁅(SemidirectProduct.inl : N →* N ⋊[φ] G).range,
          Subgroup.zpowers (SemidirectProduct.inr g₀ : N ⋊[φ] G)⁆ ∧
      commutator (N ⋊[φ] G) =
        (Subgroup.closure (Set.range fun n : N => n⁻¹ * φ g₀ n)).map
          (SemidirectProduct.inl : N →* N ⋊[φ] G) ∧
      Nat.card (commutator (N ⋊[φ] G)) * Nat.card {n : N // ∀ s, φ s n = n} = Nat.card N ∧
      Subgroup.centralizer (commutator (N ⋊[φ] G) : Set (N ⋊[φ] G)) =
        (SemidirectProduct.inl : N →* N ⋊[φ] G).range := by
  have hpow : ∀ s : G, ∃ k : ℕ, g₀ ^ k = s := fun s =>
    (Submonoid.mem_powers_iff _ _).mp
      (mem_powers_iff_mem_zpowers.mpr (hg₀ ▸ Subgroup.mem_top s))
  have hG : ∀ s t : G, s * t = t * s := by
    intro s t
    obtain ⟨i, rfl⟩ := hpow s
    obtain ⟨j, rfl⟩ := hpow t
    exact (Commute.pow_pow_self g₀ i j).eq
  let δ : N →* N :=
    { toFun := fun n => n⁻¹ * φ g₀ n
      map_one' := by simp
      map_mul' := fun a b => by
        calc (a * b)⁻¹ * φ g₀ (a * b) = b⁻¹ * a⁻¹ * (φ g₀ a * φ g₀ b) := by
              rw [_root_.mul_inv_rev, map_mul]
          _ = a⁻¹ * (b⁻¹ * φ g₀ a) * φ g₀ b := by
              rw [hN b⁻¹ a⁻¹]
              simp only [mul_assoc]
          _ = a⁻¹ * (φ g₀ a * b⁻¹) * φ g₀ b := by rw [hN b⁻¹ (φ g₀ a)]
          _ = a⁻¹ * φ g₀ a * (b⁻¹ * φ g₀ b) := by simp only [mul_assoc] }
  have hδ : ∀ n, δ n = n⁻¹ * φ g₀ n := fun n => rfl
  have hδpow : ∀ (k : ℕ) (n : N), n⁻¹ * φ (g₀ ^ k) n ∈ δ.range := by
    intro k
    induction k with
    | zero =>
      intro n
      rw [pow_zero, map_one, MulAut.one_apply, inv_mul_cancel]
      exact δ.range.one_mem
    | succ k ih =>
      intro n
      have h : n⁻¹ * φ (g₀ ^ (k + 1)) n =
          (n⁻¹ * φ g₀ n) * ((φ g₀ n)⁻¹ * φ (g₀ ^ k) (φ g₀ n)) := by
        rw [pow_succ, map_mul, MulAut.mul_apply]
        group
      rw [h]
      exact δ.range.mul_mem ⟨n, rfl⟩ (ih _)
  have hδu : ∀ (u : G) (n : N), n⁻¹ * φ u n ∈ δ.range := by
    intro u n
    obtain ⟨k, rfl⟩ := hpow u
    exact hδpow k n
  have hInormal : δ.range.Normal := ⟨fun n hn g => by rwa [hN g n, mul_inv_cancel_right]⟩
  let ψ : N ⋊[φ] G →* G × (N ⧸ δ.range) :=
    { toFun := fun x => (x.right, (x.left : N ⧸ δ.range))
      map_one' := rfl
      map_mul' := fun x y => by
        refine Prod.ext rfl ?_
        change ((x.left * φ x.right y.left : N) : N ⧸ δ.range) =
          (x.left : N ⧸ δ.range) * (y.left : N ⧸ δ.range)
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
        have h := δ.range.inv_mem (hδu x.right y.left)
        convert h using 1
        group }
  have hKψ : commutator (N ⋊[φ] G) ≤ ψ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    refine Prod.ext (hG _ _) ?_
    change (x.left : N ⧸ δ.range) * (y.left : N ⧸ δ.range) =
      (y.left : N ⧸ δ.range) * (x.left : N ⧸ δ.range)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hN]
  have hψM : ψ.ker ≤ δ.range.map (SemidirectProduct.inl : N →* N ⋊[φ] G) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : x.right = 1 := congrArg Prod.fst hx
    have h2 : (x.left : N ⧸ δ.range) = 1 := congrArg Prod.snd hx
    rw [QuotientGroup.eq_one_iff] at h2
    refine ⟨x.left, h2, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact h1.symm
  have hcomm : ∀ n : N, ⁅(SemidirectProduct.inl n⁻¹ : N ⋊[φ] G),
      (SemidirectProduct.inr g₀ : N ⋊[φ] G)⁆ = SemidirectProduct.inl (δ n) := by
    intro n
    rw [commutatorElement_def, hδ, map_mul, SemidirectProduct.inl_aut]
    simp only [map_inv, inv_inv, mul_assoc]
  have hMcomm : δ.range.map (SemidirectProduct.inl : N →* N ⋊[φ] G) ≤
      ⁅(SemidirectProduct.inl : N →* N ⋊[φ] G).range,
        Subgroup.zpowers (SemidirectProduct.inr g₀ : N ⋊[φ] G)⁆ := by
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator ⟨n⁻¹, rfl⟩ (Subgroup.mem_zpowers _)
  have hcommK : ⁅(SemidirectProduct.inl : N →* N ⋊[φ] G).range,
      Subgroup.zpowers (SemidirectProduct.inr g₀ : N ⋊[φ] G)⁆ ≤ commutator (N ⋊[φ] G) := by
    rw [commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  have hK'M : commutator (N ⋊[φ] G) = δ.range.map (SemidirectProduct.inl : N →* N ⋊[φ] G) :=
    le_antisymm (hKψ.trans hψM) (hMcomm.trans hcommK)
  have hclosure : Subgroup.closure (Set.range fun n : N => n⁻¹ * φ g₀ n) = δ.range := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨n, rfl⟩
      exact ⟨n, rfl⟩
    · rintro _ ⟨n, rfl⟩
      exact Subgroup.subset_closure ⟨n, rfl⟩
  have hfixall : ∀ n : N, (∀ s, φ s n = n) ↔ φ g₀ n = n := by
    intro n
    refine ⟨fun h => h g₀, fun h s => ?_⟩
    obtain ⟨k, rfl⟩ := hpow s
    induction k with
    | zero => rw [pow_zero, map_one, MulAut.one_apply]
    | succ k ih => rw [pow_succ, map_mul, MulAut.mul_apply, h, ih]
  have hkerδ : Nat.card δ.ker = Nat.card {n : N // ∀ s, φ s n = n} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun n => ?_)
    rw [MonoidHom.mem_ker, hδ, hfixall, inv_mul_eq_one, eq_comm]
  have hcardδ : Nat.card δ.range * Nat.card {n : N // ∀ s, φ s n = n} = Nat.card N := by
    have h := δ.ker.card_mul_index
    rw [Subgroup.index_ker, hkerδ, mul_comm] at h
    exact h
  have hcardK' : Nat.card (commutator (N ⋊[φ] G)) = Nat.card δ.range := by
    rw [hK'M, Subgroup.card_map_of_injective SemidirectProduct.inl_injective]
  refine ⟨le_antisymm (hK'M ▸ hMcomm) hcommK, by rw [hclosure]; exact hK'M,
    by rw [hcardK']; exact hcardδ, ?_⟩
  apply le_antisymm
  · intro x hx
    by_contra hxN
    have hs : x.right ≠ 1 := by
      intro h1
      apply hxN
      refine ⟨x.left, ?_⟩
      apply SemidirectProduct.ext
      · rfl
      · exact h1.symm
    have hfix : ∀ c ∈ δ.range, φ x.right c = c := by
      intro c hc
      have hmem : (SemidirectProduct.inl c : N ⋊[φ] G) ∈ commutator (N ⋊[φ] G) := by
        rw [hK'M]
        exact ⟨c, hc, rfl⟩
      have h := Subgroup.mem_centralizer_iff.mp hx _ hmem
      have hl := congrArg SemidirectProduct.left h
      simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
        SemidirectProduct.right_inl, map_one, MulAut.one_apply] at hl
      rw [hN c x.left] at hl
      exact (mul_left_cancel hl).symm
    have h1 : Nat.card δ.range ≤ Nat.card {n : N // φ x.right n = n} := by
      refine Nat.card_le_card_of_injective (fun c : δ.range => (⟨c, hfix c c.2⟩ :
        {n : N // φ x.right n = n})) (fun a b hab => Subtype.ext ?_)
      have h := congrArg Subtype.val hab
      exact h
    have h2 : Nat.card {n : N // ∀ s, φ s n = n} ≤ Nat.card {n : N // φ x.right n = n} := by
      refine Nat.card_le_card_of_injective (fun c => (⟨c.1, c.2 x.right⟩ :
        {n : N // φ x.right n = n})) (fun a b hab => Subtype.ext ?_)
      have h := congrArg Subtype.val hab
      exact h
    have h3 := hsmall x.right hs
    have h4 : Nat.card N ≤ Nat.card {n : N // φ x.right n = n} ^ 2 := by
      rw [← hcardδ, sq]
      exact Nat.mul_le_mul h1 h2
    omega
  · rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [SetLike.mem_coe, hK'M] at hz
    obtain ⟨c, -, rfl⟩ := hz
    rw [← map_mul, ← map_mul, hN]

end Semidirect

section Arithmetic

theorem pow_mod_four {x e : ℕ} (hx : Odd x) (he : Odd e) : x ^ e % 4 = x % 4 := by
  obtain ⟨r, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := he
  have h1 : (2 * r + 1) ^ 2 % 4 = 1 := by
    have : (2 * r + 1) ^ 2 = 4 * (r * r + r) + 1 := by ring
    rw [this]
    omega
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod, h1, one_pow]
  simp

theorem eps_cases (q : ℕ) : (if q % 4 = 1 then (1 : ℤ) else -1) = 1 ∨
    (if q % 4 = 1 then (1 : ℤ) else -1) = -1 := by
  split_ifs <;> simp

theorem padicValInt_pow_sub_eps {x : ℤ} {e : ℕ} (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (hx : Odd x)
    (he : Odd e) (hne : x - ε ≠ 0) :
    padicValInt 2 (x ^ e - ε) = padicValInt 2 (x - ε) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hεe : ε ^ e = ε := by
    rcases hε with rfl | rfl
    · rw [one_pow]
    · exact he.neg_one_pow
  have hgeom := geom_sum₂_mul x ε e
  rw [hεe] at hgeom
  set S := ∑ i ∈ Finset.range e, x ^ i * ε ^ (e - 1 - i)
  have hS : ¬ ((2 : ℕ) : ℤ) ∣ S := by
    intro hdvd
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd S 2).mpr hdvd
    have hx1 : (x : ZMod 2) = 1 := ZMod.intCast_eq_one_iff_odd.mpr hx
    have hε1 : (ε : ZMod 2) = 1 := by
      rcases hε with rfl | rfl
      · simp
      · simp only [Int.cast_neg, Int.cast_one]
        exact neg_one_eq_one_iff.mpr (ringChar.eq (ZMod 2) 2)
    have hcast : (S : ZMod 2) = e := by
      simp only [S, Int.cast_sum, Int.cast_mul, Int.cast_pow, hx1, hε1, one_pow, mul_one,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hcast, ZMod.natCast_eq_one_iff_odd.mpr he] at h0
    exact one_ne_zero h0
  have hS0 : S ≠ 0 := fun h => hS (h ▸ dvd_zero _)
  rw [← hgeom, padicValInt.mul hS0 hne, padicValInt.eq_zero_of_not_dvd hS, zero_add]

theorem padicValNat_two_pow_mul_odd {k h : ℕ} (hh : Odd h) : padicValNat 2 (2 ^ k * h) = k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) hh.pos.ne', padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd
      (fun h2 => (Nat.not_even_iff_odd.mpr hh) (even_iff_two_dvd.mpr h2)), add_zero]

theorem sq_lt_of_three_le {r : ℤ} {e : ℕ} {m : ℤ} (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (hr : 3 ≤ r)
    (he : 3 ≤ e) (hm : 4 ≤ m) : (r - ε) ^ 2 < m * (r ^ e - ε) := by
  have h3 : r ^ 3 ≤ r ^ e := pow_le_pow_right₀ (by omega) he
  have hr3 : 27 ≤ r ^ 3 := by
    have : (3 : ℤ) ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ (by norm_num) hr 3
    norm_num at this
    exact this
  have hsq : (r - ε) ^ 2 ≤ (r + 1) ^ 2 := by
    rcases hε with rfl | rfl <;> nlinarith
  have hpos : r ^ 3 - 1 ≤ r ^ e - ε := by rcases hε with rfl | rfl <;> omega
  have hkey : (r + 1) ^ 2 < 4 * (r ^ 3 - 1) := by nlinarith
  have h4 : 4 * (r ^ 3 - 1) ≤ m * (r ^ e - ε) := by
    apply mul_le_mul hm hpos (by omega) (by omega)
  linarith

theorem four_le_two_part {q : ℕ} (hq : Odd q) (hq1 : 1 < q) :
    4 ≤ 2 ^ padicValInt 2 ((q : ℤ) - if q % 4 = 1 then 1 else -1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq2 : q % 2 = 1 := Nat.odd_iff.mp hq
  have h4' : (4 : ℤ) ∣ (q : ℤ) - if q % 4 = 1 then 1 else -1 := by
    split_ifs with h <;> omega
  have h4 : ((2 : ℕ) : ℤ) ^ 2 ∣ (q : ℤ) - if q % 4 = 1 then 1 else -1 := by
    norm_num
    exact h4'
  have hne : ((q : ℤ) - if q % 4 = 1 then 1 else -1) ≠ 0 := by
    split_ifs with h <;> omega
  rcases (padicValInt_dvd_iff 2 _).mp h4 with h | h
  · exact absurd h hne
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) h

end Arithmetic

theorem card_oddTorus {L : Type*} [Field L] [Finite L] (h2 : (2 : L) ≠ 0) :
    (Nat.card {g : torus L // Odd (orderOf g)} : ℤ) =
      ((Nat.card L : ℤ) - if Nat.card L % 4 = 1 then 1 else -1) /
        2 ^ padicValInt 2 ((Nat.card L : ℤ) - if Nat.card L % 4 = 1 then 1 else -1) := by
  have := torus_isCyclic h2
  rw [← torus_card h2]
  have hN0 : Nat.card (torus L) ≠ 0 := Nat.card_pos.ne'
  obtain ⟨k, h, hh, hkh⟩ := Nat.exists_eq_two_pow_mul_odd hN0
  rw [card_odd_orderOf k h hkh hh, padicValInt.of_nat, hkh, padicValNat_two_pow_mul_odd hh]
  push_cast
  rw [Int.mul_ediv_cancel_left _ (by positivity)]

theorem exists_oddTorus (F : Type*) [Field F] :
    ∃ W : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F),
      ∀ g, g ∈ W ↔ g ∈ torus F ∧ Odd (orderOf g) := by
  refine ⟨{ carrier := {g | g ∈ torus F ∧ Odd (orderOf g)}
            mul_mem' := ?_
            one_mem' := ⟨(torus F).one_mem, by rw [orderOf_one]; exact odd_one⟩
            inv_mem' := ?_ }, fun g => Iff.rfl⟩
  · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(torus F).mul_mem ha hb, ?_⟩
    have hc : Commute a b := torus_comm ha hb
    exact Odd.of_dvd_nat (Odd.of_dvd_nat (ha'.mul hb') (Nat.lcm_dvd_mul _ _))
      hc.orderOf_mul_dvd_lcm
  · rintro a ⟨ha, ha'⟩
    exact ⟨(torus F).inv_mem ha, by rw [orderOf_inv]; exact ha'⟩

end CFSG.Wreathed.OddFieldTorus
