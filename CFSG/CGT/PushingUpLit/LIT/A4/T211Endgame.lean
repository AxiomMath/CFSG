module

public import CFSG.RankThree.Transfer.PGroup
public import CFSG.RankThree.Transfer.FixedPoints
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

namespace CFSG.CGT.PushingUpLit.T211

open Subgroup MulAction

abbrev Z2 := Multiplicative (ZMod 2)

theorem z2_mul_self (z : Z2) : z * z = 1 := by revert z; decide

theorem z2_inv (z : Z2) : z⁻¹ = z := by revert z; decide

theorem z2_ofAdd_one_ne_one : (Multiplicative.ofAdd (1 : ZMod 2) : Z2) ≠ 1 := by decide

theorem z2_eq_of_ne_one {y z : Z2} (hy : y ≠ 1) (hz : z ≠ 1) : y = z := by
  revert y z; decide

section Ext

variable {R : Type*} [Group R] {T : Subgroup R}

open Classical in
@[expose] noncomputable def ext (ϕ : T →* Z2) (y : R) : Z2 :=
  if h : y ∈ T then ϕ ⟨y, h⟩ else 1

variable (ϕ : T →* Z2)

theorem ext_of_mem {y : R} (h : y ∈ T) : ext ϕ y = ϕ ⟨y, h⟩ := by
  simp [ext, h]

theorem ext_one : ext ϕ 1 = 1 := by
  rw [ext_of_mem ϕ T.one_mem]
  exact map_one ϕ

theorem ext_mul {y z : R} (hy : y ∈ T) (hz : z ∈ T) : ext ϕ (y * z) = ext ϕ y * ext ϕ z := by
  rw [ext_of_mem ϕ (T.mul_mem hy hz), ext_of_mem ϕ hy, ext_of_mem ϕ hz,
    ← map_mul]
  rfl

theorem ext_inv {y : R} (hy : y ∈ T) : ext ϕ y⁻¹ = ext ϕ y := by
  rw [ext_of_mem ϕ (T.inv_mem hy), ext_of_mem ϕ hy, ← z2_inv (ϕ ⟨y, hy⟩), ← map_inv]
  rfl

theorem ext_conj {t y : R} (ht : t ∈ T) (hy : y ∈ T) : ext ϕ (t * y * t⁻¹) = ext ϕ y := by
  rw [ext_mul ϕ (T.mul_mem ht hy) (T.inv_mem ht), ext_mul ϕ ht hy, ext_inv ϕ ht,
    mul_comm (ext ϕ t) (ext ϕ y), mul_assoc, z2_mul_self, mul_one]

theorem ext_conj' {t y : R} (ht : t ∈ T) (hy : y ∈ T) : ext ϕ (t⁻¹ * y * t) = ext ϕ y := by
  simpa using ext_conj ϕ (T.inv_mem ht) hy

theorem ext_mul_self {y : R} (hy : y ∈ T) : ext ϕ (y * y) = 1 := by
  rw [ext_mul ϕ hy hy]
  exact z2_mul_self _

end Ext

section Odd

variable {R : Type*} [Group R] {T : Subgroup R}

theorem mem_of_ext_ne_one {ϕ : T →* Z2} {y : R} (h : ext ϕ y ≠ 1) : y ∈ T := by
  by_contra hy
  exact h (by simp [ext, hy])

@[expose] def oddFixed (ϕ : T →* Z2) (x : R) : Set (R ⧸ T) :=
  {X | ∃ r : R, (r : R ⧸ T) = X ∧ ext ϕ (r⁻¹ * x * r) ≠ 1}

theorem z2_conj (φ : R →* Z2) (r x : R) : φ (r⁻¹ * x * r) = φ x := by
  rw [map_mul, map_mul, map_inv, z2_inv, mul_comm (φ r) (φ x), mul_assoc, z2_mul_self, mul_one]

theorem exists_odd {ϕ : T →* Z2} {x : R} (hc : Odd (Nat.card (oddFixed ϕ x))) :
    ∃ r : R, ext ϕ (r⁻¹ * x * r) ≠ 1 := by
  by_contra h
  have h' : ∀ r : R, ext ϕ (r⁻¹ * x * r) = 1 := fun r => not_not.mp fun hh => h ⟨r, hh⟩
  have hS : oddFixed ϕ x = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun X hX => ?_
    obtain ⟨r, -, hr⟩ := hX
    exact hr (h' r)
  rw [hS] at hc
  simp at hc

theorem sup_eq_top [Finite R] (hR : IsPGroup 2 R) {A : Subgroup R} {x : R}
    (hgen : A ⊔ zpowers x = ⊤) {ϕ : T →* Z2} (hc : Odd (Nat.card (oddFixed ϕ x))) :
    A ⊔ T = ⊤ := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφs, hφk⟩ := CFSG.RankThree.Transfer.exists_surjective_zmod_of_ne_top hR hne
  have hx : φ x ≠ 1 := by
    intro hx1
    have hle : A ⊔ zpowers x ≤ φ.ker :=
      sup_le (le_trans le_sup_left hφk) (zpowers_le.mpr ((MonoidHom.mem_ker).mpr hx1))
    rw [hgen] at hle
    obtain ⟨g, hg⟩ := hφs (Multiplicative.ofAdd (1 : ZMod 2))
    have h1 : φ g = 1 := (MonoidHom.mem_ker).mp (hle (mem_top g))
    rw [h1] at hg
    exact z2_ofAdd_one_ne_one hg.symm
  obtain ⟨r, hr⟩ := exists_odd hc
  have hrT : r⁻¹ * x * r ∈ T := mem_of_ext_ne_one hr
  have h1 : φ (r⁻¹ * x * r) = 1 := (MonoidHom.mem_ker).mp (hφk (mem_sup_right hrT))
  rw [z2_conj] at h1
  exact hx h1

theorem exists_conj_mem {A : Subgroup R} [A.Normal] {x : R} (hAT : A ⊔ T = ⊤) {ϕ : T →* Z2}
    (hc : Odd (Nat.card (oddFixed ϕ x))) : ∃ a ∈ A, ext ϕ (a⁻¹ * x * a) ≠ 1 := by
  obtain ⟨r, hr⟩ := exists_odd hc
  have hrT : r⁻¹ * x * r ∈ T := mem_of_ext_ne_one hr
  have hr' : r ∈ A ⊔ T := by rw [hAT]; exact mem_top r
  obtain ⟨a, ha, t, ht, rfl⟩ := (mem_sup_of_normal_left (s := A) (t := T)).mp hr'
  refine ⟨a, ha, ?_⟩
  have hy : a⁻¹ * x * a = t * ((a * t)⁻¹ * x * (a * t)) * t⁻¹ := by group
  have hyT : a⁻¹ * x * a ∈ T := by
    rw [hy]; exact T.mul_mem (T.mul_mem ht hrT) (T.inv_mem ht)
  rw [hy, ext_conj ϕ ht hrT]
  exact hr

theorem card_oddFixed_conj (ϕ : T →* Z2) (x a : R) :
    Nat.card (oddFixed ϕ (a⁻¹ * x * a)) = Nat.card (oddFixed ϕ x) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm a : Equiv.Perm (R ⧸ T)) ?_)
  intro X
  constructor
  · rintro ⟨r, rfl, hr⟩
    refine ⟨a * r, ?_, ?_⟩
    · simp [MulAction.Quotient.smul_mk]
    · have : (a * r)⁻¹ * x * (a * r) = r⁻¹ * (a⁻¹ * x * a) * r := by group
      rw [this]; exact hr
  · rintro ⟨r, hrX, hr⟩
    refine ⟨a⁻¹ * r, ?_, ?_⟩
    · have : a • X = (r : R ⧸ T) := by simpa using hrX.symm
      have h2 : X = a⁻¹ • (r : R ⧸ T) := by rw [← this]; simp
      rw [h2]; simp [MulAction.Quotient.smul_mk]
    · have : (a⁻¹ * r)⁻¹ * (a⁻¹ * x * a) * (a⁻¹ * r) = r⁻¹ * x * r := by group
      rw [this]; exact hr

end Odd

section Delta

open scoped commutatorElement

variable {R : Type*} [Group R]

@[expose] def delta (x a : R) : R := a⁻¹ * x * a * x⁻¹

theorem delta_eq (x a : R) : delta x a = a⁻¹ * (x * a * x⁻¹) := by
  simp [delta, mul_assoc]

theorem delta_one (x : R) : delta x 1 = 1 := by simp [delta]

variable {A : Subgroup R}

theorem delta_mem [A.Normal] {x a : R} (ha : a ∈ A) : delta x a ∈ A := by
  rw [delta_eq]
  exact A.mul_mem (A.inv_mem ha) (Normal.conj_mem ‹A.Normal› a ha x)

theorem delta_mul [A.Normal] (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {x a b : R} (ha : a ∈ A)
    (hb : b ∈ A) : delta x (a * b) = delta x a * delta x b := by
  have hu : delta x a ∈ A := delta_mem ha
  have hcomm : b⁻¹ * delta x a = delta x a * b⁻¹ := hAc _ (A.inv_mem hb) _ hu
  have e1 : delta x (a * b) = b⁻¹ * delta x a * (x * b * x⁻¹) := by unfold delta; group
  have e2 : delta x b = b⁻¹ * (x * b * x⁻¹) := by unfold delta; group
  rw [e1, hcomm, e2]
  group

theorem delta_inv [A.Normal] (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {x a : R} (ha : a ∈ A) :
    delta x a⁻¹ = (delta x a)⁻¹ := by
  have h := delta_mul hAc (x := x) (A.inv_mem ha) ha
  rw [inv_mul_cancel, delta_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem delta_iter_mem [A.Normal] {x a : R} (ha : a ∈ A) (k : ℕ) : (delta x)^[k] a ∈ A := by
  induction k with
  | zero => simpa using ha
  | succ k ih => rw [Function.iterate_succ_apply']; exact delta_mem ih

theorem delta_eq_commutator (x a : R) : delta x a = ⁅a⁻¹, x⁆ := by
  simp [delta, commutatorElement_def]

theorem delta_iter_mem_lowerCentralSeries (x a : R) (k : ℕ) :
    (delta x)^[k] a ∈ (⊤ : Subgroup R).lowerCentralSeries k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', delta_eq_commutator, Subgroup.lowerCentralSeries_succ]
    exact commutator_mem_commutator (Subgroup.inv_mem _ ih) (mem_top x)

theorem exists_delta_iter_eq_one [Finite R] (hR : IsPGroup 2 R) (x : R) :
    ∃ N : ℕ, ∀ a : R, (delta x)^[N] a = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent R := hR.isNilpotent
  refine ⟨Group.nilpotencyClass R, fun a => ?_⟩
  have h := delta_iter_mem_lowerCentralSeries x a (Group.nilpotencyClass R)
  rw [Subgroup.lowerCentralSeries_nilpotencyClass] at h
  exact (mem_bot).mp h

end Delta

section Core

variable {R : Type*} [Group R] {A T : Subgroup R} [A.Normal]

@[expose] def C0 (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (x : R) (ϕ : T →* Z2) : Subgroup R where
  carrier := {a | a ∈ A ∧ delta x a ∈ T ∧ ext ϕ (delta x a) = 1}
  mul_mem' := by
    rintro a b ⟨ha, haT, ha1⟩ ⟨hb, hbT, hb1⟩
    refine ⟨A.mul_mem ha hb, ?_, ?_⟩
    · rw [delta_mul hAc ha hb]; exact T.mul_mem haT hbT
    · rw [delta_mul hAc ha hb, ext_mul ϕ haT hbT, ha1, hb1, mul_one]
  one_mem' := by
    refine ⟨A.one_mem, ?_, ?_⟩
    · rw [delta_one]; exact T.one_mem
    · rw [delta_one, ext_one]
  inv_mem' := by
    rintro a ⟨ha, haT, ha1⟩
    refine ⟨A.inv_mem ha, ?_, ?_⟩
    · rw [delta_inv hAc ha]; exact T.inv_mem haT
    · rw [delta_inv hAc ha, ext_inv ϕ haT, ha1]

theorem delta_mem_T {x d : R} (hxT : x ∈ T) (hdT : d ∈ T) (ϕ : T →* Z2) :
    delta x d ∈ T ∧ ext ϕ (delta x d) = 1 := by
  have hyT : d⁻¹ * x * d ∈ T := T.mul_mem (T.mul_mem (T.inv_mem hdT) hxT) hdT
  refine ⟨T.mul_mem hyT (T.inv_mem hxT), ?_⟩
  unfold delta
  rw [ext_mul ϕ hyT (T.inv_mem hxT), ext_conj' ϕ hdT hxT, ext_inv ϕ hxT, z2_mul_self]

theorem oddFixed_eq_orbit (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {x : R} (hxT : x ∈ T)
    {ϕ : T →* Z2} (hϕx : ext ϕ x ≠ 1) (hAT : A ⊔ T = ⊤) :
    oddFixed ϕ x = MulAction.orbit (C0 hAc x ϕ) ((1 : R) : R ⧸ T) := by
  ext X
  constructor
  · rintro ⟨r, rfl, hr⟩
    have hrT : r⁻¹ * x * r ∈ T := mem_of_ext_ne_one hr
    have hr' : r ∈ A ⊔ T := by rw [hAT]; exact mem_top r
    obtain ⟨a, ha, t, ht, rfl⟩ := (mem_sup_of_normal_left (s := A) (t := T)).mp hr'
    have hy : a⁻¹ * x * a = t * ((a * t)⁻¹ * x * (a * t)) * t⁻¹ := by group
    have hyT : a⁻¹ * x * a ∈ T := by
      rw [hy]; exact T.mul_mem (T.mul_mem ht hrT) (T.inv_mem ht)
    have hey : ext ϕ (a⁻¹ * x * a) ≠ 1 := by rw [hy, ext_conj ϕ ht hrT]; exact hr
    have hδT : delta x a ∈ T := T.mul_mem hyT (T.inv_mem hxT)
    have hδ1 : ext ϕ (delta x a) = 1 := by
      have hδ : delta x a = (a⁻¹ * x * a) * x⁻¹ := rfl
      rw [hδ, ext_mul ϕ hyT (T.inv_mem hxT), ext_inv ϕ hxT, z2_eq_of_ne_one hey hϕx,
        z2_mul_self]
    have haC : a ∈ C0 hAc x ϕ := ⟨ha, hδT, hδ1⟩
    refine ⟨⟨a, haC⟩, ?_⟩
    show ((a : R) • ((1 : R) : R ⧸ T)) = ((a * t : R) : R ⧸ T)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.mk_mul_of_mem a ht]
  · rintro ⟨⟨c, hc⟩, rfl⟩
    refine ⟨c, ?_, ?_⟩
    · show ((c : R) : R ⧸ T) = ((c : R) • ((1 : R) : R ⧸ T))
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    · obtain ⟨hcA, hδT, hδ1⟩ := hc
      have : c⁻¹ * x * c = delta x c * x := by unfold delta; group
      rw [this, ext_mul ϕ hδT hxT, hδ1, one_mul]
      exact hϕx

theorem C0_le_T [Finite R] (hR : IsPGroup 2 R) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {x : R} (hxT : x ∈ T) {ϕ : T →* Z2} (hϕx : ext ϕ x ≠ 1) (hAT : A ⊔ T = ⊤)
    (hc : Odd (Nat.card (oddFixed ϕ x))) : ∀ a ∈ C0 hAc x ϕ, a ∈ T := by
  rw [oddFixed_eq_orbit hAc hxT hϕx hAT] at hc
  have hidx := MulAction.index_stabilizer (C0 hAc x ϕ) ((1 : R) : R ⧸ T)
  rw [Nat.card_coe_set_eq, ← hidx] at hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hR.to_subgroup (C0 hAc x ϕ))
  have hdvd : (MulAction.stabilizer (C0 hAc x ϕ) ((1 : R) : R ⧸ T)).index ∣ 2 ^ n := by
    rw [← hn]; exact Subgroup.index_dvd_card _
  obtain ⟨k, -, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hk0 : k = 0 := by
    by_contra hne
    have h2 : 2 ∣ (MulAction.stabilizer (C0 hAc x ϕ) ((1 : R) : R ⧸ T)).index := by
      rw [hk']; exact dvd_pow_self 2 hne
    exact (Nat.not_even_iff_odd.mpr hc) (even_iff_two_dvd.mpr h2)
  rw [hk0, pow_zero] at hk'
  have htop := Subgroup.index_eq_one.mp hk'
  intro a ha
  have hmem : (⟨a, ha⟩ : C0 hAc x ϕ) ∈
      MulAction.stabilizer (C0 hAc x ϕ) ((1 : R) : R ⧸ T) := by rw [htop]; exact mem_top _
  rw [MulAction.mem_stabilizer_iff] at hmem
  have h1 : ((a : R) : R ⧸ T) = ((1 : R) : R ⧸ T) := by
    have : ((a : R) • ((1 : R) : R ⧸ T)) = ((1 : R) : R ⧸ T) := hmem
    rwa [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] at this
  rw [QuotientGroup.eq] at h1
  simpa using T.inv_mem h1

theorem two_dvd_orderOf [Finite R] (hR : IsPGroup 2 R) {x : R} (hx : x ≠ 1) :
    2 ∣ orderOf x := by
  obtain ⟨n, hn⟩ := hR x
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hn)
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hx (orderOf_eq_one_iff.mp hk)
  rw [hk]
  exact dvd_pow_self 2 hk0

theorem core [Finite R] (hR : IsPGroup 2 R) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA4 : ∀ a ∈ A, a ^ 4 = 1) {x : R} (hxT : x ∈ T) {ϕ : T →* Z2} (hϕx : ext ϕ x ≠ 1)
    (hAT : A ⊔ T = ⊤) (hT : T ≠ ⊤) (hc : Odd (Nat.card (oddFixed ϕ x)))
    (hd : ∀ t ∈ T, orderOf t < orderOf x → ext ϕ t = 1) :
    T.index = 2 ∧ (∃ w ∈ A, w ∈ T ∧ ext ϕ w ≠ 1) ∧ ∃ c ∈ A, ∀ u ∈ A, u ∈ T ∨ u * c⁻¹ ∈ T := by
  classical
  have hCT := C0_le_T hR hAc hxT hϕx hAT hc
  have key1 : ∀ a ∈ A, delta x a ∈ T → a ∉ T → ext ϕ (delta x a) ≠ 1 := by
    intro a ha hδ haT h1
    exact haT (hCT a ⟨ha, hδ, h1⟩)
  obtain ⟨N, hN⟩ := exists_delta_iter_eq_one hR x
  have hdeltaN : ∀ j, N ≤ j → ∀ a : R, (delta x)^[j] a = 1 := by
    intro j hj a
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [add_comm, Function.iterate_add_apply, hN a]
    exact Function.iterate_fixed (delta_one x) m
  have hAnT : ∃ c ∈ A, c ∉ T ∧ delta x c ∈ T := by
    have hex0 : ∃ a ∈ A, a ∉ T := by
      by_contra hcon
      have hle : A ≤ T := fun a ha => by_contra fun h => hcon ⟨a, ha, h⟩
      exact hT (eq_top_iff.mpr (hAT ▸ sup_le hle le_rfl))
    obtain ⟨a0, ha0A, ha0T⟩ := hex0
    have hex : ∃ k, (delta x)^[k] a0 ∈ T := ⟨N, by rw [hN a0]; exact T.one_mem⟩
    have hkspec := Nat.find_spec hex
    have hk0 : Nat.find hex ≠ 0 := by
      intro h0
      rw [h0] at hkspec
      exact ha0T hkspec
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hjT : (delta x)^[j] a0 ∉ T := Nat.find_min hex (by omega)
    have hj1 : (delta x)^[j.succ] a0 ∈ T := by rw [← hj]; exact hkspec
    rw [Function.iterate_succ_apply'] at hj1
    exact ⟨_, delta_iter_mem ha0A j, hjT, hj1⟩
  have hall : ∀ a ∈ A, delta x a ∈ T := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, haA, haδ⟩ := hcon
    have hex : ∃ i, 2 ≤ i ∧ (delta x)^[i] a ∈ T :=
      ⟨N + 2, by omega, by rw [hdeltaN _ (by omega) a]; exact T.one_mem⟩
    have hspec := Nat.find_spec hex
    have hmin : ∀ i < Nat.find hex, ¬ (2 ≤ i ∧ (delta x)^[i] a ∈ T) := fun i hi =>
      Nat.find_min hex hi
    have hprev : (delta x)^[Nat.find hex - 1] a ∉ T := by
      by_cases h1 : Nat.find hex - 1 = 1
      · rw [h1]; simpa using haδ
      · intro hT'
        exact hmin (Nat.find hex - 1) (by omega) ⟨by omega, hT'⟩
    obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 2 := ⟨Nat.find hex - 2, by omega⟩
    obtain ⟨a1, ha1def⟩ : ∃ a1, a1 = (delta x)^[m] a := ⟨_, rfl⟩
    have ha1A : a1 ∈ A := by rw [ha1def]; exact delta_iter_mem haA m
    obtain ⟨c0, hc0def⟩ : ∃ c0, c0 = delta x a1 := ⟨_, rfl⟩
    obtain ⟨w, hwdef⟩ : ∃ w, w = delta x c0 := ⟨_, rfl⟩
    have hc0A : c0 ∈ A := by rw [hc0def]; exact delta_mem ha1A
    have hc0iter : c0 = (delta x)^[m + 1] a := by
      rw [hc0def, ha1def]
      exact (Function.iterate_succ_apply' (delta x) m a).symm
    have hwiter : w = (delta x)^[m + 2] a := by
      rw [hwdef, hc0iter]
      exact (Function.iterate_succ_apply' (delta x) (m + 1) a).symm
    have hc0T : c0 ∉ T := by
      rw [hc0iter]
      have := hprev
      rwa [hm, show m + 2 - 1 = m + 1 from rfl] at this
    have hwT : w ∈ T := by
      rw [hwiter, ← hm]; exact hspec.2
    have hϕw : ext ϕ w ≠ 1 := by
      have := key1 c0 hc0A (by rw [← hwdef]; exact hwT) hc0T
      rwa [← hwdef] at this
    have hc0sqT : c0 * c0 ∈ T := by
      refine hCT _ ⟨A.mul_mem hc0A hc0A, ?_, ?_⟩
      · rw [delta_mul hAc hc0A hc0A, ← hwdef]; exact T.mul_mem hwT hwT
      · rw [delta_mul hAc hc0A hc0A, ← hwdef, ext_mul_self ϕ hwT]
    have ha1sqA : a1 * a1 ∈ A := A.mul_mem ha1A ha1A
    have hδsq : delta x (a1 * a1) = c0 * c0 := by
      rw [delta_mul hAc ha1A ha1A, ← hc0def]
    by_cases hI : a1 * a1 ∈ T
    ·
      have h1 : ext ϕ (c0 * c0) = 1 := by
        have := (delta_mem_T hxT hI ϕ).2
        rwa [hδsq] at this
      have heT : c0 * c0 * w ∈ T := T.mul_mem hc0sqT hwT
      have hew : ext ϕ (c0 * c0 * w) ≠ 1 := by
        rw [ext_mul ϕ hc0sqT hwT, h1, one_mul]; exact hϕw
      have hmemT : c0 * c0 * w * (x * x) ∈ T := T.mul_mem heT (T.mul_mem hxT hxT)
      have hext : ext ϕ (c0 * c0 * w * (x * x)) ≠ 1 := by
        rw [ext_mul ϕ heT (T.mul_mem hxT hxT), ext_mul_self ϕ hxT, mul_one]; exact hew
      have hid : a1⁻¹ * (x * x) * a1 = c0 * c0 * w * (x * x) := by
        rw [hwdef, hc0def]; simp only [delta]; group
      have hx1 : x ≠ 1 := by
        rintro rfl; exact hϕx (ext_one ϕ)
      have hord : orderOf (c0 * c0 * w * (x * x)) < orderOf x := by
        rw [← hid, CFSG.RankThree.Transfer.orderOf_conj, ← pow_two,
          orderOf_pow_of_dvd (by norm_num) (two_dvd_orderOf hR hx1)]
        exact Nat.div_lt_self (orderOf_pos x) (by norm_num)
      exact hext (hd _ hmemT hord)
    ·
      have hψ2 : ext ϕ (c0 * c0) ≠ 1 := by
        have := key1 (a1 * a1) ha1sqA (by rw [hδsq]; exact hc0sqT) hI
        rwa [hδsq] at this
      have heq : ext ϕ (c0 * c0) = ext ϕ w := z2_eq_of_ne_one hψ2 hϕw
      obtain ⟨d1, hd1def⟩ : ∃ d1, d1 = a1 * a1 * c0⁻¹ := ⟨_, rfl⟩
      have hd1A : d1 ∈ A := by rw [hd1def]; exact A.mul_mem ha1sqA (A.inv_mem hc0A)
      have hd1C : d1 ∈ C0 hAc x ϕ := by
        refine ⟨hd1A, ?_, ?_⟩
        · rw [hd1def, delta_mul hAc ha1sqA (A.inv_mem hc0A), delta_inv hAc hc0A, hδsq, ← hwdef]
          exact T.mul_mem hc0sqT (T.inv_mem hwT)
        · rw [hd1def, delta_mul hAc ha1sqA (A.inv_mem hc0A), delta_inv hAc hc0A, hδsq, ← hwdef,
            ext_mul ϕ hc0sqT (T.inv_mem hwT), ext_inv ϕ hwT, heq, z2_mul_self]
      have hd1T : d1 ∈ T := hCT _ hd1C
      have e : a1 * a1 = d1 * c0 := by rw [hd1def]; group
      have h4 : a1 * a1 * (a1 * a1) = 1 := by
        have := hA4 a1 ha1A
        calc a1 * a1 * (a1 * a1) = a1 ^ 4 := by
              rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
          _ = 1 := this
      have hcomm : d1 * c0 = c0 * d1 := hAc _ hd1A _ hc0A
      have hprod : d1 * d1 * (c0 * c0) = 1 := by
        rw [e] at h4
        calc d1 * d1 * (c0 * c0) = d1 * (d1 * c0) * c0 := by group
          _ = d1 * (c0 * d1) * c0 := by rw [hcomm]
          _ = d1 * c0 * (d1 * c0) := by group
          _ = 1 := h4
      have hsq : c0 * c0 = (d1 * d1)⁻¹ := eq_inv_of_mul_eq_one_right hprod
      apply hψ2
      rw [hsq, ext_inv ϕ (T.mul_mem hd1T hd1T), ext_mul_self ϕ hd1T]
  obtain ⟨c, hcA, hcT, hcδ⟩ := hAnT
  have hψc : ext ϕ (delta x c) ≠ 1 := key1 c hcA hcδ hcT
  have hcover : ∀ u ∈ A, u ∈ T ∨ u * c⁻¹ ∈ T := by
    intro u hu
    by_cases huT : u ∈ T
    · exact Or.inl huT
    · right
      have hψu : ext ϕ (delta x u) ≠ 1 := key1 u hu (hall u hu) huT
      refine hCT _ ⟨A.mul_mem hu (A.inv_mem hcA), ?_, ?_⟩
      · rw [delta_mul hAc hu (A.inv_mem hcA), delta_inv hAc hcA]
        exact T.mul_mem (hall u hu) (T.inv_mem (hall c hcA))
      · rw [delta_mul hAc hu (A.inv_mem hcA), delta_inv hAc hcA,
          ext_mul ϕ (hall u hu) (T.inv_mem (hall c hcA)), ext_inv ϕ (hall c hcA),
          z2_eq_of_ne_one hψu hψc, z2_mul_self]
  refine ⟨?_, ⟨delta x c, delta_mem hcA, hcδ, hψc⟩, c, hcA, hcover⟩
  rw [Subgroup.index_eq_two_iff']
  refine ⟨c⁻¹, fun r => ?_⟩
  have hr : r ∈ A ⊔ T := by rw [hAT]; exact mem_top r
  obtain ⟨a, ha, t, ht, rfl⟩ := (mem_sup_of_normal_left (s := A) (t := T)).mp hr
  have hcov : a * t ∈ T ∨ c⁻¹ * (a * t) ∈ T := by
    rcases hcover a ha with h | h
    · exact Or.inl (T.mul_mem h ht)
    · right
      have : c⁻¹ * (a * t) = (a * c⁻¹) * t := by
        have hc := hAc _ (A.inv_mem hcA) _ ha
        rw [← mul_assoc, hc]
      rw [this]; exact T.mul_mem h ht
  have hnot : ¬ (c⁻¹ * (a * t) ∈ T ∧ a * t ∈ T) := by
    rintro ⟨h1, h2⟩
    have h3 : c⁻¹ ∈ T := by
      have h4 := T.mul_mem h1 (T.inv_mem h2)
      rwa [mul_inv_cancel_right] at h4
    exact hcT (by simpa using T.inv_mem h3)
  rcases hcov with h | h
  · exact Or.inr ⟨h, fun h' => hnot ⟨h', h⟩⟩
  · exact Or.inl ⟨h, fun h' => hnot ⟨h, h'⟩⟩

theorem endgame [Finite R] (hR : IsPGroup 2 R) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA4 : ∀ a ∈ A, a ^ 4 = 1) {x : R} (hgen : A ⊔ zpowers x = ⊤) (hT : T ≠ ⊤)
    {ϕ : T →* Z2} (hc : Odd (Nat.card (oddFixed ϕ x)))
    (hd : ∀ t ∈ T, orderOf t < orderOf x → ext ϕ t = 1) :
    T.index = 2 ∧ (∃ w ∈ A, w ∈ T ∧ ext ϕ w ≠ 1) ∧ ∃ c ∈ A, ∀ u ∈ A, u ∈ T ∨ u * c⁻¹ ∈ T := by
  have hAT := sup_eq_top hR hgen hc
  obtain ⟨a, haA, ha⟩ := exists_conj_mem hAT hc
  have hx'T : a⁻¹ * x * a ∈ T := mem_of_ext_ne_one ha
  have hc' : Odd (Nat.card (oddFixed ϕ (a⁻¹ * x * a))) := by
    rw [card_oddFixed_conj]; exact hc
  have hd' : ∀ t ∈ T, orderOf t < orderOf (a⁻¹ * x * a) → ext ϕ t = 1 := by
    intro t ht hlt
    apply hd t ht
    rwa [CFSG.RankThree.Transfer.orderOf_conj] at hlt
  exact core hR hAc hA4 hx'T ha hAT hT hc' hd'

end Core

end CFSG.CGT.PushingUpLit.T211
