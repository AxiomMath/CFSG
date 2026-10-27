module

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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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

namespace CFSG.ComponentClassification.GMS78.Finkelstein

theorem exists_ne_fixed_of_involutive {α : Type} [Finite α] {f : α → α}
    (hf : Function.Involutive f) (heven : 2 ∣ Nat.card α) {x₀ : α} (hx₀ : f x₀ = x₀) :
    ∃ x, x ≠ x₀ ∧ f x = x := by
  classical
  have := Fintype.ofFinite α
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F : Function.End α := f with hF
  have h2 : F ^ 2 ^ 1 = 1 := by
    funext x
    exact hf x
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) h2
  by_contra hne
  push Not at hne
  have hc : Fintype.card ↑(Function.fixedPoints F) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨x₀, hx₀⟩, fun ⟨x, hx⟩ => Subtype.ext ?_⟩
    by_contra hxx
    exact hne x hxx hx
  rw [hc] at hmod
  rw [Nat.card_eq_fintype_card] at heven
  unfold Nat.ModEq at hmod
  omega

variable {U : Type} [Group U]

@[expose] def fixSubgroup (t : MulAut U) : Subgroup U where
  carrier := {u | t u = u}
  mul_mem' := fun {a b} (ha : t a = a) (hb : t b = b) =>
    show t (a * b) = a * b by rw [map_mul, ha, hb]
  one_mem' := map_one t
  inv_mem' := fun {a} (ha : t a = a) => show t a⁻¹ = a⁻¹ by rw [map_inv, ha]

theorem mem_fixSubgroup {t : MulAut U} {u : U} : u ∈ fixSubgroup t ↔ t u = u := Iff.rfl

@[expose] def psi (t : MulAut U) (u : U) : U := u⁻¹ * t u

structure FinkHyp (U : Type) [Group U] (n : ℕ) (t y : MulAut U) : Prop where
  one_le : 1 ≤ n
  card : Nat.card U = 2 ^ (2 * n)
  sq : t ^ 2 = 1
  comm : t * y = y * t
  order : orderOf y = 2 ^ n - 1
  reg : ∀ a b : U, t a = a → t b = b → a ≠ 1 → b ≠ 1 →
    ∃! k : ℕ, k < 2 ^ n - 1 ∧ (y ^ k) a = b

theorem map_mem_center (s : MulAut U)
    {z : U} (hz : z ∈ Subgroup.center U) : s z ∈ Subgroup.center U := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  rw [← s.apply_symm_apply g, ← map_mul, ← map_mul, hz]

theorem two_dvd_natCard_center
    [Finite U] (hU : IsPGroup 2 U) [Nontrivial U] : 2 ∣ Nat.card (Subgroup.center U) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt := hU.center_nontrivial
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card.mp (hU.to_subgroup (Subgroup.center U)))
  have h1 : 1 < Nat.card (Subgroup.center U) := Finite.one_lt_card
  rw [hm] at h1 ⊢
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at h1
  exact dvd_pow_self 2 hm0

theorem psi_eq_one_iff {t : MulAut U} {u : U} : psi t u = 1 ↔ u ∈ fixSubgroup t := by
  rw [psi, inv_mul_eq_one, mem_fixSubgroup, eq_comm]

theorem mul_psi (t : MulAut U) (u : U) : u * psi t u = t u := by
  rw [psi, mul_inv_cancel_left]

namespace FinkHyp

variable {n : ℕ} {t y : MulAut U} (h : FinkHyp U n t y)
include h

theorem t_t (u : U) : t (t u) = u := by
  rw [← MulAut.mul_apply, (pow_two t).symm.trans h.sq, MulAut.one_apply]

theorem t_pow_y (k : ℕ) (u : U) : t ((y ^ k) u) = (y ^ k) (t u) := by
  rw [← MulAut.mul_apply, ← MulAut.mul_apply, ((Commute.pow_right h.comm k) : _ = _)]

theorem pow_mem_fix (k : ℕ) {a : U} (ha : a ∈ fixSubgroup t) : (y ^ k) a ∈ fixSubgroup t := by
  rw [mem_fixSubgroup, h.t_pow_y, ha]

theorem exists_pow_eq {a b : U} (ha : a ∈ fixSubgroup t) (hb : b ∈ fixSubgroup t) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) : ∃ k, (y ^ k) a = b := by
  obtain ⟨k, ⟨-, hk⟩, -⟩ := h.reg a b ha hb ha1 hb1
  exact ⟨k, hk⟩

theorem pow_eq_one_of_fix {k : ℕ} {a : U} (ha : a ∈ fixSubgroup t) (ha1 : a ≠ 1)
    (hk : (y ^ k) a = a) : y ^ k = 1 := by
  have hpos : 0 < 2 ^ n - 1 := by
    have := Nat.one_lt_two_pow (Nat.one_le_iff_ne_zero.mp h.one_le)
    omega
  obtain ⟨k₀, -, hu⟩ := h.reg a a ha ha ha1 ha1
  have h1 : 0 = k₀ := hu 0 ⟨hpos, by simp⟩
  have hmod : (y ^ (k % (2 ^ n - 1))) a = a := by rw [← h.order, pow_mod_orderOf, hk]
  have h2 : k % (2 ^ n - 1) = k₀ := hu _ ⟨Nat.mod_lt _ hpos, hmod⟩
  rw [← pow_mod_orderOf, h.order, h2, ← h1, pow_zero]

theorem isPGroup : IsPGroup 2 U := IsPGroup.of_card h.card

theorem finite : Finite U := Nat.finite_of_card_ne_zero (by rw [h.card]; positivity)

theorem exists_center_fix : ∃ z ∈ Subgroup.center U, z ≠ 1 ∧ t z = z := by
  have := h.finite
  have hnt : Nontrivial U := by
    rw [← Finite.one_lt_card_iff_nontrivial, h.card]
    exact Nat.one_lt_two_pow (by have := h.one_le; omega)
  set f : Subgroup.center U → Subgroup.center U := fun z => ⟨t z, map_mem_center t z.2⟩ with hf
  have hinv : Function.Involutive f := fun z => Subtype.ext (h.t_t z)
  obtain ⟨⟨z, hz⟩, hz1, hfz⟩ := exists_ne_fixed_of_involutive hinv
    (two_dvd_natCard_center h.isPGroup) (x₀ := 1) (Subtype.ext (map_one t))
  exact ⟨z, hz, fun h1 => hz1 (Subtype.ext h1), congrArg Subtype.val hfz⟩

theorem fix_le_center : fixSubgroup t ≤ Subgroup.center U := by
  obtain ⟨z, hz, hz1, hzt⟩ := h.exists_center_fix
  intro a ha
  by_cases ha1 : a = 1
  · rw [ha1]
    exact one_mem _
  obtain ⟨k, rfl⟩ := h.exists_pow_eq hzt ha hz1 ha1
  exact map_mem_center _ hz

theorem exists_fix_ne_one : ∃ a ∈ fixSubgroup t, a ≠ 1 := by
  obtain ⟨z, -, hz1, hzt⟩ := h.exists_center_fix
  exact ⟨z, hzt, hz1⟩

theorem natCard_fix : Nat.card (fixSubgroup t) = 2 ^ n := by
  obtain ⟨a₀, ha₀, ha₀1⟩ := h.exists_fix_ne_one
  set m := 2 ^ n - 1 with hm
  have hm1 : m + 1 = 2 ^ n := by
    have := Nat.one_le_two_pow (n := n)
    omega
  set g : Option (Fin m) → fixSubgroup t := fun o =>
    o.elim 1 fun k => ⟨(y ^ (k : ℕ)) a₀, h.pow_mem_fix k ha₀⟩ with hg
  have hne : ∀ k : ℕ, (y ^ k) a₀ ≠ 1 := fun k h1 => ha₀1 ((y ^ k).injective (h1.trans
    (map_one _).symm))
  have hinj : Function.Injective g := by
    rintro (_ | k) (_ | k') hkk
    · rfl
    · exact absurd (congrArg Subtype.val hkk).symm (hne k')
    · exact absurd (congrArg Subtype.val hkk) (hne k)
    · have hb := h.pow_mem_fix k ha₀
      obtain ⟨k₀, -, hu⟩ := h.reg a₀ _ ha₀ hb ha₀1 (hne k)
      have e1 := hu k ⟨k.2, rfl⟩
      have e2 := hu k' ⟨k'.2, (congrArg Subtype.val hkk).symm⟩
      exact congrArg some (Fin.ext (e1.trans e2.symm))
  have hsurj : Function.Surjective g := by
    rintro ⟨b, hb⟩
    by_cases hb1 : b = 1
    · exact ⟨none, Subtype.ext hb1.symm⟩
    obtain ⟨k, ⟨hk, hkb⟩, -⟩ := h.reg a₀ b ha₀ hb ha₀1 hb1
    exact ⟨some ⟨k, hk⟩, Subtype.ext hkb⟩
  rw [← Nat.card_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card,
    Fintype.card_option, Fintype.card_fin, hm1]

theorem mul_self_eq_one_of_mem_fix {a : U} (ha : a ∈ fixSubgroup t) : a * a = 1 := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card (fixSubgroup t) := by
    rw [h.natCard_fix]
    exact dvd_pow_self 2 (by have := h.one_le; omega)
  obtain ⟨a₁, ha₁⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have ha₁1 : (a₁ : U) ≠ 1 := by
    intro h1
    have : a₁ = 1 := Subtype.ext h1
    rw [this, orderOf_one] at ha₁
    exact absurd ha₁ (by norm_num)
  have ha₁2 : (a₁ : U) * a₁ = 1 := by
    have := pow_orderOf_eq_one a₁
    rw [ha₁, pow_two] at this
    exact congrArg Subtype.val this
  by_cases ha1 : a = 1
  · rw [ha1, mul_one]
  obtain ⟨k, rfl⟩ := h.exists_pow_eq a₁.2 ha ha₁1 ha1
  rw [← map_mul, ha₁2, map_one]

theorem mem_center_of_mem_fix {a : U} (ha : a ∈ fixSubgroup t) (g : U) : g * a = a * g :=
  Subgroup.mem_center_iff.mp (h.fix_le_center ha) g

theorem psi_pow_y (k : ℕ) (u : U) : psi t ((y ^ k) u) = (y ^ k) (psi t u) := by
  rw [psi, psi, h.t_pow_y, ← map_inv, ← map_mul]

theorem psi_mul_of_mem {u : U} (hu : psi t u ∈ fixSubgroup t) (v : U) :
    psi t (u * v) = psi t u * psi t v := by
  have hc := h.mem_center_of_mem_fix hu v⁻¹
  simp only [psi, map_mul, mul_inv_rev] at hc ⊢
  calc v⁻¹ * u⁻¹ * (t u * t v) = (v⁻¹ * (u⁻¹ * t u)) * t v := by group
    _ = ((u⁻¹ * t u) * v⁻¹) * t v := by rw [hc]
    _ = u⁻¹ * t u * (v⁻¹ * t v) := by group

theorem exists_psi_mem_fix_ne_one : ∃ u₀, psi t u₀ ∈ fixSubgroup t ∧ psi t u₀ ≠ 1 := by
  have := h.finite
  have hN : (fixSubgroup t).Normal := Subgroup.normal_of_le_center h.fix_le_center
  have hle : fixSubgroup t ≤ (fixSubgroup t).comap t.toMonoidHom := fun a ha => by
    rw [Subgroup.mem_comap]
    show t (t a) = t a
    rw [show t a = a from ha]
    exact ha
  set tb := QuotientGroup.map _ _ t.toMonoidHom hle with htb
  have htb_mk : ∀ u : U, tb (u : U ⧸ fixSubgroup t) = ((t u : U) : U ⧸ fixSubgroup t) :=
    fun u => QuotientGroup.map_mk _ _ _ hle u
  have hinv : Function.Involutive tb := fun x => by
    induction x using QuotientGroup.induction_on with
    | H u => rw [htb_mk, htb_mk, h.t_t]
  have hcard : Nat.card (U ⧸ fixSubgroup t) = 2 ^ n := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (fixSubgroup t)
    rw [h.card, h.natCard_fix, two_mul, pow_add] at h1
    exact (Nat.eq_of_mul_eq_mul_right (by positivity) h1).symm
  have heven : 2 ∣ Nat.card (U ⧸ fixSubgroup t) := by
    rw [hcard]
    exact dvd_pow_self 2 (by have := h.one_le; omega)
  obtain ⟨x, hx1, hx⟩ := exists_ne_fixed_of_involutive hinv heven (x₀ := 1) (map_one tb)
  obtain ⟨u₀, rfl⟩ := QuotientGroup.mk_surjective x
  rw [htb_mk] at hx
  have hmem : psi t u₀ ∈ fixSubgroup t := QuotientGroup.eq.mp hx.symm
  refine ⟨u₀, hmem, fun h1 => hx1 ?_⟩
  exact (QuotientGroup.eq_one_iff u₀).mpr (psi_eq_one_iff.mp h1)

@[expose] def bSub : Subgroup U where
  carrier := {u | psi t u ∈ fixSubgroup t}
  mul_mem' := fun {u v} hu hv => by
    show psi t (u * v) ∈ fixSubgroup t
    rw [h.psi_mul_of_mem hu]
    exact mul_mem hu hv
  one_mem' := by
    show psi t 1 ∈ fixSubgroup t
    rw [psi_eq_one_iff.mpr (one_mem _)]
    exact one_mem _
  inv_mem' := fun {u} hu => by
    show psi t u⁻¹ ∈ fixSubgroup t
    have h1 := h.psi_mul_of_mem hu u⁻¹
    rw [mul_inv_cancel, psi_eq_one_iff.mpr (one_mem _), eq_comm, mul_eq_one_iff_eq_inv'] at h1
    rw [h1]
    exact inv_mem hu

@[expose] def psiHom : h.bSub →* fixSubgroup t where
  toFun u := ⟨psi t u, u.2⟩
  map_one' := Subtype.ext (psi_eq_one_iff.mpr (one_mem _))
  map_mul' u v := Subtype.ext (h.psi_mul_of_mem u.2 v)

theorem psiHom_surjective : Function.Surjective h.psiHom := by
  obtain ⟨u₀, hu₀, hu₀1⟩ := h.exists_psi_mem_fix_ne_one
  rintro ⟨a, ha⟩
  by_cases ha1 : a = 1
  · exact ⟨1, Subtype.ext (by rw [map_one]; exact ha1.symm)⟩
  obtain ⟨k, hk⟩ := h.exists_pow_eq hu₀ ha hu₀1 ha1
  have hmem : (y ^ k) u₀ ∈ h.bSub := by
    show psi t ((y ^ k) u₀) ∈ fixSubgroup t
    rw [h.psi_pow_y]
    exact h.pow_mem_fix k hu₀
  exact ⟨⟨_, hmem⟩, Subtype.ext ((h.psi_pow_y k u₀).trans hk)⟩

theorem natCard_ker_psiHom : Nat.card h.psiHom.ker = Nat.card (fixSubgroup t) := by
  refine Nat.card_congr
    { toFun := fun u => ⟨((u : h.bSub) : U), psi_eq_one_iff.mp (congrArg Subtype.val u.2)⟩
      invFun := fun a => ⟨⟨a, show psi t a ∈ fixSubgroup t by
          rw [psi_eq_one_iff.mpr a.2]; exact one_mem _⟩,
        Subtype.ext (psi_eq_one_iff.mpr a.2)⟩
      left_inv := fun u => rfl
      right_inv := fun a => rfl }

theorem bSub_eq_top : h.bSub = ⊤ := by
  have := h.finite
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup h.psiHom.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ h.psiHom_surjective).toEquiv,
    h.natCard_ker_psiHom, h.natCard_fix, ← pow_add, ← two_mul, ← h.card] at h1
  exact Subgroup.eq_top_of_card_eq _ h1

theorem psi_mem_fix (u : U) : psi t u ∈ fixSubgroup t := by
  have hu : u ∈ h.bSub := h.bSub_eq_top ▸ Subgroup.mem_top u
  exact hu

theorem psi_mul (u v : U) : psi t (u * v) = psi t u * psi t v :=
  h.psi_mul_of_mem (h.psi_mem_fix u) v

theorem exists_psi_eq {a : U} (ha : a ∈ fixSubgroup t) : ∃ u, psi t u = a := by
  obtain ⟨u, hu⟩ := h.psiHom_surjective ⟨a, ha⟩
  exact ⟨u, congrArg Subtype.val hu⟩

theorem mul_self_mem_fix (u : U) : u * u ∈ fixSubgroup t := by
  have hψ := h.psi_mem_fix u
  rw [mem_fixSubgroup, map_mul, ← mul_psi t u]
  calc u * psi t u * (u * psi t u) = u * (psi t u * u) * psi t u := by group
    _ = u * (u * psi t u) * psi t u := by rw [h.mem_center_of_mem_fix hψ u]
    _ = u * u * (psi t u * psi t u) := by group
    _ = u * u := by rw [h.mul_self_eq_one_of_mem_fix hψ, mul_one]

theorem exists_eq_pow_mul {u₀ u : U} (hu₀ : u₀ ∉ fixSubgroup t) (hu : u ∉ fixSubgroup t) :
    ∃ j : ℕ, ∃ a ∈ fixSubgroup t, u = (y ^ j) u₀ * a ∧ psi t u = (y ^ j) (psi t u₀) := by
  have hu₀1 : psi t u₀ ≠ 1 := fun h1 => hu₀ (psi_eq_one_iff.mp h1)
  have hu1 : psi t u ≠ 1 := fun h1 => hu (psi_eq_one_iff.mp h1)
  obtain ⟨j, hj⟩ := h.exists_pow_eq (h.psi_mem_fix u₀) (h.psi_mem_fix u) hu₀1 hu1
  set v := (y ^ j) u₀
  have hv : psi t v = psi t u := (h.psi_pow_y j u₀).trans hj
  have hinv : psi t v⁻¹ = (psi t v)⁻¹ := by
    have h1 := h.psi_mul v v⁻¹
    rw [mul_inv_cancel, psi_eq_one_iff.mpr (one_mem _), eq_comm, mul_eq_one_iff_eq_inv'] at h1
    exact h1
  refine ⟨j, v⁻¹ * u, ?_, by rw [mul_inv_cancel_left], hj.symm⟩
  rw [← psi_eq_one_iff, h.psi_mul, hinv, hv, inv_mul_cancel]

theorem squares_cases : (∀ u : U, u * u = 1) ∨ ∃ k : ℕ, ∀ u : U, u * u = (y ^ k) (psi t u) := by
  obtain ⟨u₀, -, hu₀1⟩ := h.exists_psi_mem_fix_ne_one
  have hu₀ : u₀ ∉ fixSubgroup t := fun h1 => hu₀1 (psi_eq_one_iff.mpr h1)
  have hsq : ∀ u, u ∉ fixSubgroup t → ∃ j : ℕ, u * u = (y ^ j) (u₀ * u₀) ∧
      psi t u = (y ^ j) (psi t u₀) := by
    intro u hu
    obtain ⟨j, a, ha, rfl, hψ⟩ := h.exists_eq_pow_mul hu₀ hu
    refine ⟨j, ?_, hψ⟩
    calc (y ^ j) u₀ * a * ((y ^ j) u₀ * a) = (y ^ j) u₀ * (a * (y ^ j) u₀) * a := by group
      _ = (y ^ j) u₀ * ((y ^ j) u₀ * a) * a := by rw [h.mem_center_of_mem_fix ha ((y ^ j) u₀)]
      _ = (y ^ j) u₀ * (y ^ j) u₀ * (a * a) := by group
      _ = (y ^ j) (u₀ * u₀) := by rw [h.mul_self_eq_one_of_mem_fix ha, mul_one, map_mul]
  by_cases hb : u₀ * u₀ = 1
  · left
    intro u
    by_cases hu : u ∈ fixSubgroup t
    · exact h.mul_self_eq_one_of_mem_fix hu
    · obtain ⟨j, hj, -⟩ := hsq u hu
      rw [hj, hb, map_one]
  · right
    obtain ⟨k, hk⟩ := h.exists_pow_eq (h.psi_mem_fix u₀) (h.mul_self_mem_fix u₀) hu₀1 hb
    refine ⟨k, fun u => ?_⟩
    by_cases hu : u ∈ fixSubgroup t
    · rw [h.mul_self_eq_one_of_mem_fix hu, psi_eq_one_iff.mpr hu, map_one]
    · obtain ⟨j, hj, hψ⟩ := hsq u hu
      rw [hj, hψ, ← hk, ← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_add, ← pow_add, add_comm]

theorem mul_comm' (u v : U) : u * v = v * u := by
  have hsq : (u * v) * (u * v) = (u * u) * (v * v) := by
    rcases h.squares_cases with h1 | ⟨k, hk⟩
    · rw [h1, h1, h1, mul_one]
    · rw [hk, hk, hk, h.psi_mul, map_mul]
  have h2 : v * u = u * v := by
    have := hsq
    calc v * u = u⁻¹ * ((u * v) * (u * v)) * v⁻¹ := by group
      _ = u⁻¹ * ((u * u) * (v * v)) * v⁻¹ := by rw [this]
      _ = u * v := by group
  exact h2.symm

end FinkHyp

end CFSG.ComponentClassification.GMS78.Finkelstein
