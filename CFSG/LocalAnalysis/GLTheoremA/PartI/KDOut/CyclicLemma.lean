module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.GLTheoremA

theorem mulAut_apply_eq_of_isCyclic_two {C : Type*} [Group C] [Finite C] [IsCyclic C] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {φ : MulAut C} {k : ℕ} (hφ : φ ^ (p ^ k) = 1) {x : C} {m : ℕ}
    (hx : x ^ (2 ^ m) = 1) : φ x = x := by
  have hmem : φ x ∈ Subgroup.zpowers x := by
    have hord : orderOf (φ x) = orderOf x := orderOf_injective φ.toMonoidHom φ.injective x
    have heq : Subgroup.zpowers (φ x) = Subgroup.zpowers x := by
      rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers]
      exact hord
    rw [← heq]
    exact Subgroup.mem_zpowers _
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hφz : ∀ a : ℤ, φ (x ^ a) = x ^ (i * a) := by
    intro a
    rw [map_zpow, ← hi, ← zpow_mul]
  have hiter : ∀ t : ℕ, (φ ^ t) x = x ^ (i ^ t) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ' φ t, MulAut.mul_apply, ih, hφz, pow_succ' i t]
  have hfix : x ^ (i ^ (p ^ k)) = x := by
    have h := hiter (p ^ k)
    rw [hφ, MulAut.one_apply] at h
    exact h.symm
  have hdvd : (orderOf x : ℤ) ∣ i ^ (p ^ k) - 1 :=
    orderOf_dvd_iff_zpow_eq_one.2 (by rw [zpow_sub_one, hfix, mul_inv_cancel])
  have hZ : (i : ZMod (orderOf x)) ^ (p ^ k) = 1 := by
    have h1 : ((i ^ (p ^ k) - 1 : ℤ) : ZMod (orderOf x)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdvd
    push_cast at h1
    exact sub_eq_zero.1 h1
  have hunit : IsUnit (i : ZMod (orderOf x)) :=
    IsUnit.of_pow_eq_one hZ (pow_ne_zero k hp.ne_zero)
  have hEuler : (i : ZMod (orderOf x)) ^ Nat.totient (orderOf x) = 1 := by
    have h := congrArg Units.val (ZMod.pow_totient hunit.unit)
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at h
    exact h
  have hcop : Nat.Coprime (p ^ k) (Nat.totient (orderOf x)) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hx)
    have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
    rcases j with _ | j
    · rw [hj, pow_zero, Nat.totient_one]
      exact Nat.coprime_one_right _
    · rw [hj, Nat.totient_prime_pow_succ Nat.prime_two, show (2 : ℕ) - 1 = 1 from rfl, mul_one]
      exact Nat.Coprime.pow k j hcop2
  have hi1 : (i : ZMod (orderOf x)) = 1 := by
    have h : (i : ZMod (orderOf x)) ^ (Nat.gcd (p ^ k) (Nat.totient (orderOf x))) = 1 :=
      pow_gcd_eq_one.2 ⟨hZ, hEuler⟩
    rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h
    exact h
  have hdvd1 : (orderOf x : ℤ) ∣ i - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (i - 1) (orderOf x)).1
    push_cast
    rw [hi1, sub_self]
  have h1 : x ^ (i - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.1 hdvd1
  rw [zpow_sub_one] at h1
  rw [← hi]
  exact mul_inv_eq_one.1 h1

theorem commutator_mem_of_isCyclic_quotient_two {G : Type*} [Group G] [Finite G]
    {D I : Subgroup G} [D.Normal] [I.Normal] (hcyc : IsCyclic (D ⧸ I.subgroupOf D)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {α : G} {k : ℕ} (hα : α ^ (p ^ k) = 1) {δ : G} (hδ : δ ∈ D)
    {m : ℕ} (hm : δ ^ (2 ^ m) ∈ I) : α * δ * α⁻¹ * δ⁻¹ ∈ I := by
  set N := I.subgroupOf D with hN
  let c : G →* MulAut D := MulAut.conjNormal
  have hcN : ∀ g : G, N.map (c g).toMonoidHom = N := by
    intro g
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change (c g x : G) ∈ I
      rw [MulAut.conjNormal_apply]
      exact ‹I.Normal›.conj_mem _ hx g
    · intro x hx
      refine ⟨(c g)⁻¹ x, ?_, by simp⟩
      change (((c g)⁻¹ x : D) : G) ∈ I
      rw [MulAut.conjNormal_inv_apply]
      have := ‹I.Normal›.conj_mem _ hx g⁻¹
      rwa [inv_inv] at this
  let φ : MulAut (D ⧸ N) := QuotientGroup.congr N N (c α) (hcN α)
  have hφ : ∀ (j : ℕ) (x : D), (φ ^ j) (x : D ⧸ N) = ((c α ^ j) x : D ⧸ N) := by
    intro j
    induction j with
    | zero => intro x; rfl
    | succ j ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, ih, pow_succ', MulAut.mul_apply]
      exact QuotientGroup.congr_mk' N N (c α) (hcN α) _
  have hpow : φ ^ (p ^ k) = 1 := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [hφ, ← map_pow, hα, map_one]
      rfl
  have hx : ((⟨δ, hδ⟩ : D) : D ⧸ N) ^ (2 ^ m) = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.2 (by simpa using hm)
  have h4 : φ ((⟨δ, hδ⟩ : D) : D ⧸ N) = ((⟨δ, hδ⟩ : D) : D ⧸ N) :=
    mulAut_apply_eq_of_isCyclic_two hp hp2 hpow hx
  have h5 := hφ 1 ⟨δ, hδ⟩
  rw [pow_one, pow_one, h4] at h5
  have h6 := (QuotientGroup.eq).1 h5
  have h7 : δ⁻¹ * (α * δ * α⁻¹) ∈ I := by
    have := Subgroup.mem_subgroupOf.1 h6
    have e1 : ((c α ⟨δ, hδ⟩ : D) : G) = α * δ * α⁻¹ := MulAut.conjNormal_apply α ⟨δ, hδ⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, e1] at this
    exact this
  have h8 := ‹I.Normal›.conj_mem _ h7 δ
  have h9 : δ * (δ⁻¹ * (α * δ * α⁻¹)) * δ⁻¹ = α * δ * α⁻¹ * δ⁻¹ := by group
  rwa [h9] at h8

end CFSG.LocalAnalysis.GLTheoremA
