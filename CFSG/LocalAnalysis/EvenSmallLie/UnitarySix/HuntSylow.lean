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
public import Mathlib.Tactic.Basify
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

namespace CFSG.EvenSmallLie.UnitarySix.Hunt

open Subgroup

theorem card_sylow_of_card_eq {K : Type*} [Group K] [Finite K] {p n m : ℕ} [hp : Fact p.Prime]
    (hK : Nat.card K = p ^ n * m) (hm : ¬p ∣ m) (P : Sylow p K) : Nat.card P = p ^ n := by
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero p)
  rw [P.card_eq_multiplicity, hK, Nat.factorization_mul (pow_ne_zero _ hp.out.ne_zero) hm0,
    Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, hp.out.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd hm, smul_eq_mul, mul_one, add_zero]

theorem four_dvd_card_support {α : Type*} [Fintype α] [DecidableEq α] {σ : Equiv.Perm α}
    (h2 : σ ^ 2 = 1) (hs : Equiv.Perm.sign σ = 1) : 4 ∣ σ.support.card := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := Equiv.Perm.cycleType_of_pow_prime_eq_one h2
  set k := Multiset.card σ.cycleType
  have hsum : σ.support.card = k * 2 := by
    rw [← Equiv.Perm.sum_cycleType, hc, Multiset.sum_replicate, smul_eq_mul]
  have hsign := Equiv.Perm.sign_of_cycleType σ
  rw [hs, hc, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul] at hsign
  have he : Even (k * 2 + k) := by
    rcases Nat.even_or_odd (k * 2 + k) with h | h
    · exact h
    · rw [h.neg_one_pow] at hsign
      exact absurd hsign (by decide)
  have hk : Even k := by
    have h2k : Even (k * 2) := even_two.mul_left k
    exact (Nat.even_add.1 he).1 h2k
  obtain ⟨j, hj⟩ := hk
  rw [hsum, hj]
  exact ⟨j, by ring⟩

variable {G : Type} [Group G]

@[expose] def conjClassPerm (t g : G) : Equiv.Perm {s : G // IsConj t s} where
  toFun s := ⟨g * s * g⁻¹, s.2.trans (isConj_iff.2 ⟨g, rfl⟩)⟩
  invFun s := ⟨g⁻¹ * s * g, s.2.trans (isConj_iff.2 ⟨g⁻¹, by rw [inv_inv]⟩)⟩
  left_inv s := Subtype.ext (by simp [mul_assoc])
  right_inv s := Subtype.ext (by simp [mul_assoc])

@[expose] def conjClassHom (t : G) : G →* Equiv.Perm {s : G // IsConj t s} where
  toFun := conjClassPerm t
  map_one' := Equiv.ext fun s => Subtype.ext (by simp [conjClassPerm])
  map_mul' g h := Equiv.ext fun s => Subtype.ext (by
    simp only [conjClassPerm, Equiv.coe_fn_mk, Equiv.Perm.mul_apply, mul_inv_rev]
    group)

theorem coe_conjClassHom_apply (t g : G) (s : {s : G // IsConj t s}) :
    ((conjClassHom t g s : {s : G // IsConj t s}) : G) = g * s * g⁻¹ := rfl

theorem sign_conjPerm_eq_one [Finite G] (t : G) [Fintype {s : G // IsConj t s}]
    [DecidableEq {s : G // IsConj t s}] (hG : ∀ K : Subgroup G, K.index ≠ 2) (g : G) :
    Equiv.Perm.sign (conjClassHom t g) = 1 := by
  set ψ := Equiv.Perm.sign.comp (conjClassHom t)
  have hle : ψ.ker.index ≤ 2 := by
    rw [index_ker]
    calc Nat.card ψ.range ≤ Nat.card ℤˣ := card_le_card_group _
      _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  have h0 : ψ.ker.index ≠ 0 := index_ne_zero_of_finite
  have h1 : ψ.ker.index = 1 := by
    have := hG ψ.ker
    omega
  have hg : g ∈ ψ.ker := by
    rw [index_eq_one.1 h1]
    exact mem_top g
  exact hg

theorem ncard_isConj_eq_index [Finite G] (t : G) :
    {s : G | IsConj t s}.ncard = (centralizer ({t} : Set G)).index := by
  have h1 : {s : G | IsConj t s} = MulAction.orbit (ConjAct G) t := by
    ext s
    rw [Set.mem_ofPred_eq, ConjAct.mem_orbit_conjAct, isConj_comm]
  rw [h1, ← MulAction.index_stabilizer, centralizer_eq_comap_stabilizer]
  exact (index_comap_of_surjective (MulAction.stabilizer (ConjAct G) t)
    (f := ConjAct.toConjAct.toMonoidHom) ConjAct.toConjAct.surjective).symm

theorem card_sylow_of_fixed [Finite G] (hG : ∀ K : Subgroup G, K.index ≠ 2) {t : G}
    (ht : orderOf t = 2) (hfix : {s : G | IsConj t s ∧ s * t = t * s}.ncard = 694)
    (hC : Nat.card (centralizer ({t} : Set G)) = 2 ^ 16 * 280665) (P : Sylow 2 G) :
    Nat.card P = 2 ^ 17 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype {s : G // IsConj t s} := Fintype.ofFinite _
  set σ := conjClassHom t t
  have h2 : σ ^ 2 = 1 := by
    rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]
  have h4 := four_dvd_card_support h2 (sign_conjPerm_eq_one t hG t)
  have hfixσ : (Finset.univ.filter fun s => σ s = s).card = 694 := by
    rw [← hfix]
    have e : {s : G | IsConj t s ∧ s * t = t * s} = Subtype.val ''
        ((Finset.univ.filter fun s => σ s = s : Finset _) : Set {s : G // IsConj t s}) := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hs, hst⟩
        refine ⟨⟨s, hs⟩, Subtype.ext ?_, rfl⟩
        rw [coe_conjClassHom_apply, ← hst, mul_inv_cancel_right]
      · rintro ⟨x, hx, rfl⟩
        refine ⟨x.2, ?_⟩
        have hx' := congrArg Subtype.val hx
        rw [coe_conjClassHom_apply] at hx'
        calc (x : G) * t = t * x * t⁻¹ * t := by rw [hx']
          _ = t * x := by group
    rw [e, Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset]
  have hcard : σ.support.card + 694 = Fintype.card {s : G // IsConj t s} := by
    rw [← hfixσ, Equiv.Perm.support, add_comm, Finset.card_filter_add_card_filter_not,
      Finset.card_univ]
  have hidx : Fintype.card {s : G // IsConj t s} = (centralizer ({t} : Set G)).index := by
    rw [← ncard_isConj_eq_index, ← Nat.card_eq_fintype_card, ← Nat.card_coe_set_eq]
    rfl
  have hG' : Nat.card G = (centralizer ({t} : Set G)).index * Nat.card (centralizer {t}) :=
    (index_mul_card _).symm
  obtain ⟨j, hj⟩ := h4
  refine card_sylow_of_card_eq (n := 17) (m := (347 + 2 * j) * 280665) ?_ (by omega) P
  rw [hG', ← hidx, ← hcard, hj, hC]
  ring

theorem card_sylow_normalizer [Finite G] {E : Subgroup G}
    (hN : Nat.card (normalizer (E : Set G)) = 2 ^ 10 * 443520)
    (T : Sylow 2 (normalizer (E : Set G))) : Nat.card T = 2 ^ 17 :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  card_sylow_of_card_eq (m := 3465) (by rw [hN]; norm_num) (by norm_num) T

end CFSG.EvenSmallLie.UnitarySix.Hunt
