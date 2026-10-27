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
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

public section

namespace CFSG.LargeExtraspecial.S11

open Module Equiv Subgroup
open scoped Pointwise

theorem nat_card_alternating_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem card_le_four_of_isPGroup_alternating {T : Subgroup (alternatingGroup (Fin 5))}
    (hT : IsPGroup 2 T) : Nat.card T ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  have hdvd : Nat.card T ∣ 60 := by
    have := T.card_subgroup_dvd_card
    rwa [nat_card_alternating_five] at this
  rw [hn] at hdvd ⊢
  by_contra hlt
  have h3 : 3 ≤ n := by
    by_contra h
    interval_cases n <;> simp_all
  have h8 : 2 ^ 3 ∣ 60 := (pow_dvd_pow 2 h3).trans hdvd
  norm_num at h8

theorem card_le_two_of_isPGroup_perm_three {T : Subgroup (Perm (Fin 3))} (hT : IsPGroup 2 T) :
    Nat.card T ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  have h6 : Nat.card (Perm (Fin 3)) = 6 := by rw [Nat.card_perm, Nat.card_fin]; decide
  have hdvd : Nat.card T ∣ 6 := by
    have := T.card_subgroup_dvd_card
    rwa [h6] at this
  rw [hn] at hdvd ⊢
  by_contra hlt
  have h2 : 2 ≤ n := by
    by_contra h
    interval_cases n <;> simp_all
  have h4 : 2 ^ 2 ∣ 6 := (pow_dvd_pow 2 h2).trans hdvd
  norm_num at h4

theorem sign_swap_mul_swap {a b c d : Fin 5} (h1 : a ≠ b) (h2 : c ≠ d) :
    Perm.sign (swap a b * swap c d) = 1 := by
  rw [Perm.sign_mul, Perm.sign_swap h1, Perm.sign_swap h2, Int.units_mul_self]

private def a5a : alternatingGroup (Fin 5) :=
  ⟨swap 0 1 * swap 2 3, Perm.mem_alternatingGroup.mpr (sign_swap_mul_swap (by decide) (by decide))⟩

private def a5b : alternatingGroup (Fin 5) :=
  ⟨swap 0 2 * swap 1 3, Perm.mem_alternatingGroup.mpr (sign_swap_mul_swap (by decide) (by decide))⟩

private def a5c : alternatingGroup (Fin 5) :=
  ⟨swap 0 1 * swap 1 2, Perm.mem_alternatingGroup.mpr (sign_swap_mul_swap (by decide) (by decide))⟩

private def kleinV : Subgroup (alternatingGroup (Fin 5)) where
  carrier := {x | x = 1 ∨ x = a5a ∨ x = a5b ∨ x = a5a * a5b}
  mul_mem' := by
    rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;> decide
  one_mem' := Or.inl rfl
  inv_mem' := by
    rintro x (rfl | rfl | rfl | rfl) <;> decide

private theorem mem_kleinV {t : alternatingGroup (Fin 5)} :
    t ∈ kleinV ↔ t = 1 ∨ t = a5a ∨ t = a5b ∨ t = a5a * a5b :=
  Iff.rfl

private theorem card_kleinV : Nat.card kleinV = 4 := by
  have e : Nat.card kleinV = Nat.card ((({1, a5a, a5b, a5a * a5b} :
      Finset (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5)))) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      exact Iff.rfl)
  rw [e, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  decide

private theorem kleinV_conj_mem {t : alternatingGroup (Fin 5)} (ht : t ∈ kleinV) :
    a5c * t * a5c⁻¹ ∈ kleinV := by
  rw [mem_kleinV] at ht ⊢
  rcases ht with rfl | rfl | rfl | rfl <;> decide

private theorem kleinV_fixfree {t : alternatingGroup (Fin 5)} (ht : t ∈ kleinV)
    (h : a5c * t * a5c⁻¹ = t) : t = 1 := by
  rw [mem_kleinV] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · rfl
  all_goals exact absurd h (by decide)

private theorem exists_sylow_eq {U : Subgroup (alternatingGroup (Fin 5))} (hU : Nat.card U = 4) :
    ∃ P : Sylow 2 (alternatingGroup (Fin 5)), (P : Subgroup (alternatingGroup (Fin 5))) = U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [hU]; norm_num)
  obtain ⟨P, hUP⟩ := hU2.exists_le_sylow
  refine ⟨P, (Subgroup.eq_of_le_of_card_ge hUP ?_).symm⟩
  rw [hU]
  exact card_le_four_of_isPGroup_alternating P.isPGroup'

theorem exists_conj_fixfree_alternating {T : Subgroup (alternatingGroup (Fin 5))}
    (hT : Nat.card T = 4) :
    ∃ c : alternatingGroup (Fin 5), (∀ t ∈ T, c * t * c⁻¹ ∈ T) ∧
      ∀ t ∈ T, c * t * c⁻¹ = t → t = 1 := by
  obtain ⟨P, hP⟩ := exists_sylow_eq hT
  obtain ⟨P₀, hP₀⟩ := exists_sylow_eq card_kleinV
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) P₀ P
  have hmem : ∀ t, t ∈ T ↔ x⁻¹ * t * x ∈ kleinV := by
    intro t
    rw [← hP, ← hx, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hP₀,
      MulAut.smul_def, MulAut.conj_inv_apply]
  refine ⟨x * a5c * x⁻¹, fun t ht => ?_, fun t ht htc => ?_⟩
  · rw [hmem] at ht ⊢
    have h1 := kleinV_conj_mem ht
    rwa [show x⁻¹ * (x * a5c * x⁻¹ * t * (x * a5c * x⁻¹)⁻¹) * x =
      a5c * (x⁻¹ * t * x) * a5c⁻¹ by group]
  · rw [hmem] at ht
    have h1 : a5c * (x⁻¹ * t * x) * a5c⁻¹ = x⁻¹ * t * x := by
      calc a5c * (x⁻¹ * t * x) * a5c⁻¹ =
            x⁻¹ * (x * a5c * x⁻¹ * t * (x * a5c * x⁻¹)⁻¹) * x := by group
        _ = x⁻¹ * t * x := by rw [htc]
    have h2 := kleinV_fixfree ht h1
    calc t = x * (x⁻¹ * t * x) * x⁻¹ := by group
      _ = 1 := by rw [h2]; group

theorem apply_eq_self_of_pow_five {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (hd : finrank (ZMod 2) W ≤ 3) {f : W ≃ₗ[ZMod 2] W} (hf : f ^ 5 = 1) (w : W) : f w = w := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rcases (Nat.dvd_prime Nat.prime_five).mp (orderOf_dvd_of_pow_eq_one hf) with h1 | h5
  · rw [orderOf_eq_one_iff.mp h1]
    rfl
  have hG : IsPGroup 5 (Subgroup.zpowers f) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h5, pow_one])
  have hmod := hG.card_modEq_card_fixedPoints W
  set K : Submodule (ZMod 2) W := LinearMap.ker ((f : W →ₗ[ZMod 2] W) - LinearMap.id)
  have hfix : ∀ v, v ∈ MulAction.fixedPoints (Subgroup.zpowers f) W ↔ v ∈ K := by
    intro v
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.id_apply]
    constructor
    · intro h
      exact h ⟨f, Subgroup.mem_zpowers f⟩
    · intro h g
      have hs : f ∈ MulAction.stabilizer (W ≃ₗ[ZMod 2] W) v := h
      exact (Subgroup.zpowers_le.mpr hs) g.2
  have hK : Nat.card (MulAction.fixedPoints (Subgroup.zpowers f) W) = Nat.card K :=
    Nat.card_congr (Equiv.subtypeEquivRight hfix)
  have hcW := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
  have hcK := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)
  rw [Nat.card_zmod] at hcW hcK
  have hdK : finrank (ZMod 2) K ≤ finrank (ZMod 2) W := Submodule.finrank_le K
  rw [hK, hcK, hcW] at hmod
  have hKt : finrank (ZMod 2) K = finrank (ZMod 2) W := by
    generalize finrank (ZMod 2) K = e at hmod hdK ⊢
    generalize finrank (ZMod 2) W = d at hmod hdK hd ⊢
    interval_cases d <;> interval_cases e <;> first | rfl | (norm_num [Nat.ModEq] at hmod)
  have hw : w ∈ K := (Submodule.eq_top_of_finrank_eq hKt) ▸ Submodule.mem_top
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.id_apply] at hw
  exact hw

theorem card_eq_card_inf_mul_card_range {H K : Type*} [Group H] [Group K] [Finite H]
    {X L O : Subgroup H} (hLX : L ≤ X) (φ : ↥X →* K) (hφ : φ.ker = O.subgroupOf X) :
    Nat.card L = Nat.card (L ⊓ O : Subgroup H) * Nat.card (φ.comp (inclusion hLX)).range := by
  have hker : (φ.comp (inclusion hLX)).ker = O.subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hφ, mem_subgroupOf,
      mem_subgroupOf, Subgroup.coe_inclusion]
  have h1 : Nat.card (φ.comp (inclusion hLX)).ker * Nat.card (φ.comp (inclusion hLX)).range =
      Nat.card L := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [← h1, hker, ← inf_subgroupOf_right,
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : O ⊓ L ≤ L)).toEquiv, inf_comm]

end CFSG.LargeExtraspecial.S11
