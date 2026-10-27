module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
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
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.ClassicalInvolution.Q3.M

variable {C : Type*} [Group C] [Finite C]

omit [Finite C] in
theorem card_sup_mul_card_inf {A B : Subgroup C} (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  let μ : A × B →* C :=
    MonoidHom.noncommCoprod A.subtype B.subtype fun x y => hcomm x x.2 y y.2
  have hμ : ∀ x : A × B, μ x = (x.1 : C) * x.2 := fun _ => rfl
  have hrange : μ.range = A ⊔ B := by
    refine (MonoidHom.noncommCoprod_range A.subtype B.subtype _).trans ?_
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
  have hker : Nat.card μ.ker = Nat.card ↥(A ⊓ B) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : C), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : C)⁻¹, B.inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact B.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Subtype.ext (Prod.ext rfl (Subtype.ext h))
  have h := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at h
  rwa [mul_comm]

omit [Finite C] in
theorem eq_one_of_pow_two_pow_of_pow_three_pow {x : C} {k j : ℕ} (h2 : x ^ (2 ^ k) = 1)
    (h3 : x ^ (3 ^ j) = 1) : x = 1 := by
  have h := pow_gcd_eq_one.2 ⟨h2, h3⟩
  have hcop : Nat.Coprime (2 ^ k) (3 ^ j) :=
    Nat.Coprime.pow k j (by norm_num)
  rwa [hcop.gcd_eq_one, pow_one] at h

omit [Finite C] in
theorem card_eq_mul_relIndex {K H : Subgroup C} (hKH : K ≤ H) :
    Nat.card ↥K * K.relIndex H = Nat.card ↥H := by
  have hmul := (K.subgroupOf H).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv] at hmul
  exact hmul

theorem card_sylow_inf_normal (P : Sylow 3 C) (N : Subgroup C) [N.Normal] :
    Nat.card ↥((P : Subgroup C) ⊓ N) = 3 ^ (Nat.card N).factorization 3 ∧
      ¬ 3 ∣ ((P : Subgroup C) ⊓ N).relIndex N := by
  obtain ⟨Q, hQ⟩ := CFSG.Glauberman.sylow_inf_normal P (N := N)
  have hcard : Nat.card ↥(((P : Subgroup C) ⊓ N).subgroupOf N) =
      3 ^ (Nat.card N).factorization 3 := by
    rw [← hQ]
    exact Q.card_eq_multiplicity
  refine ⟨?_, ?_⟩
  · rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : (P : Subgroup C) ⊓ N ≤ N)).toEquiv]
    exact hcard
  · have h := Q.not_dvd_index
    have hidx : Q.index = ((P : Subgroup C) ⊓ N).relIndex N := by
      rw [Subgroup.relIndex, ← hQ]
    rwa [hidx] at h

theorem exists_sylow_sup_inf {U V : Subgroup C} [U.Normal] [V.Normal]
    (hcomm : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    (h2 : ∀ x ∈ U ⊓ V, ∃ k : ℕ, x ^ (2 ^ k) = 1)
    (h3 : ∀ x : C, (∃ k : ℕ, x ^ (3 ^ k) = 1) → ∃ u ∈ U, ∃ v ∈ V, x = u * v)
    (P P' : Sylow 3 C) :
    ∃ Q : Sylow 3 C, (Q : Subgroup C) = ((P : Subgroup C) ⊓ U) ⊔ ((P' : Subgroup C) ⊓ V) := by
  set A : Subgroup C := (P : Subgroup C) ⊓ U with hA
  set B : Subgroup C := (P' : Subgroup C) ⊓ V with hB
  have hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := fun x hx y hy => hcomm x hx.2 y hy.2
  have hAB1 : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨k, hk⟩ := h2 x ⟨hx.1.2, hx.2.2⟩
    obtain ⟨j, hj⟩ := P.isPGroup' ⟨x, hx.1.1⟩
    exact (Subgroup.mem_bot.mpr (eq_one_of_pow_two_pow_of_pow_three_pow hk
      (by simpa using congrArg Subtype.val hj)))
  have hcardAB : Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
    have := card_sup_mul_card_inf hAB
    rwa [hAB1, Subgroup.card_bot, mul_one] at this
  obtain ⟨hAc, hAi⟩ := card_sylow_inf_normal P U
  obtain ⟨hBc, hBi⟩ := card_sylow_inf_normal P' V
  have hPle : (P : Subgroup C) ≤ U ⊔ V := by
    intro x hx
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := h3 x ⟨k, by simpa using congrArg Subtype.val hk⟩
    exact Subgroup.mul_mem_sup hu hv
  have hdvd1 : Nat.card ↥(P : Subgroup C) ∣ Nat.card ↥(U ⊔ V) := Subgroup.card_dvd_of_le hPle
  have hUV : Nat.card ↥(U ⊔ V) ∣ Nat.card ↥U * Nat.card ↥V :=
    Dvd.intro _ (card_sup_mul_card_inf hcomm)
  have hU' := card_eq_mul_relIndex (inf_le_right : (P : Subgroup C) ⊓ U ≤ U)
  have hV' := card_eq_mul_relIndex (inf_le_right : (P' : Subgroup C) ⊓ V ≤ V)
  have hPcard : Nat.card ↥(P : Subgroup C) = 3 ^ (Nat.card C).factorization 3 :=
    P.card_eq_multiplicity
  have hcop : Nat.Coprime (Nat.card ↥(P : Subgroup C))
      (((P : Subgroup C) ⊓ U).relIndex U * ((P' : Subgroup C) ⊓ V).relIndex V) := by
    rw [hPcard]
    refine Nat.Coprime.pow_left _ (Nat.Coprime.mul_right ?_ ?_)
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hAi
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hBi
  have hdvd2 : Nat.card ↥(P : Subgroup C) ∣ Nat.card ↥A * Nat.card ↥B := by
    have h := hdvd1.trans hUV
    rw [← hU', ← hV'] at h
    have h' : Nat.card ↥(P : Subgroup C) ∣
        (Nat.card ↥A * Nat.card ↥B) *
          (((P : Subgroup C) ⊓ U).relIndex U * ((P' : Subgroup C) ⊓ V).relIndex V) := by
      convert h using 1
      ring
    exact hcop.dvd_of_dvd_mul_right h'
  have hpos : 0 < Nat.card ↥A * Nat.card ↥B := Nat.mul_pos Nat.card_pos Nat.card_pos
  have hle1 : Nat.card ↥(P : Subgroup C) ≤ Nat.card ↥(A ⊔ B) := by
    rw [hcardAB]
    exact Nat.le_of_dvd hpos hdvd2
  have hpg : IsPGroup 3 ↥(A ⊔ B) :=
    IsPGroup.of_card (n := (Nat.card U).factorization 3 + (Nat.card V).factorization 3) (by
      rw [hcardAB, hAc, hBc, pow_add])
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  refine ⟨Q, (Subgroup.eq_of_le_of_card_ge hQ ?_).symm⟩
  have hQc : Nat.card ↥(Q : Subgroup C) = Nat.card ↥(P : Subgroup C) := by
    rw [Q.card_eq_multiplicity, hPcard]
  rw [hQc]
  exact hle1

end CFSG.ClassicalInvolution.Q3.M
