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
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
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

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup

theorem no_subgroup_card_840 {α : Type*} [Finite α] [DecidableEq α] (hα : Nat.card α = 7)
    (K : Subgroup (Equiv.Perm α)) : Nat.card K ≠ 840 := by
  classical
  intro hK
  have : Fintype α := Fintype.ofFinite α
  have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.1 (by rw [hα]; norm_num)
  have hperm : Nat.card (Equiv.Perm α) = 5040 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hα]
    decide
  have hA : Nat.card (alternatingGroup α) = 2520 := by
    rw [nat_card_alternatingGroup, hα]
    decide
  have hsimple : IsSimpleGroup (alternatingGroup α) :=
    alternatingGroup.isSimpleGroup (by rw [hα]; norm_num)
  have hidx : K.index = 6 := by
    have := K.card_mul_index
    rw [hperm, hK] at this
    omega
  have hcos : Nat.card (Equiv.Perm α ⧸ K) = 6 := by rw [← Subgroup.index, hidx]
  let f : alternatingGroup α →* Equiv.Perm (Equiv.Perm α ⧸ K) :=
    MulAction.toPermHom (alternatingGroup α) (Equiv.Perm α ⧸ K)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h0 | h0
  · have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).1 h0
    have hle := Nat.card_le_card_of_injective f hinj
    have : Finite (Equiv.Perm α ⧸ K) := Nat.finite_of_card_ne_zero (by rw [hcos]; norm_num)
    have := Fintype.ofFinite (Equiv.Perm α ⧸ K)
    rw [hA, Nat.card_eq_fintype_card (α := Equiv.Perm (Equiv.Perm α ⧸ K)), Fintype.card_perm,
      ← Nat.card_eq_fintype_card, hcos] at hle
    revert hle
    decide
  · have hle : alternatingGroup α ≤ K := by
      intro a ha
      have h1 : f ⟨a, ha⟩ = 1 := by
        have : (⟨a, ha⟩ : alternatingGroup α) ∈ f.ker := by rw [h0]; exact Subgroup.mem_top _
        exact this
      have h2 := congrArg (fun σ : Equiv.Perm (Equiv.Perm α ⧸ K) =>
        σ (((1 : Equiv.Perm α) : Equiv.Perm α ⧸ K))) h1
      simp only [Equiv.Perm.coe_one, id_eq] at h2
      have h3 : ((a * 1 : Equiv.Perm α) : Equiv.Perm α ⧸ K) =
          ((1 : Equiv.Perm α) : Equiv.Perm α ⧸ K) :=
        h2
      rw [QuotientGroup.eq] at h3
      simpa using h3
    have := Subgroup.card_le_of_le hle
    rw [hA, hK] at this
    omega

theorem false_of_prime_dvd {G : Type*} [Group G] [Finite G] (E N : Subgroup G)
    (hE : Nat.card E = 64) (hNE : ∀ n ∈ N, ∀ x ∈ E, n * x * n⁻¹ ∈ E)
    (hCE : ∀ n ∈ N, (∀ x ∈ E, n * x = x * n) → n ∈ E)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hmod : ∀ j < 6, ¬ 64 ≡ 2 ^ j [MOD p])
    (hdvd : p ∣ Nat.card N) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype E := Fintype.ofFinite E
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := N) p hdvd
  have hgN : (g : G) ∈ N := g.2
  have hg' : orderOf (g : G) = p := by rw [Subgroup.orderOf_coe]; exact hg
  have hginv : (g : G)⁻¹ ∈ N := N.inv_mem hgN
  have hiff : ∀ x : G, x ∈ E ↔ (g : G) * x * (g : G)⁻¹ ∈ E := fun x =>
    ⟨hNE _ hgN x, fun h => by
      have := hNE _ hginv _ h
      simpa [mul_assoc] using this⟩
  let σ : Equiv.Perm E := Equiv.subtypeEquiv (MulAut.conj (g : G)).toEquiv hiff
  have hσk : ∀ (k : ℕ) (x : E), (((σ ^ k) x : E) : G) = (g : G) ^ k * x * ((g : G) ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, ih]
      simp only [σ, Equiv.subtypeEquiv_apply, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
        MulAut.conj_apply, pow_succ, mul_inv_rev, mul_assoc]
  have hσp : σ ^ p ^ 1 = 1 := by
    ext x
    rw [pow_one, Equiv.Perm.one_apply, hσk, ← hg', pow_orderOf_eq_one]
    simp
  have hmodeq := Equiv.Perm.card_compl_support_modEq (p := p) (n := 1) hσp
  set C : Subgroup G := E ⊓ Subgroup.centralizer ({(g : G)} : Set G) with hC
  have hfix : ∀ x : E, x ∈ σ.supportᶜ ↔ (g : G) * x = x * (g : G) := by
    intro x
    rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Subtype.ext_iff]
    exact mul_inv_eq_iff_eq_mul
  have hCcard : σ.supportᶜ.card = Nat.card C := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : G), x.1.2, Subgroup.mem_centralizer_singleton_iff.2
          ((hfix x.1).1 x.2).symm⟩
        invFun := fun c => ⟨⟨c.1, c.2.1⟩, (hfix ⟨c.1, c.2.1⟩).2
          (Subgroup.mem_centralizer_singleton_iff.1 c.2.2).symm⟩
        left_inv := fun x => rfl
        right_inv := fun c => rfl }
  have hCle : C ≤ E := inf_le_left
  have hCdvd : Nat.card C ∣ 64 := hE ▸ Subgroup.card_dvd_of_le hCle
  have hCpow : Nat.card C ∣ 2 ^ 6 := by simpa using hCdvd
  obtain ⟨j, hj, hjC⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hCpow
  rw [← Nat.card_eq_fintype_card, hE] at hmodeq
  rw [hCcard, hjC] at hmodeq
  rcases Nat.lt_or_ge j 6 with hj6 | hj6
  · exact hmod j hj6 hmodeq.symm
  · have hj6' : j = 6 := le_antisymm hj hj6
    have hCE' : Nat.card C = Nat.card E := by rw [hjC, hj6', hE]; norm_num
    have hCeq : C = E := Subgroup.eq_of_le_of_card_ge hCle hCE'.ge
    have hcomm : ∀ x ∈ E, (g : G) * x = x * (g : G) := fun x hx =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hCeq ▸ hx : x ∈ C).2).symm
    have hgE : (g : G) ∈ E := hCE _ hgN hcomm
    have hdvd2 : p ∣ 64 := by
      rw [← hE, ← hg']
      exact Subgroup.orderOf_dvd_natCard E hgE
    have hp2' : p ∣ 2 ^ 6 := by simpa using hdvd2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hp2'))

end CFSG.EvenSporadicStandard.M22Std
