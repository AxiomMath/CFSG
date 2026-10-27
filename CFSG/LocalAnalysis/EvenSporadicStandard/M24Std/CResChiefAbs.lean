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
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup
open scoped commutatorElement

@[expose] def OddSolv : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Odd (Nat.card G) → Group.IsSolvable G

variable {U : Type} [Group U]

@[expose] def chiefW (B N : Subgroup U) [B.Normal] : Subgroup (U ⧸ B) :=
  N.map (QuotientGroup.mk' B)

instance chiefW_normal (B N : Subgroup U) [B.Normal] [N.Normal] : (chiefW B N).Normal :=
  Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective B)

@[expose] noncomputable def chiefAct (B N : Subgroup U) [B.Normal] [N.Normal] :
    U →* MulAut (chiefW B N) :=
  (MulAut.conjNormal (H := chiefW B N)).comp (QuotientGroup.mk' B)

theorem chiefAct_apply (B N : Subgroup U) [B.Normal] [N.Normal] (x : U) (w : chiefW B N) :
    ((chiefAct B N x w : chiefW B N) : U ⧸ B) = QuotientGroup.mk' B x * w *
      (QuotientGroup.mk' B x)⁻¹ := rfl

theorem chiefAct_minimal {B N : Subgroup U} [B.Normal] [N.Normal] (hBN : B ≤ N)
    (hchief : ∀ K : Subgroup U, K.Normal → B ≤ K → K ≤ N → K = B ∨ K = N)
    (K' : Subgroup (chiefW B N)) (hK' : ∀ x : U, ∀ k ∈ K', chiefAct B N x k ∈ K') :
    K' = ⊥ ∨ K' = ⊤ := by
  let K : Subgroup U := (K'.map (chiefW B N).subtype).comap (QuotientGroup.mk' B)
  have hKn : K.Normal := by
    refine ⟨fun k hk x => ?_⟩
    obtain ⟨k', hk', hkk⟩ := mem_map.1 hk
    refine mem_map.2 ⟨chiefAct B N x k', hK' x k' hk', ?_⟩
    have hkk' : (k' : U ⧸ B) = QuotientGroup.mk' B k := hkk
    show ((chiefAct B N x k' : chiefW B N) : U ⧸ B) = _
    rw [chiefAct_apply, hkk', map_mul, map_mul, map_inv]
  have hBK : B ≤ K := fun b hb => by
    refine mem_map.2 ⟨1, one_mem _, ?_⟩
    simp [(QuotientGroup.eq_one_iff b).2 hb]
  have hKN : K ≤ N := by
    intro k hk
    obtain ⟨k', _, hkk⟩ := mem_map.1 hk
    obtain ⟨n, hn, hnk⟩ := k'.2
    have h1 : QuotientGroup.mk' B n = QuotientGroup.mk' B k := by
      rw [hnk]
      exact hkk
    have h2 : n⁻¹ * k ∈ B := by
      have := QuotientGroup.eq.1 h1
      exact this
    have : k = n * (n⁻¹ * k) := by group
    rw [this]
    exact mul_mem hn (hBN h2)
  rcases hchief K hKn hBK hKN with hKB | hKN'
  · left
    refine eq_bot_iff.2 fun w hw => ?_
    obtain ⟨n, hn, hnw⟩ := w.2
    have hnK : n ∈ K := mem_map.2 ⟨w, hw, hnw.symm⟩
    rw [hKB] at hnK
    rw [mem_bot]
    apply Subtype.ext
    rw [← hnw]
    exact (QuotientGroup.eq_one_iff n).2 hnK
  · right
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨n, hn, hnw⟩ := w.2
    have hnK : n ∈ K := by rw [hKN']; exact hn
    obtain ⟨k', hk', hkk⟩ := mem_map.1 hnK
    have : k' = w := Subtype.ext (by simpa [hnw] using hkk)
    rw [← this]
    exact hk'

theorem chief_elemAb [Finite U] (hFT : OddSolv) {B N : Subgroup U} [B.Normal] [N.Normal]
    (hBN : B ≤ N) (hne : B ≠ N) (hodd : Odd (Nat.card N))
    (hchief : ∀ K : Subgroup U, K.Normal → B ≤ K → K ≤ N → K = B ∨ K = N) :
    ∃ p r : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card (chiefW B N) = p ^ r ∧
      (∀ w : chiefW B N, w ^ p = 1) ∧ ∀ a b : chiefW B N, a * b = b * a := by
  have hWodd : Odd (Nat.card (chiefW B N)) :=
    Odd.of_dvd_nat hodd (Subgroup.card_map_dvd N (QuotientGroup.mk' B))
  have hsolv : Group.IsSolvable (chiefW B N) := hFT _ hWodd
  have hnt : Nontrivial (chiefW B N) := by
    obtain ⟨n, hnN, hnB⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hBN hne)
    refine ⟨⟨⟨QuotientGroup.mk' B n, n, hnN, rfl⟩, 1, ?_⟩⟩
    intro h
    have h' : QuotientGroup.mk' B n = 1 := congrArg Subtype.val h
    exact hnB ((QuotientGroup.eq_one_iff n).1 h')
  have hmin := chiefAct_minimal hBN hchief
  have hcomm : ∀ a b : chiefW B N, a * b = b * a := by
    have hchar : (commutator (chiefW B N)).Characteristic :=
      show (⁅(⊤ : Subgroup (chiefW B N)), ⊤⁆ : Subgroup (chiefW B N)).Characteristic from
        inferInstance
    have h1 := hmin (commutator (chiefW B N)) (fun x k hk => by
      have h := hchar.fixed (chiefAct B N x)
      have hk' : k ∈ Subgroup.comap (chiefAct B N x).toMonoidHom (commutator (chiefW B N)) := by
        rw [h]; exact hk
      exact hk')
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (chiefW B N)
    have h2 : commutator (chiefW B N) = ⊥ := h1.resolve_right hlt.ne
    intro a b
    have : ⁅a, b⁆ ∈ commutator (chiefW B N) := Subgroup.commutator_mem_commutator (mem_top a)
      (mem_top b)
    rw [h2, mem_bot] at this
    exact (commutatorElement_eq_one_iff_commute.1 this).eq
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show Nat.card (chiefW B N) ≠ 1 from
    (Finite.one_lt_card (α := chiefW B N)).ne')
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hWodd) (even_iff_two_dvd.2 hpd)
  have : Fact p.Prime := ⟨hp⟩
  let Ω : Subgroup (chiefW B N) :=
    { carrier := {w | w ^ p = 1}
      one_mem' := one_pow p
      mul_mem' := fun {a b} ha hb => by
        have hab : Commute a b := hcomm a b
        show (a * b) ^ p = 1
        simp only [Set.mem_ofPred_eq] at ha hb
        rw [hab.mul_pow, ha, hb, one_mul]
      inv_mem' := fun {a} ha => by
        show a⁻¹ ^ p = 1
        simp only [Set.mem_ofPred_eq] at ha
        rw [inv_pow, ha, inv_one] }
  have hinv : ∀ (x : U), ∀ k ∈ Ω, chiefAct B N x k ∈ Ω := by
    intro x k hk
    show (chiefAct B N x k) ^ p = 1
    rw [← map_pow]
    have : k ^ p = 1 := hk
    rw [this, map_one]
  have hΩ : Ω = ⊤ := by
    rcases hmin Ω hinv with h | h
    · exfalso
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpd
      have hgΩ : g ∈ Ω := by
        show g ^ p = 1
        rw [← hg]
        exact pow_orderOf_eq_one g
      rw [h, mem_bot] at hgΩ
      rw [hgΩ, orderOf_one] at hg
      exact hp.one_lt.ne hg
    · exact h
  have hexp : ∀ w : chiefW B N, w ^ p = 1 := fun w => by
    have : w ∈ Ω := by rw [hΩ]; exact mem_top w
    exact this
  have hpg : IsPGroup p (chiefW B N) := fun w => ⟨1, by rw [pow_one]; exact hexp w⟩
  obtain ⟨r, hr⟩ := (IsPGroup.iff_card).1 hpg
  exact ⟨p, r, hp, hp2, hr, hexp, hcomm⟩

end CFSG.EvenSporadicStandard.M24Std
