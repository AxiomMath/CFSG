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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.QuasithinUnique.A5.Dec2

open scoped Pointwise

theorem exists_second_fixed_point {X : Type*} [Fintype X] [DecidableEq X] (σ : Equiv.Perm X)
    (hσ : σ ^ 5 = 1) (a : X) (ha : σ a = a) (h : ¬ Fintype.card X ≡ 1 [MOD 5]) :
    ∃ b : X, b ≠ a ∧ σ b = b := by
  have hp : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_contra hno
  have hno' : ∀ b : X, b ≠ a → σ b ≠ b := fun b hb hb' => hno ⟨b, hb, hb'⟩
  have hcard := Equiv.Perm.card_compl_support_modEq (p := 5) (n := 1) (σ := σ) (by simpa using hσ)
  have hsupp : σ.supportᶜ = {a} := by
    ext b
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Finset.mem_singleton]
    constructor
    · intro hb
      by_contra hba
      exact hno' b hba hb
    · rintro rfl
      exact ha
  rw [hsupp, Finset.card_singleton] at hcard
  exact h hcard.symm

theorem exists_comm_of_invariant {N : Type*} [Group N] [Finite N] (S : Subgroup N) (x : N)
    (hx5 : x ^ 5 = 1) (hS : ∀ s ∈ S, x * s * x⁻¹ ∈ S) (h : ¬ Nat.card S ≡ 1 [MOD 5]) :
    ∃ s ∈ S, s ≠ 1 ∧ x * s = s * x := by
  classical
  have hpow : ∀ k : ℕ, ∀ s ∈ S, x ^ k * s * (x ^ k)⁻¹ ∈ S := by
    intro k
    induction k with
    | zero => intro s hs; simpa using hs
    | succ k ih =>
      intro s hs
      have h1 := hS _ (ih s hs)
      have e : x ^ (k + 1) * s * (x ^ (k + 1))⁻¹ = x * (x ^ k * s * (x ^ k)⁻¹) * x⁻¹ := by
        rw [pow_succ']
        group
      rw [e]
      exact h1
  have hinv : ∀ s ∈ S, x⁻¹ * s * x ∈ S := by
    intro s hs
    have h4 := hpow 4 s hs
    have e4 : x ^ 4 = x⁻¹ := by
      have : x ^ 4 * x = 1 := by rw [← pow_succ]; exact hx5
      exact eq_inv_of_mul_eq_one_left this
    rw [e4] at h4
    simpa using h4
  let σ : Equiv.Perm S :=
    { toFun := fun s => ⟨x * s * x⁻¹, hS s s.2⟩
      invFun := fun s => ⟨x⁻¹ * s * x, hinv s s.2⟩
      left_inv := fun s => by ext; simp [mul_assoc]
      right_inv := fun s => by ext; simp [mul_assoc] }
  have hσk : ∀ k : ℕ, ∀ s : S, ((σ ^ k) s : N) = x ^ k * s * (x ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro s; simp
    | succ k ih =>
      intro s
      rw [pow_succ', Equiv.Perm.mul_apply]
      have e1 : (σ ((σ ^ k) s) : N) = x * ((σ ^ k) s : N) * x⁻¹ := rfl
      rw [e1, ih, pow_succ']
      group
  have hσ : σ ^ 5 = 1 := by
    ext s
    rw [hσk 5, hx5]
    simp
  have : Fintype S := Fintype.ofFinite S
  have hfix := exists_second_fixed_point σ hσ ⟨1, S.one_mem⟩ (by ext; simp [σ])
    (by rwa [← Nat.card_eq_fintype_card])
  obtain ⟨b, hb1, hb⟩ := hfix
  refine ⟨b, b.2, fun h1 => hb1 (Subtype.ext h1), ?_⟩
  have hb' : x * (b : N) * x⁻¹ = b := congrArg Subtype.val hb
  calc x * (b : N) = x * b * x⁻¹ * x := by group
    _ = b * x := by rw [hb']

theorem exists_invariant_sylow {N : Type*} [Group N] [Finite N] (C : Subgroup N) [C.Normal]
    (x : N) (hx5 : x ^ 5 = 1) (h5 : ¬ 5 ∣ Nat.card C) (r : ℕ) [Fact r.Prime] :
    ∃ S : Subgroup N, S ≤ C ∧ Nat.card S = r ^ (Nat.card C).factorization r ∧
      ∀ s ∈ S, x * s * x⁻¹ ∈ S := by
  classical
  have hp5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let _ : MulDistribMulAction N C :=
    MulDistribMulAction.compHom C (MulAut.conjNormal : N →* MulAut C)
  have : Fintype (Sylow r C) := Fintype.ofFinite _
  let σ : Equiv.Perm (Sylow r C) := MulAction.toPerm x
  have hσ : σ ^ 5 ^ 1 = 1 := by
    have : σ ^ 5 = MulAction.toPermHom N (Sylow r C) (x ^ 5) := by
      rw [map_pow]
      rfl
    rw [pow_one, this, hx5, map_one]
  have hcard : ¬ 5 ∣ Fintype.card (Sylow r C) := by
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow r C))
    rw [← Nat.card_eq_fintype_card, Sylow.card_eq_index_normalizer P]
    intro hd
    exact h5 (hd.trans (Subgroup.index_dvd_card _))
  obtain ⟨P, hP⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσ
  have hP' : x • P = P := hP
  refine ⟨(P : Subgroup C).map C.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨p, -, rfl⟩
    exact p.2
  · rw [Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity P]
  · rintro _ ⟨p, hp, rfl⟩
    have h2 : ((x • P : Sylow r C) : Subgroup C) = x • (P : Subgroup C) := rfl
    have h1 : x • p ∈ ((x • P : Sylow r C) : Subgroup C) := by
      rw [h2]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hp
    rw [hP'] at h1
    exact ⟨x • p, h1, rfl⟩

theorem exists_order_prime_comm {N : Type*} [Group N] [Finite N] (C : Subgroup N) [C.Normal]
    (x : N) (hx5 : x ^ 5 = 1) (h5 : ¬ 5 ∣ Nat.card C) (r : ℕ) [Fact r.Prime]
    (hmod : ¬ r ^ (Nat.card C).factorization r ≡ 1 [MOD 5]) :
    ∃ s ∈ C, orderOf s = r ∧ x * s = s * x := by
  obtain ⟨S, hSC, hSc, hSx⟩ := exists_invariant_sylow C x hx5 h5 r
  have hmod' : ¬ Nat.card S ≡ 1 [MOD 5] := by rwa [hSc]
  obtain ⟨s, hsS, hs1, hsx⟩ := exists_comm_of_invariant S x hx5 hSx hmod'
  have hSp : IsPGroup r S := IsPGroup.of_card hSc
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hSp ⟨s, hsS⟩
  have hks : orderOf s = r ^ k := by
    rw [← hk]
    exact (Subgroup.orderOf_mk s hsS).symm
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hks
    exact hs1 (orderOf_eq_one_iff.1 hks)
  have hr : r ∣ orderOf s := by
    rw [hks]
    exact dvd_pow_self r hk0
  have hne : orderOf s ≠ 0 := by
    rw [hks]
    exact pow_ne_zero _ (Fact.out : r.Prime).ne_zero
  refine ⟨s ^ (orderOf s / r), C.pow_mem (hSC hsS) _, orderOf_pow_orderOf_div hne hr, ?_⟩
  exact (Commute.pow_right (show Commute x s from hsx) _).eq

theorem exists_normalizer_mul_of_sylow {N : Type*} [Group N] [Finite N] (C : Subgroup N)
    [C.Normal] (r : ℕ) [Fact r.Prime] (S : Subgroup N) (hSC : S ≤ C)
    (hS : Nat.card S = r ^ (Nat.card C).factorization r) (m : N) :
    ∃ t ∈ Subgroup.normalizer (S : Set N), ∃ c ∈ C, t * c = m := by
  let P : Sylow r C := Sylow.ofCard (S.subgroupOf C) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv]
    exact hS)
  have hP : (P : Subgroup C).map C.subtype = S := Subgroup.map_subgroupOf_eq_of_le hSC
  have h := Sylow.normalizer_sup_eq_top P
  rw [hP] at h
  have hm : m ∈ Subgroup.normalizer (S : Set N) ⊔ C := by
    rw [h]
    trivial
  obtain ⟨t, ht, c, hc, htc⟩ := Subgroup.mem_sup_of_normal_right.1 hm
  exact ⟨t, ht, c, hc, htc⟩

theorem commutator_centralizes_cyclic {N : Type*} [Group N] (S : Subgroup N) [IsCyclic S]
    (t t' : N) (ht : t ∈ Subgroup.normalizer (S : Set N))
    (ht' : t' ∈ Subgroup.normalizer (S : Set N)) (s : N) (hs : s ∈ S) :
    (t * t' * t⁻¹ * t'⁻¹) * s * (t * t' * t⁻¹ * t'⁻¹)⁻¹ = s := by
  have hcomm : ∀ σ τ : MulAut S, σ * τ = τ * σ := by
    intro σ τ
    apply (IsCyclic.mulAutMulEquiv S).injective
    rw [map_mul, map_mul, mul_comm]
  let ψ := S.normalizerMonoidHom
  let a : (Subgroup.normalizer (S : Set N)) := ⟨t, ht⟩
  let b : (Subgroup.normalizer (S : Set N)) := ⟨t', ht'⟩
  have h1 : ψ (a * b * a⁻¹ * b⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    calc ψ a * ψ b * (ψ a)⁻¹ * (ψ b)⁻¹ = (ψ a * ψ b) * (ψ b * ψ a)⁻¹ := by
          simp [mul_assoc]
      _ = 1 := by rw [hcomm (ψ b) (ψ a)]; simp
  have h2 : ((ψ (a * b * a⁻¹ * b⁻¹) ⟨s, hs⟩ : S) : N) = s := by
    rw [h1]
    rfl
  have h3 : ((ψ (a * b * a⁻¹ * b⁻¹) ⟨s, hs⟩ : S) : N) =
      (t * t' * t⁻¹ * t'⁻¹) * s * (t * t' * t⁻¹ * t'⁻¹)⁻¹ := rfl
  rw [← h3]
  exact h2

theorem exists_order_five_centralizing {N : Type*} [Group N] [Finite N] (C : Subgroup N)
    [C.Normal] (x n : N) (hx5 : orderOf x = 5) (hxC : x ∉ C) (j : ℕ) (hj : ¬ j ≡ 1 [MOD 5])
    (hn : n * x * n⁻¹ = x ^ j) (r : ℕ) [Fact r.Prime] (S : Subgroup N) (hSC : S ≤ C)
    (hS : Nat.card S = r ^ (Nat.card C).factorization r) (hSr : Nat.card S = r) :
    ∃ x1 : N, orderOf x1 = 5 ∧ ∀ s ∈ S, x1 * s = s * x1 := by
  have hp5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcyc : IsCyclic S := isCyclic_of_prime_card hSr
  have hx5' : x ^ 5 = 1 := by rw [← hx5]; exact pow_orderOf_eq_one x
  obtain ⟨t₁, ht₁, c₁, hc₁, h₁⟩ := exists_normalizer_mul_of_sylow C r S hSC hS x
  obtain ⟨t₂, ht₂, c₂, hc₂, h₂⟩ := exists_normalizer_mul_of_sylow C r S hSC hS n
  have heK : t₂ * t₁ * t₂⁻¹ * t₁⁻¹ ∈ Subgroup.centralizer (S : Set N) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h := commutator_centralizes_cyclic S t₂ t₁ ht₂ ht₁ s hs
    calc s * (t₂ * t₁ * t₂⁻¹ * t₁⁻¹) = ((t₂ * t₁ * t₂⁻¹ * t₁⁻¹) * s *
          (t₂ * t₁ * t₂⁻¹ * t₁⁻¹)⁻¹) * (t₂ * t₁ * t₂⁻¹ * t₁⁻¹) := by rw [h]
      _ = (t₂ * t₁ * t₂⁻¹ * t₁⁻¹) * s := by group
  let π := QuotientGroup.mk' C
  have hπc₁ : π c₁ = 1 := (QuotientGroup.eq_one_iff c₁).2 hc₁
  have hπc₂ : π c₂ = 1 := (QuotientGroup.eq_one_iff c₂).2 hc₂
  have hπx : π x = π t₁ := by
    rw [← h₁, map_mul, hπc₁, mul_one]
  have hπn : π n = π t₂ := by
    rw [← h₂, map_mul, hπc₂, mul_one]
  have hue : (n * x * n⁻¹ * x⁻¹) * (t₂ * t₁ * t₂⁻¹ * t₁⁻¹)⁻¹ ∈ C := by
    rw [← QuotientGroup.eq_one_iff]
    have : π ((n * x * n⁻¹ * x⁻¹) * (t₂ * t₁ * t₂⁻¹ * t₁⁻¹)⁻¹) = 1 := by
      simp only [map_mul, map_inv, hπx, hπn]
      group
    simpa [π] using this
  have huQ : n * x * n⁻¹ * x⁻¹ ∈ C ⊔ Subgroup.centralizer (S : Set N) := by
    have : n * x * n⁻¹ * x⁻¹ = ((n * x * n⁻¹ * x⁻¹) * (t₂ * t₁ * t₂⁻¹ * t₁⁻¹)⁻¹) *
        (t₂ * t₁ * t₂⁻¹ * t₁⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hue heK
  have hj0 : j % 5 ≠ 0 := by
    intro h0
    have hxj : x ^ j = 1 := by
      have := pow_mod_orderOf x j
      rw [hx5, h0, pow_zero] at this
      exact this.symm
    rw [hxj] at hn
    have : x = 1 := by
      have h1 : n * x * n⁻¹ = 1 := hn
      simpa using h1
    rw [this] at hx5
    simp at hx5
  have hj1 : j % 5 ≠ 1 := fun h1 => hj (by simpa [Nat.ModEq] using h1)
  have hxj : x ^ j = x ^ (j % 5) := by
    have := pow_mod_orderOf x j
    rw [hx5] at this
    exact this.symm
  have hxQ : x ∈ C ⊔ Subgroup.centralizer (S : Set N) := by
    rw [hn, hxj] at huQ
    have hcases : j % 5 = 2 ∨ j % 5 = 3 ∨ j % 5 = 4 := by omega
    rcases hcases with h | h | h
    · rw [h] at huQ
      have e : x ^ 2 * x⁻¹ = x := by group
      rwa [e] at huQ
    · rw [h] at huQ
      have e : x = (x ^ 3 * x⁻¹) ^ 3 := by
        have : (x ^ 3 * x⁻¹) = x ^ 2 := by group
        rw [this, ← pow_mul]
        calc x = x ^ 5 * x := by rw [hx5']; simp
          _ = x ^ (2 * 3) := by rw [← pow_succ]
      rw [e]
      exact Subgroup.pow_mem _ huQ 3
    · rw [h] at huQ
      have e : x = (x ^ 4 * x⁻¹) ^ 2 := by
        have : (x ^ 4 * x⁻¹) = x ^ 3 := by group
        rw [this, ← pow_mul]
        calc x = x ^ 5 * x := by rw [hx5']; simp
          _ = x ^ (3 * 2) := by rw [← pow_succ]
      rw [e]
      exact Subgroup.pow_mem _ huQ 2
  obtain ⟨c, hc, k, hk, hck⟩ := Subgroup.mem_sup_of_normal_left.1 hxQ
  have hπk : π k = π x := by
    have hπc : π c = 1 := (QuotientGroup.eq_one_iff c).2 hc
    have : k = c⁻¹ * x := by rw [← hck]; group
    rw [this, map_mul, map_inv, hπc]
    simp
  have hπx1 : π x ≠ 1 := fun h => hxC ((QuotientGroup.eq_one_iff x).1 h)
  have hπo : orderOf (π x) = 5 := by
    refine orderOf_eq_prime ?_ hπx1
    rw [← map_pow, hx5', map_one]
  have h5k : 5 ∣ orderOf k := by
    have := orderOf_map_dvd π k
    rwa [hπk, hπo] at this
  have hkpos : orderOf k ≠ 0 := (orderOf_pos k).ne'
  refine ⟨k ^ (orderOf k / 5), orderOf_pow_orderOf_div hkpos h5k, fun s hs => ?_⟩
  have hkK : k ^ (orderOf k / 5) ∈ Subgroup.centralizer (S : Set N) :=
    Subgroup.pow_mem _ hk _
  exact (Subgroup.mem_centralizer_iff.1 hkK s hs).symm

section Centralizer

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem card_subgroupOf_centralizer (V : Set G) :
    Nat.card ((Subgroup.centralizer V).subgroupOf (Subgroup.normalizer V)) =
      Nat.card (Subgroup.centralizer V) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer V)).toEquiv

theorem exists_order_prime_comm_centralizer (V : Set G) (x : G)
    (hx : x ∈ Subgroup.normalizer V) (hx5 : x ^ 5 = 1)
    (h5 : ¬ 5 ∣ Nat.card (Subgroup.centralizer V)) (r : ℕ) [Fact r.Prime]
    (hmod : ¬ r ^ (Nat.card (Subgroup.centralizer V)).factorization r ≡ 1 [MOD 5]) :
    ∃ s ∈ Subgroup.centralizer V, orderOf s = r ∧ x * s = s * x := by
  have hc := card_subgroupOf_centralizer V
  obtain ⟨s, hs, hso, hsx⟩ := exists_order_prime_comm
    ((Subgroup.centralizer V).subgroupOf (Subgroup.normalizer V))
    (⟨x, hx⟩ : Subgroup.normalizer V) (by ext; simpa using hx5) (by rwa [hc]) r
    (by rwa [hc])
  refine ⟨s, hs, ?_, ?_⟩
  · rw [← hso]
    exact Subgroup.orderOf_coe s
  · have := congrArg Subtype.val hsx
    exact this

theorem exists_order_five_centralizing_centralizer (V : Set G) (x n : G)
    (hx : x ∈ Subgroup.normalizer V) (hn' : n ∈ Subgroup.normalizer V) (hx5 : orderOf x = 5)
    (hxC : x ∉ Subgroup.centralizer V) (j : ℕ) (hj : ¬ j ≡ 1 [MOD 5])
    (hn : n * x * n⁻¹ = x ^ j) (r : ℕ) [Fact r.Prime] (s : G)
    (hs : s ∈ Subgroup.centralizer V) (hsr : orderOf s = r)
    (hr2 : ¬ r ^ 2 ∣ Nat.card (Subgroup.centralizer V)) :
    ∃ x1 : G, orderOf x1 = 5 ∧ x1 * s = s * x1 := by
  have hc := card_subgroupOf_centralizer V
  let C : Subgroup (Subgroup.normalizer V) :=
    (Subgroup.centralizer V).subgroupOf (Subgroup.normalizer V)
  let s' : Subgroup.normalizer V := ⟨s, Subgroup.centralizer_le_normalizer V hs⟩
  have hs'C : s' ∈ C := hs
  have hs'o : orderOf s' = r := by
    rw [← Subgroup.orderOf_coe]
    exact hsr
  let S : Subgroup (Subgroup.normalizer V) := Subgroup.zpowers s'
  have hSC : S ≤ C := by
    rw [Subgroup.zpowers_le]
    exact hs'C
  have hSr : Nat.card S = r := by
    rw [Nat.card_zpowers, hs'o]
  have hrC : r ∣ Nat.card C := by
    rw [hc, ← hsr]
    exact Subgroup.orderOf_dvd_natCard _ hs
  have hfac : (Nat.card C).factorization r = 1 := by
    have hpos : Nat.card C ≠ 0 := Nat.card_pos.ne'
    have h1 : r ^ 1 ∣ Nat.card C := by simpa using hrC
    have h2 : ¬ r ^ 2 ∣ Nat.card C := by rwa [hc]
    have hge := ((Fact.out : r.Prime).pow_dvd_iff_le_factorization hpos).1 h1
    have hlt : ¬ 2 ≤ (Nat.card C).factorization r := fun h =>
      h2 (((Fact.out : r.Prime).pow_dvd_iff_le_factorization hpos).2 h)
    omega
  have hx5' : orderOf (⟨x, hx⟩ : Subgroup.normalizer V) = 5 := by
    rw [← Subgroup.orderOf_coe]
    exact hx5
  obtain ⟨x1, hx1o, hx1⟩ := exists_order_five_centralizing C (⟨x, hx⟩ : Subgroup.normalizer V)
    (⟨n, hn'⟩ : Subgroup.normalizer V) hx5' (fun h => hxC h) j hj (by ext; simpa using hn) r S hSC
    (by rw [hfac, pow_one]; exact hSr) hSr
  refine ⟨(x1 : G), ?_, ?_⟩
  · rw [← hx1o]
    exact Subgroup.orderOf_coe x1
  · have := congrArg Subtype.val (hx1 s' (Subgroup.mem_zpowers s'))
    exact this

end Centralizer

theorem mem_normalizer_of_forward {G : Type*} [Group G] [Finite G] (V : Subgroup G) (x : G)
    (h : ∀ v ∈ V, x * v * x⁻¹ ∈ V) : x ∈ Subgroup.normalizer (V : Set G) := by
  have hpow : ∀ k : ℕ, ∀ v ∈ V, x ^ k * v * (x ^ k)⁻¹ ∈ V := by
    intro k
    induction k with
    | zero => intro v hv; simpa using hv
    | succ k ih =>
      intro v hv
      have h1 := h _ (ih v hv)
      have e : x ^ (k + 1) * v * (x ^ (k + 1))⁻¹ = x * (x ^ k * v * (x ^ k)⁻¹) * x⁻¹ := by
        rw [pow_succ']
        group
      rw [e]
      exact h1
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨h v, fun hv => ?_⟩
  have hN : 0 < orderOf x := orderOf_pos x
  have h1 := hpow (orderOf x - 1) _ hv
  have e : x ^ (orderOf x - 1) * (x * v * x⁻¹) * (x ^ (orderOf x - 1))⁻¹ = v := by
    have hx : x ^ (orderOf x - 1) * x = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hN, pow_orderOf_eq_one]
    have hx' : x ^ (orderOf x - 1) = x⁻¹ := eq_inv_of_mul_eq_one_left hx
    rw [hx']
    group
  rwa [e] at h1

section Conj

variable {G : Type*} [Group G] [Finite G]

theorem le_relIndex_centralizer_of_conj (K : Subgroup G) (y : G) {n : ℕ} (q : Fin n → G)
    (hq : ∀ i, q i ∈ K) (hinj : Function.Injective fun i => q i * y * (q i)⁻¹) :
    n ≤ (Subgroup.centralizer ({y} : Set G)).relIndex K := by
  let H := (Subgroup.centralizer ({y} : Set G)).subgroupOf K
  let f : Fin n → K ⧸ H := fun i => QuotientGroup.mk ⟨q i, hq i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply hinj
    have h1 : (⟨q i, hq i⟩ : K)⁻¹ * ⟨q j, hq j⟩ ∈ H := QuotientGroup.eq.1 hij
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 := Subgroup.mem_centralizer_iff.1 h1 y rfl
    have h3 : q i * y * (q i)⁻¹ * q j = q j * y := by
      have h4 : y * ((q i)⁻¹ * q j) = (q i)⁻¹ * q j * y := h2
      calc q i * y * (q i)⁻¹ * q j = q i * (y * ((q i)⁻¹ * q j)) := by group
        _ = q i * ((q i)⁻¹ * q j * y) := by rw [h4]
        _ = q j * y := by group
    show q i * y * (q i)⁻¹ = q j * y * (q j)⁻¹
    calc q i * y * (q i)⁻¹ = (q i * y * (q i)⁻¹ * q j) * (q j)⁻¹ := by group
      _ = q j * y * (q j)⁻¹ := by rw [h3]
  have h := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin] at h
  exact h

theorem le_relIndex_inf_centralizer_of_conj (K : Subgroup G) (y : G) {n : ℕ} (q : Fin n → G)
    (hq : ∀ i, q i ∈ K) (hinj : Function.Injective fun i => q i * y * (q i)⁻¹) :
    n ≤ (K ⊓ Subgroup.centralizer ({y} : Set G)).relIndex K := by
  have h := le_relIndex_centralizer_of_conj K y q hq hinj
  rwa [Subgroup.inf_relIndex_left]

end Conj

end CFSG.QuasithinUnique.A5.Dec2
