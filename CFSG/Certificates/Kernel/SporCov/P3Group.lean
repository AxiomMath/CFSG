module

public import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Int.Star
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KD.SporCov

open Subgroup

variable {G : Type*} [Group G]

structure P3Rel (p : ℕ) (g₁ g₂ z : G) : Prop where
  zp : z ^ p = 1
  c₁ : z * g₁ = g₁ * z
  c₂ : z * g₂ = g₂ * z
  rel : g₁ * g₂ = z * (g₂ * g₁)
  p₁ : ∃ e : ℕ, g₁ ^ p = z ^ e
  p₂ : ∃ e : ℕ, g₂ ^ p = z ^ e

@[expose] def nf (g₁ g₂ z : G) (a b c : ℤ) : G := g₁ ^ a * g₂ ^ b * z ^ c

theorem comm_of_mem_closure {s : Set G} (hs : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    ∀ x ∈ closure s, ∀ y ∈ closure s, x * y = y * x := by
  have h1 : closure s ≤ centralizer s := by
    rw [closure_le]
    intro a ha
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro b hb
    exact hs b hb a ha
  intro x hx y hy
  have h2 : closure s ≤ centralizer {x} := by
    rw [closure_le]
    intro a ha
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.1 (h1 hx) a ha
  exact (mem_centralizer_singleton_iff.1 (h2 hy)).symm

theorem exists_inv_mod {p : ℕ} (hp : p.Prime) {b : ℤ} (hb : ¬ (p : ℤ) ∣ b) :
    ∃ u : ℕ, (p : ℤ) ∣ b * u - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hb' : (b : ZMod p) ≠ 0 := fun e => hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).1 e)
  refine ⟨((b : ZMod p)⁻¹).val, ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  simp [hb']

theorem eq_closure_pair [Finite G] {p : ℕ} (hp : p.Prime) {z v : G} (hzp : z ^ p = 1)
    (hz : z ≠ 1) {E : Subgroup G} (hcard : Nat.card E = p ^ 2) (hzE : z ∈ E) (hvE : v ∈ E)
    (hv : v ∉ zpowers z) : closure ({z, v} : Set G) = E := by
  have : Fact p.Prime := ⟨hp⟩
  set C := closure ({z, v} : Set G)
  have hCE : C ≤ E := by
    rw [closure_le]
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hzE
    · exact hvE
  have hzC : zpowers z ≤ C := (zpowers_le).2 (subset_closure (by simp))
  have hvC : v ∈ C := subset_closure (by simp)
  have hd : Nat.card C ∣ p ^ 2 := by
    rw [← hcard]
    exact card_dvd_of_le hCE
  obtain ⟨j, hj, hjC⟩ := (Nat.dvd_prime_pow hp).1 hd
  have hzc : Nat.card (zpowers z) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hzp hz]
  have hd1 : p ∣ p ^ j := by
    rw [← hjC, ← hzc]
    exact card_dvd_of_le hzC
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · rw [pow_zero] at hd1
      exact absurd (Nat.le_of_dvd one_pos hd1) (by have := hp.one_lt; omega)
    · exact h
  rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
  · have he : zpowers z = C := eq_of_le_of_card_ge hzC (le_of_eq (by rw [hjC, hzc, pow_one]))
    exact absurd (he ▸ hvC) hv
  · exact eq_of_le_of_card_ge hCE (le_of_eq (by rw [hjC, hcard]))

namespace P3Rel

variable {p : ℕ} {g₁ g₂ z : G} (hR : P3Rel p g₁ g₂ z)
include hR

theorem cz₁ : Commute z g₁ := hR.c₁

theorem cz₂ : Commute z g₂ := hR.c₂

theorem zc₁ (m n : ℤ) : z ^ m * g₁ ^ n = g₁ ^ n * z ^ m :=
  (Commute.zpow_zpow hR.cz₁ m n).eq

theorem zc₂ (m n : ℤ) : z ^ m * g₂ ^ n = g₂ ^ n * z ^ m :=
  (Commute.zpow_zpow hR.cz₂ m n).eq

theorem swap (a b : ℤ) : g₂ ^ b * g₁ ^ a = g₁ ^ a * g₂ ^ b * z ^ (-(a * b)) := by
  have hzi : Commute g₁ z⁻¹ := hR.cz₁.inv_left.symm
  have hs : SemiconjBy g₂ g₁ (g₁ * z⁻¹) := by
    change g₂ * g₁ = g₁ * z⁻¹ * g₂
    have e : g₂ * g₁ = z⁻¹ * (g₁ * g₂) := by
      rw [hR.rel]
      group
    rw [e, ← mul_assoc, hzi.eq]
  have h1 : g₂ * g₁ ^ a = g₁ ^ a * z ^ (-a) * g₂ := by
    have := hs.zpow_right a
    rw [hzi.mul_zpow, inv_zpow'] at this
    exact this
  have hs2 : SemiconjBy (g₁ ^ a) (z ^ (-a) * g₂) g₂ := by
    change g₁ ^ a * (z ^ (-a) * g₂) = g₂ * g₁ ^ a
    rw [h1, mul_assoc]
  have h2 := hs2.zpow_right b
  have hc : Commute (z ^ (-a)) g₂ := hR.cz₂.zpow_left (-a)
  rw [hc.mul_zpow, ← zpow_mul] at h2
  have h3 : g₁ ^ a * (z ^ (-a * b) * g₂ ^ b) = g₂ ^ b * g₁ ^ a := h2
  rw [← h3, hR.zc₂ (-a * b) b, neg_mul]
  simp only [mul_assoc]

theorem nf_mul (a b c a' b' c' : ℤ) :
    nf g₁ g₂ z a b c * nf g₁ g₂ z a' b' c' = nf g₁ g₂ z (a + a') (b + b') (c + c' - a' * b) := by
  unfold nf
  calc g₁ ^ a * g₂ ^ b * z ^ c * (g₁ ^ a' * g₂ ^ b' * z ^ c')
      = g₁ ^ a * (g₂ ^ b * (z ^ c * g₁ ^ a')) * (g₂ ^ b' * z ^ c') := by simp only [mul_assoc]
    _ = g₁ ^ a * (g₂ ^ b * g₁ ^ a') * z ^ c * g₂ ^ b' * z ^ c' := by
        rw [hR.zc₁]
        simp only [mul_assoc]
    _ = g₁ ^ a * (g₁ ^ a' * g₂ ^ b * z ^ (-(a' * b))) * z ^ c * g₂ ^ b' * z ^ c' := by
        rw [hR.swap a' b]
    _ = g₁ ^ a * g₁ ^ a' * g₂ ^ b * (z ^ (-(a' * b)) * z ^ c * g₂ ^ b') * z ^ c' := by
        simp only [mul_assoc]
    _ = g₁ ^ a * g₁ ^ a' * g₂ ^ b * (g₂ ^ b' * z ^ (-(a' * b) + c)) * z ^ c' := by
        rw [← zpow_add z (-(a' * b)) c, hR.zc₂]
    _ = g₁ ^ (a + a') * g₂ ^ (b + b') * z ^ (c + c' - a' * b) := by
        rw [zpow_add g₁ a a', zpow_add g₂ b b',
          show c + c' - a' * b = (-(a' * b) + c) + c' by ring, zpow_add z (-(a' * b) + c) c']
        simp only [mul_assoc]

theorem nf_inv (a b c : ℤ) : (nf g₁ g₂ z a b c)⁻¹ = nf g₁ g₂ z (-a) (-b) (-c - a * b) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [hR.nf_mul, show a + -a = 0 by ring, show b + -b = 0 by ring,
    show c + (-c - a * b) - -a * b = 0 by ring]
  simp [nf]

theorem nf_pow (a b c : ℤ) :
    ∀ n : ℕ, ∃ c' : ℤ, nf g₁ g₂ z a b c ^ n = nf g₁ g₂ z (n * a) (n * b) c'
  | 0 => ⟨0, by simp [nf]⟩
  | n + 1 => by
    obtain ⟨c', hc'⟩ := nf_pow a b c n
    refine ⟨c' + c - a * (n * b), ?_⟩
    rw [pow_succ, hc', hR.nf_mul, show ((n + 1 : ℕ) : ℤ) * a = n * a + a by push_cast; ring,
      show ((n + 1 : ℕ) : ℤ) * b = n * b + b by push_cast; ring]

theorem g₁_mem : g₁ ∈ closure ({g₁, g₂} : Set G) := subset_closure (by simp)

theorem g₂_mem : g₂ ∈ closure ({g₁, g₂} : Set G) := subset_closure (by simp)

theorem z_mem : z ∈ closure ({g₁, g₂} : Set G) := by
  have e : z = g₁ * g₂ * (g₂ * g₁)⁻¹ := by
    rw [hR.rel]
    group
  rw [e]
  exact mul_mem (mul_mem hR.g₁_mem hR.g₂_mem) (inv_mem (mul_mem hR.g₂_mem hR.g₁_mem))

theorem le_centralizer : closure ({g₁, g₂} : Set G) ≤ centralizer {z} := by
  rw [closure_le]
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  rcases ha with rfl | rfl
  · exact hR.c₁.symm
  · exact hR.c₂.symm

theorem exists_nf {x : G} (hx : x ∈ closure ({g₁, g₂} : Set G)) :
    ∃ a b c : ℤ, x = nf g₁ g₂ z a b c := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨1, 0, 0, by simp [nf]⟩
    · exact ⟨0, 1, 0, by simp [nf]⟩
  | one => exact ⟨0, 0, 0, by simp [nf]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, c, rfl⟩ := hx
    obtain ⟨a', b', c', rfl⟩ := hy
    exact ⟨_, _, _, hR.nf_mul a b c a' b' c'⟩
  | inv x _ hx =>
    obtain ⟨a, b, c, rfl⟩ := hx
    exact ⟨_, _, _, hR.nf_inv a b c⟩

theorem g₁_zpow_mem {m : ℤ} (hm : (p : ℤ) ∣ m) : g₁ ^ m ∈ zpowers z := by
  obtain ⟨k, rfl⟩ := hm
  obtain ⟨e, he⟩ := hR.p₁
  rw [zpow_mul, zpow_natCast, he]
  exact zpow_mem (pow_mem (mem_zpowers z) e) k

theorem g₂_zpow_mem {m : ℤ} (hm : (p : ℤ) ∣ m) : g₂ ^ m ∈ zpowers z := by
  obtain ⟨k, rfl⟩ := hm
  obtain ⟨e, he⟩ := hR.p₂
  rw [zpow_mul, zpow_natCast, he]
  exact zpow_mem (pow_mem (mem_zpowers z) e) k

theorem zpow_pow (k : ℤ) : (z ^ k) ^ p = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hR.zp, one_zpow]

theorem pow_mem {x : G} (hx : x ∈ closure ({g₁, g₂} : Set G)) : x ^ p ∈ zpowers z := by
  obtain ⟨a, b, c, rfl⟩ := hR.exists_nf hx
  obtain ⟨c', hc'⟩ := hR.nf_pow a b c p
  rw [hc']
  unfold nf
  exact mul_mem (mul_mem (hR.g₁_zpow_mem (dvd_mul_right _ _))
    (hR.g₂_zpow_mem (dvd_mul_right _ _))) (zpow_mem_zpowers z c')

theorem isPGroup : IsPGroup p (closure ({g₁, g₂} : Set G)) := by
  intro x
  refine ⟨2, ?_⟩
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hR.pow_mem x.2)
  apply Subtype.ext
  rw [Subgroup.coe_pow, OneMemClass.coe_one, pow_two, pow_mul, ← hk, hR.zpow_pow]

theorem z_eq_one_of_comm (e : g₁ * g₂ = g₂ * g₁) : z = 1 := by
  rw [hR.rel] at e
  exact mul_eq_right.1 e

theorem card_eq [Finite G] (hp : p.Prime) (hz : z ≠ 1) (hval : (Nat.card G).factorization p = 3) :
    Nat.card (closure ({g₁, g₂} : Set G)) = p ^ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  set S := closure ({g₁, g₂} : Set G) with hS
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hR.isPGroup
  have hle : n ≤ 3 := by
    have hd : p ^ n ∣ Nat.card G := hn ▸ Subgroup.card_subgroup_dvd_card S
    rw [← hval]
    exact (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hd
  have hnc : ¬ (∀ x y : S, x * y = y * x) := by
    intro hc
    have e : g₁ * g₂ = g₂ * g₁ := congrArg Subtype.val (hc ⟨g₁, hR.g₁_mem⟩ ⟨g₂, hR.g₂_mem⟩)
    exact hz (hR.z_eq_one_of_comm e)
  interval_cases n
  · exfalso
    apply hnc
    have : Subsingleton S := (Nat.card_eq_one_iff_unique.1 (hn.trans (pow_zero p))).1
    intro x y
    exact Subsingleton.elim _ _
  · exfalso
    apply hnc
    have := isCyclic_of_prime_card (p := p) (by simpa using hn)
    exact fun x y => (IsCyclic.commGroup (α := S)).mul_comm x y
  · exact absurd (IsPGroup.commutative_of_card_eq_prime_sq hn) hnc
  · exact hn

theorem z_mem_of_le [Finite G] (hp : p.Prime) (hz : z ≠ 1)
    (hS : Nat.card (closure ({g₁, g₂} : Set G)) = p ^ 3) {E : Subgroup G}
    (hE : E ≤ closure ({g₁, g₂} : Set G)) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hcard : Nat.card E = p ^ 2) : z ∈ E := by
  by_contra hzE
  set S := closure ({g₁, g₂} : Set G) with hSdef
  set T := closure ((E : Set G) ∪ {z}) with hT
  have hzc := hR.le_centralizer
  have hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    apply comm_of_mem_closure
    rintro a (ha | ha) b (hb | hb)
    · exact hEc a ha b hb
    · rw [Set.mem_singleton_iff] at hb
      subst hb
      exact mem_centralizer_singleton_iff.1 (hzc (hE ha))
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      exact (mem_centralizer_singleton_iff.1 (hzc (hE hb))).symm
    · rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]
  have hET : E ≤ T := fun x hx => subset_closure (Or.inl hx)
  have hzT : z ∈ T := subset_closure (Or.inr rfl)
  have hTS : T ≤ S := by
    rw [closure_le]
    rintro a (ha | ha)
    · exact hE ha
    · rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact hR.z_mem
  have hd1 : Nat.card T ∣ p ^ 3 := by
    rw [← hS]
    exact card_dvd_of_le hTS
  obtain ⟨j, hj, hjT⟩ := (Nat.dvd_prime_pow hp).1 hd1
  have hd2 : p ^ 2 ∣ p ^ j := by
    rw [← hcard, ← hjT]
    exact card_dvd_of_le hET
  have hj2 : 2 ≤ j := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hd2
  rcases (show j = 2 ∨ j = 3 by omega) with rfl | rfl
  · have he : E = T := eq_of_le_of_card_ge hET (le_of_eq (by rw [hjT, hcard]))
    exact hzE (by rw [he]; exact hzT)
  · have he : T = S := eq_of_le_of_card_ge hTS (le_of_eq (by rw [hjT, hS]))
    have e := hTc g₁ (by rw [he]; exact hR.g₁_mem) g₂ (by rw [he]; exact hR.g₂_mem)
    exact hz (hR.z_eq_one_of_comm e)

theorem mem_lines [Finite G] (hp : p.Prime) (hz : z ≠ 1)
    (hS : Nat.card (closure ({g₁, g₂} : Set G)) = p ^ 3) {E : Subgroup G}
    (hE : E ≤ closure ({g₁, g₂} : Set G)) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hcard : Nat.card E = p ^ 2) : z ∈ E ∧ (g₂ ∈ E ∨ ∃ i < p, g₁ * g₂ ^ i ∈ E) := by
  have : Fact p.Prime := ⟨hp⟩
  have hzE := hR.z_mem_of_le hp hz hS hE hEc hcard
  refine ⟨hzE, ?_⟩
  have hzz : zpowers z ≤ E := (zpowers_le).2 hzE
  obtain ⟨x, hxE, hxz⟩ : ∃ x ∈ E, x ∉ zpowers z := by
    by_contra! hno
    have hle : Nat.card E ≤ Nat.card (zpowers z) := card_le_of_le hno
    rw [hcard, Nat.card_zpowers, orderOf_eq_prime hR.zp hz] at hle
    have := hp.one_lt
    nlinarith
  obtain ⟨a, b, c, rfl⟩ := hR.exists_nf (hE hxE)
  unfold nf at hxE hxz
  have hy : g₁ ^ a * g₂ ^ b ∈ E := by
    have := mul_mem hxE (zpow_mem hzE (-c))
    rwa [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one] at this
  by_cases ha : (p : ℤ) ∣ a
  · have ha' : g₁ ^ a ∈ E := hzz (hR.g₁_zpow_mem ha)
    have hb2 : g₂ ^ b ∈ E := (mul_mem_cancel_left ha').1 hy
    by_cases hb : (p : ℤ) ∣ b
    · exact absurd (mul_mem (mul_mem (hR.g₁_zpow_mem ha) (hR.g₂_zpow_mem hb))
        (zpow_mem_zpowers z c)) hxz
    · left
      obtain ⟨u, hu⟩ := exists_inv_mod hp hb
      have hbu : g₂ ^ (b * u) ∈ E := by
        rw [zpow_mul, zpow_natCast]
        exact Subgroup.pow_mem _ hb2 u
      rw [show b * u = 1 + (b * u - 1) by ring, zpow_one_add] at hbu
      exact (mul_mem_cancel_right (hzz (hR.g₂_zpow_mem hu))).1 hbu
  · right
    obtain ⟨u, hu⟩ := exists_inv_mod hp ha
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
    set i : ℕ := ((u * b) % p).toNat with hi
    have hii : (i : ℤ) = (u * b) % p := Int.toNat_of_nonneg (Int.emod_nonneg _ hp0.ne')
    have hip : i < p := by
      have := Int.emod_lt_of_pos (u * b) hp0
      omega
    refine ⟨i, hip, ?_⟩
    have hyu : g₁ ^ (u * a) * g₂ ^ (u * b) ∈ E := by
      obtain ⟨c', hc'⟩ := hR.nf_pow a b 0 u
      have h1 : (g₁ ^ a * g₂ ^ b) ^ u = nf g₁ g₂ z (u * a) (u * b) c' := by
        rw [← hc']
        simp [nf]
      have h2 := Subgroup.pow_mem _ hy u
      rw [h1] at h2
      unfold nf at h2
      have := mul_mem h2 (zpow_mem hzE (-c'))
      rwa [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one] at this
    have hd1 : (p : ℤ) ∣ u * a - 1 := by
      rw [mul_comm]
      exact hu
    have hd2 : (p : ℤ) ∣ u * b - i := by
      rw [hii, Int.emod_def]
      exact ⟨u * b / p, by ring⟩
    obtain ⟨k₁, hk₁⟩ := mem_zpowers_iff.1 (hR.g₁_zpow_mem hd1)
    obtain ⟨k₂, hk₂⟩ := mem_zpowers_iff.1 (hR.g₂_zpow_mem hd2)
    have e : g₁ ^ (u * a) * g₂ ^ (u * b) = g₁ * g₂ ^ i * z ^ (k₁ + k₂) := by
      rw [show (u : ℤ) * a = 1 + (u * a - 1) by ring, zpow_one_add, ← hk₁,
        show (u : ℤ) * b = i + (u * b - i) by ring, zpow_add, ← hk₂, zpow_natCast, zpow_add,
        ← zpow_natCast g₂ i]
      calc g₁ * z ^ k₁ * (g₂ ^ (i : ℤ) * z ^ k₂)
          = g₁ * (z ^ k₁ * g₂ ^ (i : ℤ)) * z ^ k₂ := by simp only [mul_assoc]
        _ = g₁ * g₂ ^ (i : ℤ) * (z ^ k₁ * z ^ k₂) := by
          rw [hR.zc₂]
          simp only [mul_assoc]
    rw [e] at hyu
    exact (mul_mem_cancel_right (zpow_mem hzE _)).1 hyu

theorem g₂_not_mem (hz : z ≠ 1) : g₂ ∉ zpowers z := by
  intro hm
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hm
  apply hz
  apply hR.z_eq_one_of_comm
  rw [← hk]
  exact (hR.cz₁.zpow_left k).symm.eq

theorem line_not_mem (hz : z ≠ 1) (i : ℕ) : g₁ * g₂ ^ i ∉ zpowers z := by
  intro hm
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hm
  apply hz
  apply hR.z_eq_one_of_comm
  have e : g₁ = z ^ k * (g₂ ^ i)⁻¹ := eq_mul_inv_of_mul_eq hk.symm
  have hc : Commute (z ^ k * (g₂ ^ i)⁻¹) g₂ :=
    Commute.mul_left (hR.cz₂.zpow_left k)
      ((Commute.pow_left (Commute.refl g₂) i).inv_left)
  rw [e]
  exact hc.eq

theorem eq_line [Finite G] (hp : p.Prime) (hz : z ≠ 1)
    (hS : Nat.card (closure ({g₁, g₂} : Set G)) = p ^ 3) {E : Subgroup G}
    (hE : E ≤ closure ({g₁, g₂} : Set G)) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hcard : Nat.card E = p ^ 2) :
    E = closure ({z, g₂} : Set G) ∨ ∃ i < p, E = closure ({z, g₁ * g₂ ^ i} : Set G) := by
  obtain ⟨hzE, hl⟩ := hR.mem_lines hp hz hS hE hEc hcard
  rcases hl with h2 | ⟨i, hi, h3⟩
  · exact Or.inl (eq_closure_pair hp hR.zp hz hcard hzE h2 (hR.g₂_not_mem hz)).symm
  · exact Or.inr ⟨i, hi, (eq_closure_pair hp hR.zp hz hcard hzE h3 (hR.line_not_mem hz i)).symm⟩

theorem exists_conj_lines [Finite G] (hp : p.Prime) (hz : z ≠ 1)
    (hval : (Nat.card G).factorization p = 3) {E : Subgroup G} (hEp : IsPGroup p E)
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hcard : Nat.card E = p ^ 2) :
    ∃ g : G, g * z * g⁻¹ ∈ E ∧ (g * g₂ * g⁻¹ ∈ E ∨ ∃ i < p, g * (g₁ * g₂ ^ i) * g⁻¹ ∈ E) := by
  have : Fact p.Prime := ⟨hp⟩
  have hS := hR.card_eq hp hz hval
  let Sy : Sylow p G := Sylow.ofCard (closure ({g₁, g₂} : Set G)) (by rw [hS, hval])
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Sy P
  set f : G →* G := (MulAut.conj g⁻¹).toMonoidHom with hfdef
  have hf : ∀ x, f x = g⁻¹ * x * g := fun x => by simp [hfdef, MulAut.conj_apply]
  have hE'S : E.map f ≤ closure ({g₁, g₂} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxP : x ∈ (P : Subgroup G) := hEP hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxP
    obtain ⟨t, ht, e⟩ := hxP
    have et : g⁻¹ * x * g = t := by
      rw [← e]
      simp [MulAut.conj_apply]
      group
    rw [hf, et]
    exact ht
  have hE'c : ∀ x ∈ E.map f, ∀ y ∈ E.map f, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hEc x hx y hy]
  have hE'card : Nat.card (E.map f) = p ^ 2 := by
    rw [card_map_of_injective (MulAut.conj g⁻¹).injective, hcard]
  have back : ∀ w ∈ E.map f, g * w * g⁻¹ ∈ E := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hf, show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
    exact hx
  obtain ⟨hzE, hl⟩ := hR.mem_lines hp hz hS hE'S hE'c hE'card
  refine ⟨g, back _ hzE, ?_⟩
  rcases hl with h2 | ⟨i, hi, h3⟩
  · exact Or.inl (back _ h2)
  · exact Or.inr ⟨i, hi, back _ h3⟩

end P3Rel

end CFSG.KD.SporCov

end
