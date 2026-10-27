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

namespace CFSG.LargeExtraspecial.S63

open Subgroup

@[expose] def D42At (H : Type*) [Group H] (s : H) : Prop :=
  ∀ N : Subgroup H, N ≤ centralizer ({s} : Set H) →
    (∀ c ∈ centralizer ({s} : Set H), ∀ n ∈ N, c * n * c⁻¹ ∈ N) → IsPGroup 2 N → s ∈ N →
      (∀ n ∈ N, (∀ m ∈ N, n * m = m * n) → n = 1 ∨ n = s) → 2 ^ 5 ≤ Nat.card N →
        N ≤ zpowers s ⊔ ⁅N, centralizer ({s} : Set H)⁆ ∧ centralizer (N : Set H) ≤ N

theorem map_centralizer_singleton {H H' : Type*} [Group H] [Group H'] (e : H ≃* H') (s : H) :
    (centralizer ({s} : Set H)).map e.toMonoidHom = centralizer ({e s} : Set H') := by
  ext x
  simp only [mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hy]
  · intro hx
    refine ⟨e.symm x, e.injective ?_, e.apply_symm_apply x⟩
    rw [map_mul, map_mul, e.apply_symm_apply, hx]

theorem D42At.of_mulEquiv {H H' : Type*} [Group H] [Group H'] (e : H ≃* H') {s : H}
    (h : D42At H' (e s)) : D42At H s := by
  intro N hNC hNn hN2 hsN hZ hcard
  set f : H →* H' := e.toMonoidHom with hfdef
  have hf : Function.Injective f := e.injective
  have hC := map_centralizer_singleton e s
  have hle : N.map f ≤ centralizer ({e s} : Set H') := by
    rw [← hC]
    exact map_mono hNC
  have hnor : ∀ c ∈ centralizer ({e s} : Set H'), ∀ n ∈ N.map f, c * n * c⁻¹ ∈ N.map f := by
    intro c hc n hn
    rw [← hC] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    obtain ⟨n', hn', rfl⟩ := hn
    exact ⟨c' * n' * c'⁻¹, hNn c' hc' n' hn', by simp [f]⟩
  have hcen : ∀ n ∈ N.map f, (∀ m ∈ N.map f, n * m = m * n) → n = 1 ∨ n = e s := by
    rintro _ ⟨n, hn, rfl⟩ hcomm
    have hn' : ∀ m ∈ N, n * m = m * n := by
      intro m hm
      apply e.injective
      have := hcomm (e m) ⟨m, hm, rfl⟩
      simpa [f] using this
    rcases hZ n hn hn' with h0 | h0
    · left; simp [f, h0]
    · right; simp [f, h0]
  have hcd : 2 ^ 5 ≤ Nat.card (N.map f) := by
    rw [card_map_of_injective hf]
    exact hcard
  obtain ⟨h1, h2⟩ := h (N.map f) hle hnor (hN2.map f) ⟨s, hsN, rfl⟩ hcen hcd
  refine ⟨?_, fun c hc => ?_⟩
  · rw [← map_le_map_iff_of_injective hf, Subgroup.map_sup, MonoidHom.map_zpowers, map_commutator,
      hC]
    exact h1
  · have hec : e c ∈ centralizer (N.map f : Set H') := by
      rw [mem_centralizer_iff]
      rintro _ ⟨n, hn, rfl⟩
      change e n * e c = e c * e n
      rw [← map_mul, ← map_mul, (mem_centralizer_iff.1 hc) n hn]
    obtain ⟨n, hn, hnc⟩ := h2 hec
    rw [← e.injective hnc]
    exact hn

theorem D42At.conj {H : Type*} [Group H] {x : H} (h : D42At H x) (g : H) :
    D42At H (g * x * g⁻¹) := by
  refine D42At.of_mulEquiv (MulAut.conj g⁻¹) ?_
  rw [MulAut.conj_apply, inv_inv, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
  exact h

theorem card_le_of_forall_mem {H : Type*} [Group H] (N : Subgroup H) (S : Finset H)
    (h : ∀ m ∈ N, m ∈ S) : Nat.card N ≤ S.card := by
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun m hm => h m hm) (Finset.finite_toSet S)

section Semidirect

variable {H : Type*} [Group H] {z : H} {Q L : Subgroup H}

@[expose] def projL (Q L N : Subgroup H) (hnorm : ∀ l ∈ L, ∀ q ∈ Q, l * q * l⁻¹ ∈ Q) :
    Subgroup H where
  carrier := {l | l ∈ L ∧ ∃ q ∈ Q, q * l ∈ N}
  one_mem' := ⟨L.one_mem, 1, Q.one_mem, by rw [one_mul]; exact N.one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, q, hq, hqa⟩ ⟨hb, r, hr, hrb⟩
    refine ⟨L.mul_mem ha hb, q * (a * r * a⁻¹), Q.mul_mem hq (hnorm a ha r hr), ?_⟩
    rw [show q * (a * r * a⁻¹) * (a * b) = (q * a) * (r * b) by group]
    exact N.mul_mem hqa hrb
  inv_mem' := by
    rintro a ⟨ha, q, hq, hqa⟩
    refine ⟨L.inv_mem ha, a⁻¹ * q⁻¹ * a⁻¹⁻¹, hnorm _ (L.inv_mem ha) _ (Q.inv_mem hq), ?_⟩
    rw [show a⁻¹ * q⁻¹ * a⁻¹⁻¹ * a⁻¹ = (q * a)⁻¹ by group]
    exact N.inv_mem hqa

theorem pow_mul_eq (hnorm : ∀ l ∈ L, ∀ q ∈ Q, l * q * l⁻¹ ∈ Q) {q l : H} (hq : q ∈ Q)
    (hl : l ∈ L) : ∀ j : ℕ, ∃ r ∈ Q, (q * l) ^ j = r * l ^ j := by
  intro j
  induction j with
  | zero => exact ⟨1, Q.one_mem, by simp⟩
  | succ j ih =>
    obtain ⟨r, hr, hrj⟩ := ih
    refine ⟨r * (l ^ j * q * (l ^ j)⁻¹), Q.mul_mem hr (hnorm _ (L.pow_mem hl j) q hq), ?_⟩
    rw [pow_succ, hrj, pow_succ]
    group

theorem le_of_semidirect (hQL : ∀ c ∈ centralizer ({z} : Set H), ∃ q ∈ Q, ∃ l ∈ L, c = q * l)
    (hnorm : ∀ l ∈ L, ∀ q ∈ Q, l * q * l⁻¹ ∈ Q) (hdisj : ∀ x ∈ Q, x ∈ L → x = 1)
    (hcore : ∀ K : Subgroup H, K ≤ L → (∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K) →
      IsPGroup 2 K → K = ⊥)
    (hLC : L ≤ centralizer ({z} : Set H)) {N : Subgroup H}
    (hNC : N ≤ centralizer ({z} : Set H))
    (hNn : ∀ c ∈ centralizer ({z} : Set H), ∀ n ∈ N, c * n * c⁻¹ ∈ N) (hN2 : IsPGroup 2 N) :
    N ≤ Q := by
  have hK : projL Q L N hnorm = ⊥ := by
    refine hcore _ (fun l hl => hl.1) ?_ ?_
    · rintro l hl k ⟨hk, q, hq, hqk⟩
      refine ⟨L.mul_mem (L.mul_mem hl hk) (L.inv_mem hl), l * q * l⁻¹, hnorm l hl q hq, ?_⟩
      rw [show l * q * l⁻¹ * (l * k * l⁻¹) = l * (q * k) * l⁻¹ by group]
      exact hNn l (hLC hl) _ hqk
    · rintro ⟨k, hk, q, hq, hqk⟩
      obtain ⟨m, hm⟩ := hN2 ⟨q * k, hqk⟩
      have hm' : (q * k) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      obtain ⟨r, hr, hrk⟩ := pow_mul_eq hnorm hq hk (2 ^ m)
      rw [hrk] at hm'
      have hkq : k ^ 2 ^ m = r⁻¹ := eq_inv_of_mul_eq_one_right hm'
      have h1 : k ^ 2 ^ m = 1 := hdisj _ (hkq ▸ Q.inv_mem hr) (L.pow_mem hk _)
      exact ⟨m, Subtype.ext (by simpa using h1)⟩
  intro n hn
  obtain ⟨q, hq, l, hl, rfl⟩ := hQL n (hNC hn)
  have hl1 : l ∈ projL Q L N hnorm := ⟨hl, q, hq, hn⟩
  rw [hK, mem_bot] at hl1
  rw [hl1, mul_one]
  exact hq

theorem d42At_of_semidirect (hzQ : z ∈ Q) (hLC : L ≤ centralizer ({z} : Set H))
    (hQL : ∀ c ∈ centralizer ({z} : Set H), ∃ q ∈ Q, ∃ l ∈ L, c = q * l)
    (hnorm : ∀ l ∈ L, ∀ q ∈ Q, l * q * l⁻¹ ∈ Q) (hdisj : ∀ x ∈ Q, x ∈ L → x = 1)
    (hcore : ∀ K : Subgroup H, K ≤ L → (∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K) →
      IsPGroup 2 K → K = ⊥)
    (hirr : ∀ M : Subgroup H, M ≤ Q → (∀ l ∈ L, ∀ m ∈ M, l * m * l⁻¹ ∈ M) → z ∈ M →
      (∃ m ∈ M, m ≠ 1 ∧ m ≠ z) → Q ≤ M)
    (hcomm : Q ≤ zpowers z ⊔ ⁅Q, L⁆)
    (hfaith : ∀ q ∈ Q, ∀ l ∈ L, (∀ x ∈ Q, q * l * x = x * (q * l)) → l = 1) :
    D42At H z := by
  classical
  intro N hNC hNn hN2 hzN _ hcard
  have hNQ : N ≤ Q := le_of_semidirect hQL hnorm hdisj hcore hLC hNC hNn hN2
  have hex : ∃ m ∈ N, m ≠ 1 ∧ m ≠ z := by
    by_contra hne
    push Not at hne
    have := card_le_of_forall_mem N {1, z} fun m hm => by
      by_cases h1 : m = 1
      · simp [h1]
      · simp [hne m hm h1]
    have h2 : ({1, z} : Finset H).card ≤ 2 := Finset.card_le_two
    omega
  have hQN : Q ≤ N := hirr N hNQ (fun l hl n hn => hNn l (hLC hl) n hn) hzN hex
  have hNeq : N = Q := le_antisymm hNQ hQN
  subst hNeq
  refine ⟨hcomm.trans (sup_le_sup_left (commutator_mono le_rfl hLC) _), fun c hc => ?_⟩
  have hcz : c ∈ centralizer ({z} : Set H) := by
    rw [mem_centralizer_singleton_iff]
    exact ((mem_centralizer_iff.1 hc) z hzN).symm
  obtain ⟨q, hq, l, hl, rfl⟩ := hQL c hcz
  have hl1 : l = 1 := hfaith q hq l hl fun x hx => ((mem_centralizer_iff.1 hc) x hx).symm
  rw [hl1, mul_one]
  exact hq

end Semidirect

theorem d42At_of_witness {H : Type*} [Group H] {t : H} (P : Set H) (Z : Finset H)
    (hZ8 : Z.card ≤ 8)
    (hP : ∀ N : Subgroup H, N ≤ centralizer ({t} : Set H) →
      (∀ c ∈ centralizer ({t} : Set H), ∀ n ∈ N, c * n * c⁻¹ ∈ N) → IsPGroup 2 N →
        ∀ n ∈ N, n ∈ P)
    (hZc : ∀ y ∈ Z, ∀ x ∈ P, x * y = y * x)
    (hw : ∀ x ∈ P, x ∉ Z → ∃ c ∈ centralizer ({t} : Set H),
      x⁻¹ * c⁻¹ * x * c ∈ Z ∧ x⁻¹ * c⁻¹ * x * c ≠ 1 ∧ x⁻¹ * c⁻¹ * x * c ≠ t) :
    D42At H t := by
  intro N hNC hNn hN2 _ hZN hcard
  have hNP := hP N hNC hNn hN2
  obtain ⟨x, hxN, hxZ⟩ : ∃ x ∈ N, x ∉ Z := by
    by_contra hne
    push Not at hne
    have := card_le_of_forall_mem N Z hne
    omega
  obtain ⟨c, hc, hwZ, hw1, hwt⟩ := hw x (hNP x hxN) hxZ
  have hcN : c⁻¹ * x * c⁻¹⁻¹ ∈ N := hNn _ (inv_mem hc) x hxN
  have hwN : x⁻¹ * c⁻¹ * x * c ∈ N := by
    rw [show x⁻¹ * c⁻¹ * x * c = x⁻¹ * (c⁻¹ * x * c⁻¹⁻¹) by group]
    exact N.mul_mem (N.inv_mem hxN) hcN
  rcases hZN _ hwN (fun m hm => (hZc _ hwZ m (hNP m hm)).symm) with h | h
  · exact absurd h hw1
  · exact absurd h hwt

end CFSG.LargeExtraspecial.S63
