module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finite.Basic
import CFSG.FeitThompson.OddOrder.FreeActionKernelCongruence

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise MulAction
open scoped commutatorElement

variable {H : Type*} [Group H] {A N : Subgroup H} {b c : MulAut H} {p n : ℕ} {m l : ℤ}
  {Hc : ℕ → Subgroup H}

theorem apply_mem_of_pointwise_smul_eq (hb : b • A = A) {x : H} (hx : x ∈ A) : b x ∈ A := by
  rw [← hb]; exact Subgroup.smul_mem_pointwise_smul x b A hx

theorem inv_pointwise_smul_eq (hb : b • A = A) : b⁻¹ • A = A := by rw [inv_smul_eq_iff, hb]

theorem mem_of_apply_mem (hb : b • A = A) {x : H} (hx : b x ∈ A) : x ∈ A := by
  have := apply_mem_of_pointwise_smul_eq (inv_pointwise_smul_eq hb) hx
  simpa using this

theorem card_eq_relIndex_mul_card_of_le (hNA : N ≤ A) :
    Nat.card A = N.relIndex A * Nat.card N := by
  have h := Subgroup.index_mul_card (N.subgroupOf A)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNA).toEquiv] at h
  rw [Subgroup.relIndex, h]

theorem card_quotient_subgroupOf_eq_relIndex (A N : Subgroup H) :
    Nat.card (↥A ⧸ N.subgroupOf A) = N.relIndex A := by
  rw [Subgroup.relIndex, Subgroup.index_eq_card]

theorem mk_subgroupOf_eq_mk_iff [(N.subgroupOf A).Normal] {x y : H} (hx : x ∈ A) (hy : y ∈ A) :
    (QuotientGroup.mk (⟨x, hx⟩ : A) : ↥A ⧸ N.subgroupOf A) = QuotientGroup.mk ⟨y, hy⟩
      ↔ x⁻¹ * y ∈ N := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]; simp

theorem mk_subgroupOf_eq_one_iff [(N.subgroupOf A).Normal] {x : H} (hx : x ∈ A) :
    (QuotientGroup.mk (⟨x, hx⟩ : A) : ↥A ⧸ N.subgroupOf A) = 1 ↔ x ∈ N := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem mk_subgroupOf_zpow [(N.subgroupOf A).Normal] {x : H} (hx : x ∈ A) (k : ℤ) :
    (QuotientGroup.mk (⟨x, hx⟩ : A) : ↥A ⧸ N.subgroupOf A) ^ k =
      QuotientGroup.mk ⟨x ^ k, A.zpow_mem hx k⟩ := by
  rw [← QuotientGroup.mk_zpow]; congr 1

theorem pow_relIndex_mem_of_mem [(N.subgroupOf A).Normal] {x : H} (hx : x ∈ A) :
    x ^ N.relIndex A ∈ N := by
  have h := Subgroup.pow_index_mem (N.subgroupOf A) (⟨x, hx⟩ : A)
  rw [Subgroup.mem_subgroupOf] at h
  simpa [Subgroup.relIndex] using h

theorem zpow_mem_of_relIndex_dvd [(N.subgroupOf A).Normal] {x : H} (hx : x ∈ A) {k : ℤ}
    (hk : ((N.relIndex A : ℕ) : ℤ) ∣ k) : x ^ k ∈ N := by
  obtain ⟨t, rfl⟩ := hk
  rw [zpow_mul, zpow_natCast]
  exact N.zpow_mem (pow_relIndex_mem_of_mem hx) t

theorem orderOf_mk_subgroupOf (hp : p.Prime) [(N.subgroupOf A).Normal] (hidx : N.relIndex A = p)
    {x : H} (hx : x ∈ A) (hxN : x ∉ N) :
    orderOf (QuotientGroup.mk (⟨x, hx⟩ : A) : ↥A ⧸ N.subgroupOf A) = p := by
  have hcard : Nat.card (↥A ⧸ N.subgroupOf A) = p := by
    rw [card_quotient_subgroupOf_eq_relIndex, hidx]
  have hne : (QuotientGroup.mk (⟨x, hx⟩ : A) : ↥A ⧸ N.subgroupOf A) ≠ 1 := fun h =>
    hxN ((mk_subgroupOf_eq_one_iff hx).1 h)
  have hdvd := hcard ▸ orderOf_dvd_natCard (QuotientGroup.mk (⟨x, hx⟩ : A) : ↥A ⧸ N.subgroupOf A)
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) hne
  · exact h

theorem exists_zpow_inv_mul_mem (hp : p.Prime) [(N.subgroupOf A).Normal]
    (hidx : N.relIndex A = p) {x : H} (hx : x ∈ A) (hxN : x ∉ N) {y : H} (hy : y ∈ A) :
    ∃ k : ℤ, (x ^ k)⁻¹ * y ∈ N := by
  have hcard : Nat.card (↥A ⧸ N.subgroupOf A) = p := by
    rw [card_quotient_subgroupOf_eq_relIndex, hidx]
  have : Finite (↥A ⧸ N.subgroupOf A) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  have htop : Subgroup.zpowers (QuotientGroup.mk (⟨x, hx⟩ : A) : ↥A ⧸ N.subgroupOf A) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by
      rw [Nat.card_zpowers, orderOf_mk_subgroupOf hp hidx hx hxN, hcard])
  obtain ⟨k, hk⟩ : (QuotientGroup.mk (⟨y, hy⟩ : A) : ↥A ⧸ N.subgroupOf A) ∈
      Subgroup.zpowers (QuotientGroup.mk (⟨x, hx⟩ : A)) := htop ▸ Subgroup.mem_top _
  refine ⟨k, ?_⟩
  rw [← mk_subgroupOf_eq_mk_iff (A.zpow_mem hx k) hy, ← mk_subgroupOf_zpow hx]
  exact hk

theorem prime_dvd_of_zpow_mem (hp : p.Prime) [(N.subgroupOf A).Normal] (hidx : N.relIndex A = p)
    {x : H} (hx : x ∈ A) (hxN : x ∉ N) {k : ℤ} (hk : x ^ k ∈ N) : (p : ℤ) ∣ k := by
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ : A) : ↥A ⧸ N.subgroupOf A) ^ k = 1 := by
    rw [mk_subgroupOf_zpow hx, mk_subgroupOf_eq_one_iff]; exact hk
  have h2 := orderOf_dvd_iff_zpow_eq_one.2 h1
  rwa [orderOf_mk_subgroupOf hp hidx hx hxN] at h2

def ActsAsZPowOn (b : MulAut H) (A N : Subgroup H) (m : ℤ) : Prop :=
  ∀ x ∈ A, (x ^ m)⁻¹ * b x ∈ N

theorem actsAsZPowOn_def : ActsAsZPowOn b A N m ↔ ∀ x ∈ A, (x ^ m)⁻¹ * b x ∈ N := Iff.rfl

theorem actsAsZPowOn_one_iff : ActsAsZPowOn b A N 1 ↔ ∀ x ∈ A, x⁻¹ * b x ∈ N := by
  simp [ActsAsZPowOn]

theorem actsAsZPowOn_zero_iff : ActsAsZPowOn b A N 0 ↔ ∀ x ∈ A, b x ∈ N := by
  simp [ActsAsZPowOn]

namespace ActsAsZPowOn

theorem one (A N : Subgroup H) : ActsAsZPowOn 1 A N 1 := fun x _ => by simp

theorem mul (hbN : b • N = N) (hb : ActsAsZPowOn b A N m) (hc : ActsAsZPowOn c A N l) :
    ActsAsZPowOn (b * c) A N (m * l) := by
  intro x hx
  have h1 : ((x ^ l) ^ m)⁻¹ * b (x ^ l) ∈ N := hb _ (A.zpow_mem hx l)
  have h2 : b ((x ^ l)⁻¹ * c x) ∈ N := apply_mem_of_pointwise_smul_eq hbN (hc x hx)
  have key : (x ^ (m * l))⁻¹ * (b * c) x
      = (((x ^ l) ^ m)⁻¹ * b (x ^ l)) * b ((x ^ l)⁻¹ * c x) := by
    rw [mul_comm m l, zpow_mul, map_mul, map_inv]
    simp only [MulAut.mul_apply]
    group
  rw [key]
  exact N.mul_mem h1 h2

theorem pow (hbN : b • N = N) (hb : ActsAsZPowOn b A N m) (k : ℕ) :
    ActsAsZPowOn (b ^ k) A N (m ^ k) := by
  induction k with
  | zero => simpa using one A N
  | succ k ih => rw [pow_succ', pow_succ']; exact hb.mul hbN ih

theorem mul_inv (hcA : c • A = A) (hb : ActsAsZPowOn b A N m) (hc : ActsAsZPowOn c A N m) :
    ActsAsZPowOn (b * c⁻¹) A N 1 := by
  intro x hx
  set y := c⁻¹ x with hy
  have hyA : y ∈ A := apply_mem_of_pointwise_smul_eq (inv_pointwise_smul_eq hcA) hx
  have hcy : c y = x := by simp [hy]
  have key : (x ^ (1 : ℤ))⁻¹ * (b * c⁻¹) x = ((y ^ m)⁻¹ * c y)⁻¹ * ((y ^ m)⁻¹ * b y) := by
    rw [hcy]
    simp only [MulAut.mul_apply, zpow_one, mul_inv_rev, inv_inv]
    rw [← hy]
    group
  rw [key]
  exact N.mul_mem (N.inv_mem (hc y hyA)) (hb y hyA)

theorem dvd_sub (hp : p.Prime) [(N.subgroupOf A).Normal] (hidx : N.relIndex A = p)
    {x : H} (hx : x ∈ A) (hxN : x ∉ N) (hm : ActsAsZPowOn b A N m) (hl : ActsAsZPowOn b A N l) :
    (p : ℤ) ∣ m - l := by
  have hmem : x ^ (l - m) ∈ N := by
    have key : x ^ (l - m) = ((x ^ m)⁻¹ * b x) * ((x ^ l)⁻¹ * b x)⁻¹ := by
      rw [zpow_sub]; group
    rw [key]
    exact N.mul_mem (hm x hx) (N.inv_mem (hl x hx))
  exact dvd_sub_comm.1 (prime_dvd_of_zpow_mem hp hidx hx hxN hmem)

theorem of_dvd_sub [(N.subgroupOf A).Normal] (hb : ActsAsZPowOn b A N m)
    (h : ((N.relIndex A : ℕ) : ℤ) ∣ m - l) : ActsAsZPowOn b A N l := by
  intro x hx
  have key : (x ^ l)⁻¹ * b x = x ^ (m - l) * ((x ^ m)⁻¹ * b x) := by group
  rw [key]
  exact N.mul_mem (zpow_mem_of_relIndex_dvd hx h) (hb x hx)

theorem not_dvd [(N.subgroupOf A).Normal] (hidx : N.relIndex A = p)
    (hbN : b • N = N) (hnle : ¬ A ≤ N) (hb : ActsAsZPowOn b A N m) : ¬ (p : ℤ) ∣ m := by
  intro hdvd
  obtain ⟨x, hx, hxN⟩ := SetLike.not_le_iff_exists.1 hnle
  have h0 : ActsAsZPowOn b A N 0 :=
    hb.of_dvd_sub (by rw [hidx, sub_zero]; exact hdvd)
  exact hxN (mem_of_apply_mem hbN (actsAsZPowOn_zero_iff.1 h0 x hx))

end ActsAsZPowOn

theorem exists_actsAsZPowOn (hp : p.Prime) [(N.subgroupOf A).Normal] (hidx : N.relIndex A = p)
    (hbA : b • A = A) (hbN : b • N = N) : ∃ m : ℤ, ActsAsZPowOn b A N m := by
  have hcard : Nat.card (↥A ⧸ N.subgroupOf A) = p := by
    rw [card_quotient_subgroupOf_eq_relIndex, hidx]
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (↥A ⧸ N.subgroupOf A) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  have : IsCyclic (↥A ⧸ N.subgroupOf A) := isCyclic_of_prime_card (p := p) hcard
  set f : ↥A →* ↥A := MonoidHom.codRestrict ((b : H →* H).comp A.subtype) A
    fun x => apply_mem_of_pointwise_smul_eq hbA x.2
  have hcomap : N.subgroupOf A ≤ Subgroup.comap f (N.subgroupOf A) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact apply_mem_of_pointwise_smul_eq hbN hx
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (QuotientGroup.map _ _ f hcomap)
  refine ⟨m, fun x hx => ?_⟩
  have h1 := hm (QuotientGroup.mk (⟨x, hx⟩ : A))
  rw [QuotientGroup.map_mk, mk_subgroupOf_zpow hx] at h1
  exact (mk_subgroupOf_eq_mk_iff (A.zpow_mem hx m)
    (apply_mem_of_pointwise_smul_eq hbA hx)).1 h1.symm

structure IsPrimeFactorChain (p : ℕ) (Hc : ℕ → Subgroup H) (n : ℕ) : Prop where
  eq_top : Hc 0 = ⊤
  eq_bot : Hc n = ⊥
  le_succ : ∀ i < n, Hc (i + 1) ≤ Hc i
  normal_succ : ∀ i < n, ((Hc (i + 1)).subgroupOf (Hc i)).Normal
  relIndex_succ : ∀ i < n, (Hc (i + 1)).relIndex (Hc i) = p

namespace IsPrimeFactorChain

theorem not_le_succ (hp : p.Prime) (hc : IsPrimeFactorChain p Hc n) {i : ℕ} (hi : i < n) :
    ¬ Hc i ≤ Hc (i + 1) := by
  intro hle
  rw [← Subgroup.relIndex_eq_one, hc.relIndex_succ i hi] at hle
  exact hp.one_lt.ne' hle

theorem exists_mem_not_mem (hp : p.Prime) (hc : IsPrimeFactorChain p Hc n) {i : ℕ} (hi : i < n) :
    ∃ x ∈ Hc i, x ∉ Hc (i + 1) :=
  SetLike.not_le_iff_exists.1 (hc.not_le_succ hp hi)

theorem card_eq_pow (hc : IsPrimeFactorChain p Hc n) {i : ℕ} (hi : i ≤ n) :
    Nat.card (Hc i) = p ^ (n - i) := by
  have key : ∀ d j, j + d = n → Nat.card (Hc j) = p ^ d := by
    intro d
    induction d with
    | zero =>
      intro j hj
      simp only [Nat.add_zero] at hj
      subst hj
      rw [hc.eq_bot]
      simp
    | succ d ih =>
      intro j hj
      have hjn : j < n := by omega
      rw [card_eq_relIndex_mul_card_of_le (hc.le_succ j hjn), hc.relIndex_succ j hjn,
        ih (j + 1) (by omega), pow_succ']
  exact key (n - i) i (by omega)

theorem card_eq (hc : IsPrimeFactorChain p Hc n) : Nat.card H = p ^ n := by
  have h := hc.card_eq_pow (i := 0) (Nat.zero_le n)
  rw [hc.eq_top] at h
  simpa using h

theorem finite (hp : p.Prime) (hc : IsPrimeFactorChain p Hc n) : Finite H :=
  Nat.finite_of_card_ne_zero (by rw [hc.card_eq]; exact pow_ne_zero _ hp.ne_zero)

theorem isPGroup (hc : IsPrimeFactorChain p Hc n) : IsPGroup p H :=
  IsPGroup.of_card hc.card_eq

theorem closure_range_eq_top (hp : p.Prime) (hc : IsPrimeFactorChain p Hc n) {t : Fin n → H}
    (ht : ∀ i : Fin n, t i ∈ Hc (i : ℕ)) (ht' : ∀ i : Fin n, t i ∉ Hc ((i : ℕ) + 1)) :
    Subgroup.closure (Set.range t) = ⊤ := by
  set S := Subgroup.closure (Set.range t)
  have key : ∀ d j, j + d = n → Hc j ≤ S := by
    intro d
    induction d with
    | zero =>
      intro j hj
      simp only [Nat.add_zero] at hj
      rw [hj, hc.eq_bot]
      exact bot_le
    | succ d ih =>
      intro j hj
      have hjn : j < n := by omega
      have hih : Hc (j + 1) ≤ S := ih (j + 1) (by omega)
      have := hc.normal_succ j hjn
      intro x hx
      obtain ⟨k, hk⟩ := exists_zpow_inv_mul_mem hp (hc.relIndex_succ j hjn)
        (ht ⟨j, hjn⟩) (ht' ⟨j, hjn⟩) hx
      have h1 : t ⟨j, hjn⟩ ^ k ∈ S := S.zpow_mem (Subgroup.subset_closure ⟨⟨j, hjn⟩, rfl⟩) k
      have hxeq : x = t ⟨j, hjn⟩ ^ k * ((t ⟨j, hjn⟩ ^ k)⁻¹ * x) := by group
      rw [hxeq]
      exact S.mul_mem h1 (hih hk)
  exact top_le_iff.1 (hc.eq_top ▸ key n 0 (by omega))

end IsPrimeFactorChain

def chainStabilizer (Hc : ℕ → Subgroup H) (n : ℕ) : Subgroup (MulAut H) where
  carrier := {b | ∀ i ≤ n, b • Hc i = Hc i}
  one_mem' _ _ := by simp
  mul_mem' hb hc i hi := by rw [mul_smul, hc i hi, hb i hi]
  inv_mem' hb i hi := inv_pointwise_smul_eq (hb i hi)

@[simp]
theorem mem_chainStabilizer :
    b ∈ chainStabilizer Hc n ↔ ∀ i ≤ n, b • Hc i = Hc i := Iff.rfl

def chainKernel (Hc : ℕ → Subgroup H) (n : ℕ) : Subgroup (MulAut H) where
  carrier := {b | (∀ i ≤ n, b • Hc i = Hc i) ∧ ∀ i < n, ∀ x ∈ Hc i, x⁻¹ * b x ∈ Hc (i + 1)}
  one_mem' := ⟨fun i _ => by simp, fun i _ x _ => by simp⟩
  mul_mem' := by
    rintro b c ⟨hb1, hb2⟩ ⟨hc1, hc2⟩
    refine ⟨fun i hi => by rw [mul_smul, hc1 i hi, hb1 i hi], fun i hi x hx => ?_⟩
    have hcx : c x ∈ Hc i := apply_mem_of_pointwise_smul_eq (hc1 i (by omega)) hx
    have key : x⁻¹ * (b * c) x = (x⁻¹ * c x) * ((c x)⁻¹ * b (c x)) := by
      simp only [MulAut.mul_apply]; group
    rw [key]
    exact (Hc (i + 1)).mul_mem (hc2 i hi x hx) (hb2 i hi _ hcx)
  inv_mem' := by
    rintro b ⟨hb1, hb2⟩
    refine ⟨fun i hi => inv_pointwise_smul_eq (hb1 i hi), fun i hi x hx => ?_⟩
    have hy : b⁻¹ x ∈ Hc i :=
      apply_mem_of_pointwise_smul_eq (inv_pointwise_smul_eq (hb1 i (by omega))) hx
    have h := hb2 i hi _ hy
    rw [show b (b⁻¹ x) = x by simp] at h
    have := (Hc (i + 1)).inv_mem h
    simpa using this

@[simp]
theorem mem_chainKernel :
    b ∈ chainKernel Hc n ↔
      (∀ i ≤ n, b • Hc i = Hc i) ∧ ∀ i < n, ∀ x ∈ Hc i, x⁻¹ * b x ∈ Hc (i + 1) := Iff.rfl

theorem chainKernel_le_chainStabilizer : chainKernel Hc n ≤ chainStabilizer Hc n :=
  fun _ hb => hb.1

theorem actsAsZPowOn_one_of_mem_chainKernel (hb : b ∈ chainKernel Hc n) {i : ℕ} (hi : i < n) :
    ActsAsZPowOn b (Hc i) (Hc (i + 1)) 1 :=
  actsAsZPowOn_one_iff.2 (hb.2 i hi)

theorem commutator_le_chainKernel (hp : p.Prime) (hc : IsPrimeFactorChain p Hc n)
    {B : Subgroup (MulAut H)} (hB : B ≤ chainStabilizer Hc n) :
    ⁅B, B⁆ ≤ chainKernel Hc n := by
  refine Subgroup.commutator_le.2 fun u hu v hv => ?_
  have hu' := hB hu
  have hv' := hB hv
  refine ⟨fun i hi => ?_, fun i hi x hx => ?_⟩
  · rw [commutatorElement_def]
    rw [mul_smul, mul_smul, mul_smul, inv_pointwise_smul_eq (hv' i hi),
      inv_pointwise_smul_eq (hu' i hi), hv' i hi, hu' i hi]
  · have hnorm := hc.normal_succ i hi
    obtain ⟨m, hm⟩ := exists_actsAsZPowOn hp (hc.relIndex_succ i hi) (hu' i (by omega))
      (hu' (i + 1) (by omega))
    obtain ⟨l, hl⟩ := exists_actsAsZPowOn hp (hc.relIndex_succ i hi) (hv' i (by omega))
      (hv' (i + 1) (by omega))
    have h1 : ActsAsZPowOn (u * v) (Hc i) (Hc (i + 1)) (m * l) :=
      hm.mul (hu' (i + 1) (by omega)) hl
    have h2 : ActsAsZPowOn (v * u) (Hc i) (Hc (i + 1)) (m * l) := by
      have := hl.mul (hv' (i + 1) (by omega)) hm
      rwa [mul_comm l m] at this
    have hvu : (v * u) • Hc i = Hc i := by rw [mul_smul, hu' i (by omega), hv' i (by omega)]
    have h3 := h1.mul_inv hvu h2
    rw [actsAsZPowOn_one_iff] at h3
    have h4 := h3 x hx
    rwa [show ((u * v) * (v * u)⁻¹ : MulAut H) = ⁅u, v⁆ by rw [commutatorElement_def]; group] at h4

def chainCosetTuples (hle : ∀ i < n, Hc (i + 1) ≤ Hc i) (t₀ : Fin n → H)
    (ht₀ : ∀ i : Fin n, t₀ i ∈ Hc (i : ℕ)) : SubMulAction (chainKernel Hc n) (Fin n → H) where
  carrier := {t | ∀ i : Fin n, (t₀ i)⁻¹ * t i ∈ Hc ((i : ℕ) + 1)}
  smul_mem' := by
    intro b t ht i
    have hti : t i ∈ Hc (i : ℕ) := by
      have h1 : t i = t₀ i * ((t₀ i)⁻¹ * t i) := by group
      rw [h1]
      exact (Hc _).mul_mem (ht₀ i) (hle i i.2 (ht i))
    have h2 : (t i)⁻¹ * (b : MulAut H) (t i) ∈ Hc ((i : ℕ) + 1) := b.2.2 i i.2 _ hti
    have key : (t₀ i)⁻¹ * (b • t) i = ((t₀ i)⁻¹ * t i) * ((t i)⁻¹ * (b : MulAut H) (t i)) := by
      change (t₀ i)⁻¹ * (b : MulAut H) (t i) = _
      group
    rw [key]
    exact (Hc _).mul_mem (ht i) h2

theorem mem_chainCosetTuples {hle : ∀ i < n, Hc (i + 1) ≤ Hc i} {t₀ : Fin n → H}
    {ht₀ : ∀ i : Fin n, t₀ i ∈ Hc (i : ℕ)} {t : Fin n → H} :
    t ∈ chainCosetTuples hle t₀ ht₀ ↔ ∀ i : Fin n, (t₀ i)⁻¹ * t i ∈ Hc ((i : ℕ) + 1) := Iff.rfl

theorem mem_of_mem_chainCosetTuples {hle : ∀ i < n, Hc (i + 1) ≤ Hc i} {t₀ : Fin n → H}
    {ht₀ : ∀ i : Fin n, t₀ i ∈ Hc (i : ℕ)} {t : Fin n → H}
    (ht : t ∈ chainCosetTuples hle t₀ ht₀) (i : Fin n) : t i ∈ Hc (i : ℕ) := by
  have h1 : t i = t₀ i * ((t₀ i)⁻¹ * t i) := by group
  rw [h1]
  exact (Hc _).mul_mem (ht₀ i) (hle i i.2 (mem_chainCosetTuples.1 ht i))

theorem not_mem_of_mem_chainCosetTuples {hle : ∀ i < n, Hc (i + 1) ≤ Hc i} {t₀ : Fin n → H}
    {ht₀ : ∀ i : Fin n, t₀ i ∈ Hc (i : ℕ)} (ht₀' : ∀ i : Fin n, t₀ i ∉ Hc ((i : ℕ) + 1))
    {t : Fin n → H} (ht : t ∈ chainCosetTuples hle t₀ ht₀) (i : Fin n) :
    t i ∉ Hc ((i : ℕ) + 1) := by
  intro hmem
  refine ht₀' i ?_
  have h := (Hc ((i : ℕ) + 1)).mul_mem (mem_chainCosetTuples.1 ht i) ((Hc _).inv_mem hmem)
  have key : (t₀ i)⁻¹ = ((t₀ i)⁻¹ * t i) * (t i)⁻¹ := by group
  have h2 := (Hc ((i : ℕ) + 1)).inv_mem h
  rw [← key] at h2
  simpa using h2

def chainCosetTuplesEquiv (hle : ∀ i < n, Hc (i + 1) ≤ Hc i) (t₀ : Fin n → H)
    (ht₀ : ∀ i : Fin n, t₀ i ∈ Hc (i : ℕ)) :
    ↥(chainCosetTuples hle t₀ ht₀) ≃ ((i : Fin n) → ↥(Hc ((i : ℕ) + 1))) where
  toFun t i := ⟨(t₀ i)⁻¹ * (t : Fin n → H) i, mem_chainCosetTuples.1 t.2 i⟩
  invFun g := ⟨fun i => t₀ i * (g i : H), mem_chainCosetTuples.2 fun i => by simp⟩
  left_inv t := by ext i; simp
  right_inv g := by ext i; simp

theorem card_chainCosetTuples (hle : ∀ i < n, Hc (i + 1) ≤ Hc i) (t₀ : Fin n → H)
    (ht₀ : ∀ i : Fin n, t₀ i ∈ Hc (i : ℕ)) :
    Nat.card ↥(chainCosetTuples hle t₀ ht₀) = ∏ i : Fin n, Nat.card (Hc ((i : ℕ) + 1)) := by
  rw [Nat.card_congr (chainCosetTuplesEquiv hle t₀ ht₀), Nat.card_pi]

theorem exists_card_chainCosetTuples_eq_pow (hc : IsPrimeFactorChain p Hc n)
    (t₀ : Fin n → H) (ht₀ : ∀ i : Fin n, t₀ i ∈ Hc (i : ℕ)) :
    ∃ e : ℕ, Nat.card ↥(chainCosetTuples hc.le_succ t₀ ht₀) = p ^ e := by
  refine ⟨∑ i : Fin n, (n - ((i : ℕ) + 1)), ?_⟩
  rw [card_chainCosetTuples, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun i _ => hc.card_eq_pow (by omega)

theorem stabilizer_chainCosetTuples_eq_bot (hp : p.Prime) (hc : IsPrimeFactorChain p Hc n)
    {t₀ : Fin n → H} (ht₀ : ∀ i : Fin n, t₀ i ∈ Hc (i : ℕ))
    (ht₀' : ∀ i : Fin n, t₀ i ∉ Hc ((i : ℕ) + 1))
    (t : ↥(chainCosetTuples hc.le_succ t₀ ht₀)) :
    stabilizer (chainKernel Hc n) t = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun b hb => ?_
  have hfix : ∀ i : Fin n, (b : MulAut H) ((t : Fin n → H) i) = (t : Fin n → H) i := by
    intro i
    have h := congrArg (fun s : ↥(chainCosetTuples hc.le_succ t₀ ht₀) => (s : Fin n → H) i)
      (mem_stabilizer_iff.1 hb)
    exact h
  have hclos : Subgroup.closure (Set.range (t : Fin n → H)) = ⊤ :=
    hc.closure_range_eq_top hp (mem_of_mem_chainCosetTuples t.2)
      (not_mem_of_mem_chainCosetTuples ht₀' t.2)
  have heq : Set.EqOn ((b : MulAut H) : H →* H) (MonoidHom.id H) (Set.range (t : Fin n → H)) := by
    rintro x ⟨i, rfl⟩
    exact hfix i
  have h2 := MonoidHom.eqOn_closure heq
  rw [hclos] at h2
  refine Subtype.ext (MulEquiv.ext fun x => ?_)
  exact h2 (by simp : x ∈ (⊤ : Subgroup H))

theorem isPGroup_chainKernel (hp : p.Prime) (hc : IsPrimeFactorChain p Hc n) :
    IsPGroup p (chainKernel Hc n) := by
  have hfin : Finite H := hc.finite hp
  by_cases hn : n = 0
  ·
    subst hn
    have h : (⊤ : Subgroup H) = ⊥ := hc.eq_top ▸ hc.eq_bot
    rw [Subgroup.eq_bot_iff_forall] at h
    have : Subsingleton H :=
      ⟨fun a b => by rw [h a (Subgroup.mem_top a), h b (Subgroup.mem_top b)]⟩
    have : Subsingleton (MulAut H) := ⟨fun u v => MulEquiv.ext fun _ => Subsingleton.elim _ _⟩
    exact fun _ => ⟨0, Subsingleton.elim _ _⟩
  choose t₀ ht₀ ht₀' using fun i : Fin n => hc.exists_mem_not_mem hp i.2
  obtain ⟨e, he⟩ := exists_card_chainCosetTuples_eq_pow hc t₀ ht₀
  have hdvd : Nat.card (chainKernel Hc n) ∣ Nat.card ↥(chainCosetTuples hc.le_succ t₀ ht₀) :=
    card_dvd_card_of_forall_stabilizer_eq_bot
      (stabilizer_chainCosetTuples_eq_bot hp hc ht₀ ht₀')
  rw [he] at hdvd
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  exact IsPGroup.of_card hk

theorem isPGroup_commutator_of_isPrimeFactorChain (hp : p.Prime)
    (hc : IsPrimeFactorChain p Hc n) {B : Subgroup (MulAut H)}
    (hB : B ≤ chainStabilizer Hc n) : IsPGroup p ↥(⁅B, B⁆ : Subgroup (MulAut H)) :=
  (isPGroup_chainKernel hp hc).to_le (commutator_le_chainKernel hp hc hB)

theorem exists_card_commutator_eq_pow (hp : p.Prime) (hc : IsPrimeFactorChain p Hc n)
    {B : Subgroup (MulAut H)} (hB : B ≤ chainStabilizer Hc n) :
    ∃ a : ℕ, Nat.card ↥(⁅B, B⁆ : Subgroup (MulAut H)) = p ^ a := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite H := hc.finite hp
  exact (isPGroup_commutator_of_isPrimeFactorChain hp hc hB).exists_card_eq

theorem intCast_dvd_pow_sub_one (hp : p.Prime) (h : ¬ (p : ℤ) ∣ m) :
    (p : ℤ) ∣ m ^ (p - 1) - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hm : (m : ZMod p) ≠ 0 := by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.pow_card_sub_one_eq_one hm, sub_self]

theorem pow_sub_one_mem_chainKernel (hp : p.Prime) (hc : IsPrimeFactorChain p Hc n)
    (hb : b ∈ chainStabilizer Hc n) : b ^ (p - 1) ∈ chainKernel Hc n := by
  refine ⟨fun i hi => ((chainStabilizer Hc n).pow_mem hb (p - 1)) i hi, fun i hi x hx => ?_⟩
  have hnorm := hc.normal_succ i hi
  obtain ⟨m, hm⟩ := exists_actsAsZPowOn hp (hc.relIndex_succ i hi)
    (hb i (by omega)) (hb (i + 1) (by omega))
  have hnd : ¬ (p : ℤ) ∣ m :=
    hm.not_dvd (hc.relIndex_succ i hi) (hb (i + 1) (by omega)) (hc.not_le_succ hp hi)
  have h1 : ActsAsZPowOn (b ^ (p - 1)) (Hc i) (Hc (i + 1)) (m ^ (p - 1)) :=
    hm.pow (hb (i + 1) (by omega)) (p - 1)
  have h2 : ActsAsZPowOn (b ^ (p - 1)) (Hc i) (Hc (i + 1)) 1 :=
    h1.of_dvd_sub (by rw [hc.relIndex_succ i hi]; exact intCast_dvd_pow_sub_one hp hnd)
  have h3 := h2 x hx
  simpa using h3

theorem eq_one_of_mem_chainKernel_of_coprime (hp : p.Prime) (hc : IsPrimeFactorChain p Hc n)
    (hK : b ∈ chainKernel Hc n) (hcop : Nat.Coprime (orderOf b) p) : b = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 (isPGroup_chainKernel hp hc)) ⟨b, hK⟩
  have hk' : orderOf b = p ^ k := by
    rw [← hk, Subgroup.orderOf_coe (⟨b, hK⟩ : chainKernel Hc n)]
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · rw [hk0, pow_zero] at hk'
    exact orderOf_eq_one_iff.1 hk'
  · have hpd : p ∣ orderOf b := by rw [hk']; exact dvd_pow_self p (by omega)
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop.symm hpd) hp.one_lt.ne'

theorem orderOf_dvd_sub_one_of_coprime (hp : p.Prime) (hc : IsPrimeFactorChain p Hc n)
    {B : Subgroup (MulAut H)} (hB : B ≤ chainStabilizer Hc n) {b : MulAut H} (hbB : b ∈ B)
    (hcop : Nat.Coprime (orderOf b) p) : orderOf b ∣ p - 1 :=
  orderOf_dvd_of_pow_eq_one (eq_one_of_mem_chainKernel_of_coprime hp hc
    (pow_sub_one_mem_chainKernel hp hc (hB hbB))
    (Nat.Coprime.coprime_dvd_left (orderOf_pow_dvd _) hcop))

theorem prime_dvd_sub_one_of_dvd_card (hp : p.Prime) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hc : IsPrimeFactorChain p Hc n) {B : Subgroup (MulAut H)}
    (hB : B ≤ chainStabilizer Hc n) (hdvd : q ∣ Nat.card B) : q ∣ p - 1 := by
  have : Fact q.Prime := ⟨hq⟩
  have : Finite H := hc.finite hp
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := B) q hdvd
  have hu' : orderOf (u : MulAut H) = q := by rw [← hu, Subgroup.orderOf_coe]
  have hcop : Nat.Coprime (orderOf (u : MulAut H)) p := by
    rw [hu']
    exact (Nat.coprime_primes hq hp).2 hqp
  have h := orderOf_dvd_sub_one_of_coprime hp hc hB u.2 hcop
  rwa [hu'] at h

end CFSG.FeitThompson
