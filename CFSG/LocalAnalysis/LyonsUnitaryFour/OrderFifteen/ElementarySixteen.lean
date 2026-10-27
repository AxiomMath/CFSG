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

namespace CFSG.LyonsUnitaryFour

@[expose] def IsElementarySixteenOrderFiveAutomizer {H : Type*} [Group H] (P : Subgroup H) :
    Prop :=
  Nonempty (P ≃* Multiplicative (Fin 4 → ZMod 2)) ∧
    ((Subgroup.centralizer (P : Set H)).subgroupOf (Subgroup.normalizer (P : Set H))).index = 5 ∧
    ∀ A : Subgroup H, A ≤ P →
      (∀ n ∈ Subgroup.normalizer (P : Set H), ∀ a ∈ A, n * a * n⁻¹ ∈ A) → A = ⊥ ∨ A = P

section Helpers

variable {H : Type*} [Group H]

theorem elementarySixteen_facts {P : Subgroup H} (e : P ≃* Multiplicative (Fin 4 → ZMod 2)) :
    Nat.card P = 16 ∧ (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧ ∀ x ∈ P, x * x = 1 := by
  refine ⟨?_, fun x hx y hy => ?_, fun x hx => ?_⟩
  · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    rfl
  · have h := e.injective (show e (⟨x, hx⟩ * ⟨y, hy⟩) = e (⟨y, hy⟩ * ⟨x, hx⟩) by
      rw [map_mul, map_mul, mul_comm])
    exact congrArg Subtype.val h
  · have h : e (⟨x, hx⟩ * ⟨x, hx⟩) = e 1 := by
      rw [map_mul, map_one]
      apply Multiplicative.toAdd.injective
      funext i
      simp only [toAdd_mul, toAdd_one, Pi.add_apply, Pi.zero_apply]
      exact CharTwo.add_self_eq_zero _
    exact congrArg Subtype.val (e.injective h)

theorem invariant_of_generator [Finite H] {P : Subgroup H}
    (hidx : ((Subgroup.centralizer (P : Set H)).subgroupOf
      (Subgroup.normalizer (P : Set H))).index = 5)
    {t : H} (htN : t ∈ Subgroup.normalizer (P : Set H)) (htC : t ∉ Subgroup.centralizer (P : Set H))
    {A : Subgroup H} (hAP : A ≤ P) (hA : ∀ a ∈ A, t * a * t⁻¹ ∈ A) :
    ∀ n ∈ Subgroup.normalizer (P : Set H), ∀ a ∈ A, n * a * n⁻¹ ∈ A := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set N := Subgroup.normalizer (P : Set H) with hN
  set C := Subgroup.centralizer (P : Set H) with hC
  have hpow : ∀ k : ℕ, ∀ a ∈ A, t ^ k * a * (t ^ k)⁻¹ ∈ A := by
    intro k
    induction k with
    | zero => intro a ha; simpa using ha
    | succ k ih =>
      intro a ha
      have h := hA _ (ih a ha)
      rw [pow_succ']
      simpa [mul_assoc, mul_inv_rev] using h
  intro n hn a ha
  have hcard : Nat.card (N ⧸ C.subgroupOf N) = 5 := hidx
  have hne : (QuotientGroup.mk ⟨t, htN⟩ : N ⧸ C.subgroupOf N) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact htC
  have htop := zpowers_eq_top_of_prime_card hcard hne
  have hmem : (QuotientGroup.mk ⟨n, hn⟩ : N ⧸ C.subgroupOf N) ∈
      Submonoid.powers (QuotientGroup.mk ⟨t, htN⟩ : N ⧸ C.subgroupOf N) := by
    rw [mem_powers_iff_mem_zpowers, htop]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := hmem
  simp only at hk
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hk
  have hc : ((t ^ k)⁻¹ * n : H) ∈ C := by simpa using hk
  have hca : ((t ^ k)⁻¹ * n) * a * ((t ^ k)⁻¹ * n)⁻¹ = a := by
    have h := (Subgroup.mem_centralizer_iff.mp hc) a (hAP ha)
    rw [← h]
    group
  have h := hpow k a ha
  rw [← hca] at h
  simpa [mul_assoc] using h


section Generator

variable [Finite H] {P : Subgroup H}

omit [Finite H] in
theorem pow_five_mem_centralizer
    (hidx : ((Subgroup.centralizer (P : Set H)).subgroupOf
      (Subgroup.normalizer (P : Set H))).index = 5)
    {m : H} (hm : m ∈ Subgroup.normalizer (P : Set H)) :
    m ^ 5 ∈ Subgroup.centralizer (P : Set H) := by
  have hcard : Nat.card (Subgroup.normalizer (P : Set H) ⧸
      (Subgroup.centralizer (P : Set H)).subgroupOf (Subgroup.normalizer (P : Set H))) = 5 := hidx
  have h := pow_card_eq_one' (G := Subgroup.normalizer (P : Set H) ⧸
      (Subgroup.centralizer (P : Set H)).subgroupOf (Subgroup.normalizer (P : Set H)))
    (x := ((⟨m, hm⟩ : Subgroup.normalizer (P : Set H)) : Subgroup.normalizer (P : Set H) ⧸
      (Subgroup.centralizer (P : Set H)).subgroupOf (Subgroup.normalizer (P : Set H))))
  rw [hcard, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
  simpa using h

theorem exists_pow_inv_mul_mem_centralizer
    (hidx : ((Subgroup.centralizer (P : Set H)).subgroupOf
      (Subgroup.normalizer (P : Set H))).index = 5)
    {n : H} (hnN : n ∈ Subgroup.normalizer (P : Set H)) (hnC : n ∉ Subgroup.centralizer (P : Set H))
    {m : H} (hm : m ∈ Subgroup.normalizer (P : Set H)) :
    ∃ k < 5, (n ^ k)⁻¹ * m ∈ Subgroup.centralizer (P : Set H) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set N := Subgroup.normalizer (P : Set H) with hN
  set C := Subgroup.centralizer (P : Set H) with hC
  have hcard : Nat.card (N ⧸ C.subgroupOf N) = 5 := hidx
  have hne : (QuotientGroup.mk ⟨n, hnN⟩ : N ⧸ C.subgroupOf N) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hnC
  have htop := zpowers_eq_top_of_prime_card hcard hne
  have hmem : (QuotientGroup.mk ⟨m, hm⟩ : N ⧸ C.subgroupOf N) ∈
      Submonoid.powers (QuotientGroup.mk ⟨n, hnN⟩ : N ⧸ C.subgroupOf N) := by
    rw [mem_powers_iff_mem_zpowers, htop]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := hmem
  simp only at hk
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hk
  have hk' : (n ^ k)⁻¹ * m ∈ C := by simpa using hk
  refine ⟨k % 5, Nat.mod_lt _ (by norm_num), ?_⟩
  have hq : (n ^ 5) ^ (k / 5) ∈ C := C.pow_mem (pow_five_mem_centralizer hidx hnN) _
  have hsplit : n ^ k = n ^ (k % 5) * (n ^ 5) ^ (k / 5) := by
    rw [← pow_mul, ← pow_add, Nat.mod_add_div]
  have heq : (n ^ (k % 5))⁻¹ * m = (n ^ 5) ^ (k / 5) * ((n ^ k)⁻¹ * m) := by
    rw [hsplit]
    group
  rw [heq]
  exact C.mul_mem hq hk'

theorem eq_one_of_conj_eq_of_generator
    (hidx : ((Subgroup.centralizer (P : Set H)).subgroupOf
      (Subgroup.normalizer (P : Set H))).index = 5)
    (hirr : ∀ A : Subgroup H, A ≤ P →
      (∀ n ∈ Subgroup.normalizer (P : Set H), ∀ a ∈ A, n * a * n⁻¹ ∈ A) → A = ⊥ ∨ A = P)
    {n : H} (hnN : n ∈ Subgroup.normalizer (P : Set H)) (hnC : n ∉ Subgroup.centralizer (P : Set H))
    {x : H} (hx : x ∈ P) (hfix : n * x * n⁻¹ = x) : x = 1 := by
  set F := P ⊓ Subgroup.centralizer ({n} : Set H) with hF
  have hFinv : ∀ a ∈ F, n * a * n⁻¹ ∈ F := by
    rintro a ⟨haP, haC⟩
    have hah : a * n = n * a := Subgroup.mem_centralizer_singleton_iff.mp haC
    have h : n * a * n⁻¹ = a := by rw [← hah, mul_inv_cancel_right]
    rw [h]
    exact ⟨haP, haC⟩
  rcases hirr F inf_le_left (invariant_of_generator hidx hnN hnC inf_le_left hFinv) with
    hbot | htop
  · have hxn : x * n = n * x := by
      calc x * n = (n * x * n⁻¹) * n := by rw [hfix]
        _ = n * x := by group
    have hxF : x ∈ F := ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hxn⟩
    rw [hbot, Subgroup.mem_bot] at hxF
    exact hxF
  · exfalso
    apply hnC
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyF : y ∈ F := by rw [htop]; exact hy
    exact Subgroup.mem_centralizer_singleton_iff.mp hyF.2

theorem eq_one_of_pow_conj_eq
    (hidx : ((Subgroup.centralizer (P : Set H)).subgroupOf
      (Subgroup.normalizer (P : Set H))).index = 5)
    (hirr : ∀ A : Subgroup H, A ≤ P →
      (∀ n ∈ Subgroup.normalizer (P : Set H), ∀ a ∈ A, n * a * n⁻¹ ∈ A) → A = ⊥ ∨ A = P)
    {n : H} (hnN : n ∈ Subgroup.normalizer (P : Set H)) (hnC : n ∉ Subgroup.centralizer (P : Set H))
    {x : H} (hx : x ∈ P) {k : ℕ} (hk : ¬ 5 ∣ k) (hfix : n ^ k * x * (n ^ k)⁻¹ = x) : x = 1 := by
  apply eq_one_of_conj_eq_of_generator hidx hirr hnN hnC hx
  have hmul : ∀ j : ℕ, n ^ (k * j) * x * (n ^ (k * j))⁻¹ = x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.mul_succ, pow_add]
      calc n ^ (k * j) * n ^ k * x * (n ^ (k * j) * n ^ k)⁻¹ =
          n ^ (k * j) * (n ^ k * x * (n ^ k)⁻¹) * (n ^ (k * j))⁻¹ := by group
        _ = x := by rw [hfix, ih]
  have h5 : ∀ j : ℕ, (n ^ 5) ^ j * x * ((n ^ 5) ^ j)⁻¹ = x := by
    intro j
    have hc := (Subgroup.centralizer (P : Set H)).pow_mem (pow_five_mem_centralizer hidx hnN) j
    have h := (Subgroup.mem_centralizer_iff.mp hc) x hx
    rw [← h]
    group
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, k * a = 5 * b + 1 := by
    have hr : k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
    rcases hr with hr | hr | hr | hr
    · exact ⟨1, k / 5, by omega⟩
    · exact ⟨3, (3 * k) / 5, by omega⟩
    · exact ⟨2, (2 * k) / 5, by omega⟩
    · exact ⟨4, (4 * k) / 5, by omega⟩
  have hsplit : n ^ (k * a) = (n ^ 5) ^ b * n := by rw [hab, pow_succ, pow_mul]
  have h1 := hmul a
  rw [hsplit] at h1
  calc n * x * n⁻¹ = ((n ^ 5) ^ b)⁻¹ * ((n ^ 5) ^ b * n * x * ((n ^ 5) ^ b * n)⁻¹) *
        (n ^ 5) ^ b := by group
    _ = ((n ^ 5) ^ b)⁻¹ * x * (n ^ 5) ^ b := by rw [h1]
    _ = x := by
        have := h5 b
        calc ((n ^ 5) ^ b)⁻¹ * x * (n ^ 5) ^ b =
            ((n ^ 5) ^ b)⁻¹ * ((n ^ 5) ^ b * x * ((n ^ 5) ^ b)⁻¹) * (n ^ 5) ^ b := by
              rw [this]
          _ = x := by group

theorem isConj_iff_exists_pow_conj (S : Sylow 2 H)
    (hcomm : ∀ x ∈ (S : Subgroup H), ∀ y ∈ (S : Subgroup H), x * y = y * x)
    (hidx : ((Subgroup.centralizer ((S : Subgroup H) : Set H)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup H) : Set H))).index = 5)
    {n : H} (hnN : n ∈ Subgroup.normalizer ((S : Subgroup H) : Set H))
    (hnC : n ∉ Subgroup.centralizer ((S : Subgroup H) : Set H))
    {x y : H} (hx : x ∈ (S : Subgroup H)) (hy : y ∈ (S : Subgroup H)) :
    IsConj x y ↔ ∃ k < 5, n ^ k * x * (n ^ k)⁻¹ = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    have : IsMulCommutative (S : Subgroup H) :=
      ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
    have hy' : c⁻¹⁻¹ * x * c⁻¹ ∈ (S : Subgroup H) := by rw [inv_inv, hc]; exact hy
    obtain ⟨m, hm, hmeq⟩ := Sylow.conj_eq_normalizer_conj_of_mem S x c⁻¹ hx hy'
    obtain ⟨k, hk, hkc⟩ := exists_pow_inv_mul_mem_centralizer hidx hnN hnC
      ((Subgroup.normalizer ((S : Subgroup H) : Set H)).inv_mem hm)
    refine ⟨k, hk, ?_⟩
    have hcx := (Subgroup.mem_centralizer_iff.mp hkc) x hx
    rw [← hc]
    calc n ^ k * x * (n ^ k)⁻¹
        = n ^ k * ((n ^ k)⁻¹ * m⁻¹ * x * ((n ^ k)⁻¹ * m⁻¹)⁻¹) * (n ^ k)⁻¹ := by
          rw [← hcx]
          group
      _ = m⁻¹ * x * m := by group
      _ = c⁻¹⁻¹ * x * c⁻¹ := hmeq.symm
      _ = c * x * c⁻¹ := by rw [inv_inv]
  · rintro ⟨k, -, hk⟩
    exact isConj_iff.mpr ⟨n ^ k, hk⟩

end Generator

end Helpers

section Orbits

theorem iterate_ne_self_of_five {X : Type*} (f : X → X) (h5 : ∀ x, f^[5] x = x)
    (hfix : ∀ x, f x ≠ x) (x : X) {k : ℕ} (hk0 : 0 < k) (hk5 : k < 5) : f^[k] x ≠ x := by
  intro hk
  have hmul : ∀ j : ℕ, f^[k * j] x = x := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [Nat.mul_succ, Function.iterate_add_apply, hk, ih]
  have h5mul : ∀ j : ℕ, f^[5 * j] x = x := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [Nat.mul_succ, Function.iterate_add_apply, h5, ih]
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, k * a = 5 * b + 1 := by
    have hr : k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
    rcases hr with hr | hr | hr | hr
    · exact ⟨1, k / 5, by omega⟩
    · exact ⟨3, (3 * k) / 5, by omega⟩
    · exact ⟨2, (2 * k) / 5, by omega⟩
    · exact ⟨4, (4 * k) / 5, by omega⟩
  apply hfix x
  have h := hmul a
  rw [hab, Nat.add_comm, Function.iterate_add_apply, h5mul] at h
  exact h

theorem exists_three_free_orbits {X : Type*} [Fintype X] (hX : Fintype.card X = 15) (f : X → X)
    (h5 : ∀ x, f^[5] x = x) (hfix : ∀ x, f x ≠ x) :
    ∃ r : Fin 3 → X, ∀ y, ∃! ik : Fin 3 × Fin 5, y = f^[(ik.2 : ℕ)] (r ik.1) := by
  classical
  have hmod : ∀ (x : X) (j : ℕ), f^[j] x = f^[j % 5] x := by
    intro x j
    conv_lhs => rw [← Nat.mod_add_div j 5]
    rw [Function.iterate_add_apply]
    congr 1
    induction j / 5 with
    | zero => rfl
    | succ q ih => rw [Nat.mul_succ, Function.iterate_add_apply, h5, ih]
  set orbit : X → Finset X := fun x => Finset.univ.image (fun k : Fin 5 => f^[(k : ℕ)] x)
    with horbit
  have hinj : ∀ x : X, Function.Injective (fun k : Fin 5 => f^[(k : ℕ)] x) := by
    intro x j k hjk
    simp only at hjk
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · have hk : f^[(k : ℕ)] x = f^[(k : ℕ) - j] (f^[(j : ℕ)] x) := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]
      exact iterate_ne_self_of_five f h5 hfix _ (k := (k : ℕ) - j) (by omega) (by omega)
        (by rw [← hk, hjk])
    · have hj : f^[(j : ℕ)] x = f^[(j : ℕ) - k] (f^[(k : ℕ)] x) := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]
      exact iterate_ne_self_of_five f h5 hfix _ (k := (j : ℕ) - k) (by omega) (by omega)
        (by rw [← hj, hjk])
  have hcard : ∀ x, (orbit x).card = 5 := by
    intro x
    rw [horbit, Finset.card_image_of_injective _ (hinj x), Finset.card_univ, Fintype.card_fin]
  have hmem : ∀ x y, y ∈ orbit x ↔ ∃ k : Fin 5, f^[(k : ℕ)] x = y := by
    intro x y
    simp [horbit]
  have horbit_eq : ∀ x y, y ∈ orbit x → orbit y = orbit x := by
    intro x y hy
    obtain ⟨k, rfl⟩ := (hmem x y).mp hy
    ext z
    rw [hmem, hmem]
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨⟨((j : ℕ) + k) % 5, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
      simp only
      rw [← hmod, Function.iterate_add_apply]
    · rintro ⟨j, rfl⟩
      refine ⟨⟨((j : ℕ) + (5 - k)) % 5, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
      simp only
      rw [← hmod, ← Function.iterate_add_apply]
      rw [hmod]
      congr 1
      have := k.2
      omega
  have hdisj : ∀ x y, y ∉ orbit x → Disjoint (orbit x) (orbit y) := by
    intro x y hy
    rw [Finset.disjoint_left]
    intro z hzx hzy
    apply hy
    rw [← horbit_eq x z hzx, horbit_eq y z hzy]
    exact (hmem y y).mpr ⟨0, rfl⟩
  have hself : ∀ x, x ∈ orbit x := fun x => (hmem x x).mpr ⟨0, rfl⟩
  have hne : Nonempty X := by
    rw [← Fintype.card_pos_iff, hX]
    norm_num
  obtain ⟨x₀⟩ := hne
  obtain ⟨x₁, hx₁⟩ : ∃ x₁, x₁ ∉ orbit x₀ := by
    by_contra hall
    push Not at hall
    have : (Finset.univ : Finset X) ⊆ orbit x₀ := fun y _ => hall y
    have := Finset.card_le_card this
    rw [Finset.card_univ, hX, hcard] at this
    omega
  have hd01 := hdisj x₀ x₁ hx₁
  obtain ⟨x₂, hx₂⟩ : ∃ x₂, x₂ ∉ orbit x₀ ∪ orbit x₁ := by
    by_contra hall
    push Not at hall
    have : (Finset.univ : Finset X) ⊆ orbit x₀ ∪ orbit x₁ := fun y _ => hall y
    have := Finset.card_le_card this
    rw [Finset.card_univ, hX, Finset.card_union_of_disjoint hd01, hcard, hcard] at this
    omega
  rw [Finset.mem_union, not_or] at hx₂
  have hd02 := hdisj x₀ x₂ hx₂.1
  have hd12 := hdisj x₁ x₂ hx₂.2
  have hcover : orbit x₀ ∪ orbit x₁ ∪ orbit x₂ = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hd02, hd12⟩),
      Finset.card_union_of_disjoint hd01, hcard, hcard, hcard, hX]
  set r : Fin 3 → X := ![x₀, x₁, x₂] with hr
  have hsep : ∀ i j : Fin 3, i ≠ j → Disjoint (orbit (r i)) (orbit (r j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first | exact absurd rfl hij | skip
    · exact hd01
    · exact hd02
    · exact hd01.symm
    · exact hd12
    · exact hd02.symm
    · exact hd12.symm
  have huniq : ∀ (i i' : Fin 3) (k k' : Fin 5),
      f^[(k : ℕ)] (r i) = f^[(k' : ℕ)] (r i') → i = i' ∧ k = k' := by
    intro i i' k k' h
    by_cases hii : i = i'
    · subst hii
      exact ⟨rfl, hinj _ h⟩
    · exfalso
      exact Finset.disjoint_left.mp (hsep i i' hii) ((hmem _ _).mpr ⟨k, rfl⟩)
        ((hmem _ _).mpr ⟨k', h.symm⟩)
  refine ⟨r, fun y => ?_⟩
  have hy : y ∈ orbit x₀ ∪ orbit x₁ ∪ orbit x₂ := by rw [hcover]; exact Finset.mem_univ y
  rw [Finset.mem_union, Finset.mem_union] at hy
  have hex : ∃ ik : Fin 3 × Fin 5, y = f^[(ik.2 : ℕ)] (r ik.1) := by
    rcases hy with (hy | hy) | hy
    · obtain ⟨k, hk⟩ := (hmem _ _).mp hy
      exact ⟨(0, k), hk.symm⟩
    · obtain ⟨k, hk⟩ := (hmem _ _).mp hy
      exact ⟨(1, k), hk.symm⟩
    · obtain ⟨k, hk⟩ := (hmem _ _).mp hy
      exact ⟨(2, k), hk.symm⟩
  obtain ⟨ik, hik⟩ := hex
  refine ⟨ik, hik, fun jk hjk => ?_⟩
  obtain ⟨h1, h2⟩ := huniq jk.1 ik.1 jk.2 ik.2 (hjk.symm.trans hik)
  exact Prod.ext h1 h2

end Orbits

end CFSG.LyonsUnitaryFour
