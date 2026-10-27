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
public import Mathlib.Tactic.ENatToNat
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

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Kst

open Equiv

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

@[expose] def fixCount (g : Perm Ω) : ℕ := (Finset.univ.filter fun ω => g ω = ω).card

theorem fixCount_modEq (p n : ℕ) [Fact p.Prime]
    {g : Perm Ω} (hg : g ^ p ^ n = 1) : Fintype.card Ω ≡ fixCount g [MOD p] := by
  classical
  let F : Function.End Ω := ⇑g
  have hF : F ^ p ^ n = 1 := by
    funext ω
    have h1 : ((⇑g)^[p ^ n]) ω = ω := by
      rw [Equiv.Perm.iterate_eq_pow, hg]
      rfl
    exact h1
  have h := Equiv.Perm.card_fixedPoints_modEq (f := F) (p := p) (n := n) hF
  have e : Fintype.card (Function.fixedPoints F) = fixCount g := by
    rw [fixCount, ← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun ω => Iff.rfl)
  rw [e] at h
  exact h

structure SixData (G : Subgroup (Perm Ω)) (ω₀ : Ω) (a b : Perm Ω) : Prop where
  card_Ω : Fintype.card Ω = 6
  card_G : Nat.card G = 120
  trans : ∀ ω : Ω, ∃ g ∈ G, g ω₀ = ω
  a_mem : a ∈ G
  b_mem : b ∈ G
  a_fix : a ω₀ = ω₀
  b_fix : b ω₀ = ω₀
  a_five : a ^ 5 = 1
  a_fpf : ∀ ω : Ω, ω ≠ ω₀ → a ω ≠ ω
  b_four : b ^ 4 = 1
  b_two : b ^ 2 ≠ 1
  b_conj : b * a * b⁻¹ = a ^ 2 ∨ b * a * b⁻¹ = a ^ 3

namespace SixData

variable {G : Subgroup (Perm Ω)} {ω₀ : Ω} {a b : Perm Ω}

theorem exists_ne (h : SixData G ω₀ a b) : ∃ ω : Ω, ω ≠ ω₀ := by
  by_contra hcon
  push Not at hcon
  have : Fintype.card Ω ≤ 1 := Fintype.card_le_one_iff.2 fun x y => (hcon x).trans (hcon y).symm
  have h6 := h.card_Ω
  omega

theorem orderOf_a (h : SixData G ω₀ a b) : orderOf a = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨ω, hω⟩ := h.exists_ne
  refine orderOf_eq_prime h.a_five ?_
  intro h1
  exact h.a_fpf ω hω (by rw [h1, Equiv.Perm.one_apply])

theorem a_pow_fix (h : SixData G ω₀ a b) {ω : Ω} (hω : ω ≠ ω₀) {n : ℕ} (hn : (a ^ n) ω = ω) :
    5 ∣ n := by
  by_contra h5
  have h5' : n % 5 ≠ 0 := fun h0 => h5 (Nat.dvd_of_mod_eq_zero h0)
  have e : a ^ (n % 5) = a ^ n := by
    have := pow_mod_orderOf a n
    rwa [h.orderOf_a] at this
  have hmod : (a ^ (n % 5)) ω = ω := by rw [e]; exact hn
  have hr : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have key : ∀ r s : ℕ, (a ^ r) ω = ω → r * s % 5 = 1 → a ω = ω := by
    intro r s hr hrs
    have h1 : ((a ^ r) ^ s) ω = ω := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hr s
    rw [← pow_mul] at h1
    have e2 : a ^ (r * s) = a ^ 1 := by
      have := pow_mod_orderOf a (r * s)
      rw [h.orderOf_a, hrs] at this
      exact this.symm
    rw [e2, pow_one] at h1
    exact h1
  apply h.a_fpf ω hω
  generalize n % 5 = r at h5' hr hmod
  interval_cases r
  · exact absurd rfl h5'
  · exact key 1 1 hmod (by norm_num)
  · exact key 2 3 hmod (by norm_num)
  · exact key 3 2 hmod (by norm_num)
  · exact key 4 4 hmod (by norm_num)

theorem a_pow_inj (h : SixData G ω₀ a b) {ω : Ω} (hω : ω ≠ ω₀) {i j : ℕ} (hi : i < 5) (hj : j < 5)
    (hij : (a ^ i) ω = (a ^ j) ω) : i = j := by
  have key : ∀ i d : ℕ, 0 < d → i + d < 5 → (a ^ i) ω = (a ^ (i + d)) ω → False := by
    intro i d hd hid hij
    have h1 : (a ^ i) ω = (a ^ i) ((a ^ d) ω) := by
      rw [hij, pow_add]
      rfl
    have h2 : (a ^ d) ω = ω := ((a ^ i).injective h1).symm
    have := h.a_pow_fix hω h2
    omega
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    exact key i (d + 1) (by omega) hj (by simpa [add_assoc] using hij)
  · exact heq
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    exact key j (d + 1) (by omega) hi (by simpa [add_assoc] using hij.symm)

theorem exists_a_pow (h : SixData G ω₀ a b) {ω ω' : Ω} (hω : ω ≠ ω₀) (hω' : ω' ≠ ω₀) :
    ∃ i, i < 5 ∧ (a ^ i) ω = ω' := by
  classical
  set S : Finset Ω := (Finset.range 5).image (fun i => (a ^ i) ω) with hS
  have hinj : Set.InjOn (fun i => (a ^ i) ω) (Finset.range 5 : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact h.a_pow_inj hω hi hj hij
  have hcard : S.card = 5 := by
    rw [hS, Finset.card_image_of_injOn hinj]
    simp
  have hsub : S ⊆ Finset.univ.erase ω₀ := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩
    intro hi
    apply hω
    have hfix : (a ^ i) ω₀ = ω₀ := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h.a_fix i
    exact (a ^ i).injective (hi.trans hfix.symm)
  have hXcard : (Finset.univ.erase ω₀).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, h.card_Ω]
  have heq : S = Finset.univ.erase ω₀ :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hXcard])
  have hmem : ω' ∈ S := by
    rw [heq]
    simp [hω']
  obtain ⟨i, hi, hiω⟩ := Finset.mem_image.1 hmem
  exact ⟨i, Finset.mem_range.1 hi, hiω⟩

theorem exists_fix_b (h : SixData G ω₀ a b) : ∃ ω₁ : Ω, ω₁ ≠ ω₀ ∧ b ω₁ = ω₁ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : b ^ 2 ^ 2 = 1 := by
    norm_num
    exact h.b_four
  have hmod := fixCount_modEq 2 2 h4
  rw [h.card_Ω] at hmod
  have hge1 : 1 ≤ fixCount b := Finset.card_pos.2 ⟨ω₀, by simp [h.b_fix]⟩
  have hge2 : 2 ≤ fixCount b := by
    unfold Nat.ModEq at hmod
    omega
  by_contra hcon
  push Not at hcon
  have hle : fixCount b ≤ 1 := by
    unfold fixCount
    rw [Finset.card_le_one]
    intro x hx y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    have hx' : x = ω₀ := by
      by_contra hne
      exact hcon x hne hx
    have hy' : y = ω₀ := by
      by_contra hne
      exact hcon y hne hy
    rw [hx', hy']
  omega

theorem a_pow_four (h : SixData G ω₀ a b) : a ^ 4 = a⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ]
  exact h.a_five

theorem b_sq_conj (h : SixData G ω₀ a b) : b ^ 2 * a * (b ^ 2)⁻¹ = a⁻¹ := by
  have e : b ^ 2 * a * (b ^ 2)⁻¹ = b * (b * a * b⁻¹) * b⁻¹ := by
    rw [pow_two]
    group
  rw [e, ← h.a_pow_four]
  rcases h.b_conj with hc | hc
  · rw [hc]
    have : b * a ^ 2 * b⁻¹ = (b * a * b⁻¹) ^ 2 := by rw [conj_pow]
    rw [this, hc, ← pow_mul]
  · rw [hc]
    have : b * a ^ 3 * b⁻¹ = (b * a * b⁻¹) ^ 3 := by rw [conj_pow]
    rw [this, hc, ← pow_mul]
    calc a ^ (3 * 3) = a ^ 5 * a ^ 4 := by rw [← pow_add]
      _ = a ^ 4 := by rw [h.a_five, one_mul]

theorem fix_b_sq (h : SixData G ω₀ a b) {ω₁ : Ω} (hω₁ : ω₁ ≠ ω₀) (hb : b ω₁ = ω₁) {ω : Ω}
    (hω : (b ^ 2) ω = ω) : ω = ω₀ ∨ ω = ω₁ := by
  by_cases h0 : ω = ω₀
  · exact Or.inl h0
  right
  obtain ⟨i, hi, hiω⟩ := h.exists_a_pow hω₁ h0
  have hconj : b ^ 2 * a ^ i * (b ^ 2)⁻¹ = a ^ (4 * i) := by
    rw [← conj_pow, h.b_sq_conj, ← h.a_pow_four, ← pow_mul]
  have hb2 : (b ^ 2) ω₁ = ω₁ := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hb 2
  have h1 : (b ^ 2) ((a ^ i) ω₁) = (a ^ (4 * i)) ω₁ := by
    have e : b ^ 2 * a ^ i = (b ^ 2 * a ^ i * (b ^ 2)⁻¹) * b ^ 2 := by group
    calc (b ^ 2) ((a ^ i) ω₁) = (b ^ 2 * a ^ i) ω₁ := rfl
      _ = ((b ^ 2 * a ^ i * (b ^ 2)⁻¹) * b ^ 2) ω₁ := by rw [← e]
      _ = (a ^ (4 * i)) ω₁ := by rw [hconj]; show (a ^ (4 * i)) ((b ^ 2) ω₁) = _; rw [hb2]
  rw [← hiω] at hω
  rw [h1] at hω
  have h2 : (a ^ i) ((a ^ (3 * i)) ω₁) = (a ^ i) ω₁ := by
    have : a ^ (4 * i) = a ^ i * a ^ (3 * i) := by rw [← pow_add]; congr 1; omega
    rw [this] at hω
    exact hω
  have h3 : (a ^ (3 * i)) ω₁ = ω₁ := (a ^ i).injective h2
  have h4 := h.a_pow_fix hω₁ h3
  have hi0 : i = 0 := by omega
  rw [← hiω, hi0, pow_zero]
  rfl

theorem two_trans (h : SixData G ω₀ a b) (p q p' q' : Ω) (hp : p ≠ p') (hq : q ≠ q') :
    ∃ g ∈ G, g p = q ∧ g p' = q' := by
  obtain ⟨cp, hcp, hcpω⟩ := h.trans p
  obtain ⟨cq, hcq, hcqω⟩ := h.trans q
  have hx0 : cp⁻¹ p' ≠ ω₀ := by
    intro hx0
    apply hp
    have : p' = cp ω₀ := by rw [← hx0]; simp
    rw [this, hcpω]
  have hy0 : cq⁻¹ q' ≠ ω₀ := by
    intro hy0
    apply hq
    have : q' = cq ω₀ := by rw [← hy0]; simp
    rw [this, hcqω]
  obtain ⟨i, -, hiy⟩ := h.exists_a_pow hx0 hy0
  have hai : a ^ i ∈ G := pow_mem h.a_mem i
  have hfix : (a ^ i) ω₀ = ω₀ := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h.a_fix i
  refine ⟨cq * a ^ i * cp⁻¹, mul_mem (mul_mem hcq hai) (inv_mem hcp), ?_, ?_⟩
  · have h1 : cp⁻¹ p = ω₀ := by rw [← hcpω]; simp
    show cq ((a ^ i) (cp⁻¹ p)) = q
    rw [h1, hfix, hcqω]
  · show cq ((a ^ i) (cp⁻¹ p')) = q'
    rw [hiy]
    simp

theorem orderOf_b (h : SixData G ω₀ a b) : orderOf b = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : ¬ b ^ 2 ^ 1 = 1 := by simpa using h.b_two
  have h2 : b ^ 2 ^ (1 + 1) = 1 := by simpa using h.b_four
  have := orderOf_eq_prime_pow h1 h2
  simpa using this

theorem card_stab (h : SixData G ω₀ a b) : {g : Perm Ω | g ∈ G ∧ g ω₀ = ω₀}.ncard = 20 := by
  classical
  haveI : MulAction.IsPretransitive ↥G Ω := ⟨fun x y => by
    obtain ⟨gx, hgx, hx⟩ := h.trans x
    obtain ⟨gy, hgy, hy⟩ := h.trans y
    refine ⟨⟨gy * gx⁻¹, mul_mem hgy (inv_mem hgx)⟩, ?_⟩
    show (gy * gx⁻¹) x = y
    rw [← hx, ← hy]
    simp⟩
  have h1 := MulAction.card_orbit_mul_card_stabilizer_eq_card_group ↥G ω₀
  simp only [← Nat.card_eq_fintype_card] at h1
  rw [MulAction.orbit_eq_univ, Nat.card_univ, Nat.card_eq_fintype_card, h.card_Ω, h.card_G] at h1
  have h2 : Nat.card (MulAction.stabilizer ↥G ω₀) = 20 := by omega
  have himg : {g : Perm Ω | g ∈ G ∧ g ω₀ = ω₀} =
      Subtype.val '' ((MulAction.stabilizer ↥G ω₀ : Subgroup ↥G) : Set ↥G) := by
    ext g
    constructor
    · rintro ⟨hg, hg0⟩
      exact ⟨⟨g, hg⟩, hg0, rfl⟩
    · rintro ⟨g', hg', rfl⟩
      exact ⟨g'.2, hg'⟩
  rw [himg, Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq]
  exact h2

theorem stab_eq (h : SixData G ω₀ a b) {ω₁ : Ω} (hω₁ : ω₁ ≠ ω₀) (hb : b ω₁ = ω₁) {g : Perm Ω}
    (hg : g ∈ G) (hg0 : g ω₀ = ω₀) : ∃ i j : ℕ, i < 5 ∧ j < 4 ∧ g = a ^ i * b ^ j := by
  classical
  set T : Finset (Perm Ω) := (Finset.range 5 ×ˢ Finset.range 4).image
    (fun ij : ℕ × ℕ => a ^ ij.1 * b ^ ij.2) with hT
  have hinj : Set.InjOn (fun ij : ℕ × ℕ => a ^ ij.1 * b ^ ij.2)
      ((Finset.range 5 ×ˢ Finset.range 4 : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' he
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio] at hij hij'
    have he' : a ^ i * b ^ j = a ^ i' * b ^ j' := he
    have hbj : (b ^ j) ω₁ = ω₁ := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hb j
    have hbj' : (b ^ j') ω₁ = ω₁ := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hb j'
    have h1 : (a ^ i) ω₁ = (a ^ i') ω₁ := by
      have := congrArg (fun f : Perm Ω => f ω₁) he'
      simpa [Perm.mul_apply, hbj, hbj'] using this
    have hii : i = i' := h.a_pow_inj hω₁ hij.1 hij'.1 h1
    subst hii
    have hjj : b ^ j = b ^ j' := mul_left_cancel he'
    have hjj' : j = j' := by
      have := pow_injOn_Iio_orderOf (x := b)
      rw [h.orderOf_b] at this
      exact this (by simpa using hij.2) (by simpa using hij'.2) hjj
    rw [hjj']
  have hcard : T.card = 20 := by
    rw [hT, Finset.card_image_of_injOn hinj]
    simp
  have hsub : (T : Set (Perm Ω)) ⊆ {g : Perm Ω | g ∈ G ∧ g ω₀ = ω₀} := by
    intro f hf
    obtain ⟨⟨i, j⟩, -, rfl⟩ := Finset.mem_image.1 hf
    refine ⟨mul_mem (pow_mem h.a_mem i) (pow_mem h.b_mem j), ?_⟩
    show (a ^ i) ((b ^ j) ω₀) = ω₀
    rw [Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h.b_fix j,
      Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h.a_fix i]
  have heq : (T : Set (Perm Ω)) = {g : Perm Ω | g ∈ G ∧ g ω₀ = ω₀} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [h.card_stab, Set.ncard_coe_finset, hcard])
      (Set.toFinite _)
  have hmem : g ∈ (T : Set (Perm Ω)) := by
    rw [heq]
    exact ⟨hg, hg0⟩
  obtain ⟨⟨i, j⟩, hij, hgij⟩ := Finset.mem_image.1 hmem
  simp only [Finset.mem_product, Finset.mem_range] at hij
  exact ⟨i, j, hij.1, hij.2, hgij.symm⟩

theorem eq_pow_b_of_fix_two (h : SixData G ω₀ a b) {ω₁ : Ω} (hω₁ : ω₁ ≠ ω₀) (hb : b ω₁ = ω₁)
    {g : Perm Ω} (hg : g ∈ G) (hg0 : g ω₀ = ω₀) (hg1 : g ω₁ = ω₁) :
    ∃ j : ℕ, j < 4 ∧ g = b ^ j := by
  obtain ⟨i, j, hi, hj, rfl⟩ := h.stab_eq hω₁ hb hg hg0
  have hbj : (b ^ j) ω₁ = ω₁ := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hb j
  have h1 : (a ^ i) ω₁ = ω₁ := by
    have : (a ^ i) ((b ^ j) ω₁) = ω₁ := hg1
    rwa [hbj] at this
  have h5 := h.a_pow_fix hω₁ h1
  have hi0 : i = 0 := by omega
  exact ⟨j, hj, by rw [hi0, pow_zero, one_mul]⟩

theorem fix_b_pow (h : SixData G ω₀ a b) {ω₁ : Ω} (hω₁ : ω₁ ≠ ω₀) (hb : b ω₁ = ω₁) {j : ℕ}
    (hj : j < 4) (hj0 : j ≠ 0) {ω : Ω} (hω : (b ^ j) ω = ω) : ω = ω₀ ∨ ω = ω₁ := by
  have hb1 : b ω = ω → (b ^ 2) ω = ω := fun h1 =>
    Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h1 2
  apply h.fix_b_sq hω₁ hb
  interval_cases j
  · exact absurd rfl hj0
  · exact hb1 hω
  · exact hω
  · apply hb1
    have h3 : (b * b ^ 3) ω = b ω := by rw [Perm.mul_apply, hω]
    rw [← pow_succ'] at h3
    rwa [h.b_four, Perm.one_apply, eq_comm] at h3

theorem eq_one_of_fix_three (h : SixData G ω₀ a b) {g : Perm Ω} (hg : g ∈ G) (hg0 : g ω₀ = ω₀)
    {x y : Ω} (hx : x ≠ ω₀) (hy : y ≠ ω₀) (hxy : x ≠ y) (hgx : g x = x) (hgy : g y = y) :
    g = 1 := by
  obtain ⟨ω₁, hω₁, hb⟩ := h.exists_fix_b
  obtain ⟨i, -, hix⟩ := h.exists_a_pow hx hω₁
  set d : Perm Ω := a ^ i with hd
  have hdG : d ∈ G := pow_mem h.a_mem i
  have hd0 : d ω₀ = ω₀ := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h.a_fix i
  have hg₂G : d * g * d⁻¹ ∈ G := mul_mem (mul_mem hdG hg) (inv_mem hdG)
  have hconj : ∀ z : Ω, g z = z → (d * g * d⁻¹) (d z) = d z := by
    intro z hz
    simp [Perm.mul_apply, hz]
  have h20 : (d * g * d⁻¹) ω₀ = ω₀ := by
    have := hconj ω₀ hg0
    rwa [hd0] at this
  have h21 : (d * g * d⁻¹) ω₁ = ω₁ := by
    have := hconj x hgx
    rwa [hix] at this
  obtain ⟨j, hj, hgj⟩ := h.eq_pow_b_of_fix_two hω₁ hb hg₂G h20 h21
  by_cases hj0 : j = 0
  · rw [hj0, pow_zero] at hgj
    have : g = d⁻¹ * (d * g * d⁻¹) * d := by group
    rw [this, hgj]
    group
  · exfalso
    have hyfix := hconj y hgy
    rw [hgj] at hyfix
    have hdy0 : d y ≠ ω₀ := by
      intro h0
      apply hy
      have := (d).injective (h0.trans hd0.symm)
      exact this
    have hdy1 : d y ≠ ω₁ := by
      intro h1
      apply hxy
      have : d x = d y := hix.trans h1.symm
      exact (d.injective this)
    rcases h.fix_b_pow hω₁ hb hj hj0 hyfix with h0 | h1
    · exact hdy0 h0
    · exact hdy1 h1

theorem fixCount_le_two (h : SixData G ω₀ a b) {g : Perm Ω} (hg : g ∈ G) (hg1 : g ≠ 1) :
    fixCount g ≤ 2 := by
  by_contra hcon
  push Not at hcon
  unfold fixCount at hcon
  obtain ⟨p₁, hp₁, p₂, hp₂, p₃, hp₃, h12, h13, h23⟩ := Finset.two_lt_card.1 hcon
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂ hp₃
  obtain ⟨c', hc', hc'ω⟩ := h.trans p₁
  have hc : c'⁻¹ ∈ G := inv_mem hc'
  have hcp₁ : c'⁻¹ p₁ = ω₀ := by rw [← hc'ω]; simp
  have hg₁G : c'⁻¹ * g * c'⁻¹⁻¹ ∈ G := mul_mem (mul_mem hc hg) (inv_mem hc)
  have hconj : ∀ z : Ω, g z = z → (c'⁻¹ * g * c'⁻¹⁻¹) (c'⁻¹ z) = c'⁻¹ z := by
    intro z hz
    simp [Perm.mul_apply, hz]
  have h0 : (c'⁻¹ * g * c'⁻¹⁻¹) ω₀ = ω₀ := by
    have := hconj p₁ hp₁
    rwa [hcp₁] at this
  have hx : c'⁻¹ p₂ ≠ ω₀ := by
    intro h0
    apply h12
    exact (c'⁻¹).injective (hcp₁.trans h0.symm)
  have hy : c'⁻¹ p₃ ≠ ω₀ := by
    intro h0
    apply h13
    exact (c'⁻¹).injective (hcp₁.trans h0.symm)
  have hxy : c'⁻¹ p₂ ≠ c'⁻¹ p₃ := fun he => h23 ((c'⁻¹).injective he)
  have h1 := h.eq_one_of_fix_three hg₁G h0 hx hy hxy (hconj p₂ hp₂) (hconj p₃ hp₃)
  apply hg1
  have : g = c'⁻¹⁻¹ * (c'⁻¹ * g * c'⁻¹⁻¹) * c'⁻¹ := by group
  rw [this, h1]
  group

theorem fixCount_invol (h : SixData G ω₀ a b) {g : Perm Ω} (hg : g ∈ G) (hg1 : g ≠ 1)
    (hg2 : g * g = 1) : fixCount g = 0 ∨ fixCount g = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : g ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two]; exact hg2
  have hmod := fixCount_modEq 2 1 h2
  rw [h.card_Ω] at hmod
  have hle := h.fixCount_le_two hg hg1
  unfold Nat.ModEq at hmod
  omega

theorem fixCount_b_sq (h : SixData G ω₀ a b) : fixCount (b ^ 2) = 2 := by
  have hG : b ^ 2 ∈ G := pow_mem h.b_mem 2
  have hsq : b ^ 2 * b ^ 2 = 1 := by rw [← pow_add]; exact h.b_four
  have hge1 : 1 ≤ fixCount (b ^ 2) :=
    Finset.card_pos.2 ⟨ω₀, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h.b_fix 2⟩
  rcases h.fixCount_invol hG h.b_two hsq with h0 | h2
  · omega
  · exact h2

theorem invol_eq_of_fix_two (h : SixData G ω₀ a b) {p q : Ω} (hpq : p ≠ q) {g g' : Perm Ω}
    (hg : g ∈ G) (hg' : g' ∈ G) (hg1 : g ≠ 1) (hg1' : g' ≠ 1) (hgg : g * g = 1) (hgg' : g' * g' = 1)
    (hgp : g p = p) (hgq : g q = q) (hgp' : g' p = p) (hgq' : g' q = q) : g = g' := by
  obtain ⟨ω₁, hω₁, hb⟩ := h.exists_fix_b
  obtain ⟨c, hc, hcp, hcq⟩ := h.two_trans p ω₀ q ω₁ hpq hω₁.symm
  have hconj : ∀ f : Perm Ω, ∀ z : Ω, f z = z → (c * f * c⁻¹) (c z) = c z := by
    intro f z hz
    simp [Perm.mul_apply, hz]
  have key : ∀ f : Perm Ω, f ∈ G → f ≠ 1 → f * f = 1 → f p = p → f q = q → c * f * c⁻¹ = b ^ 2 := by
    intro f hf hf1 hff hfp hfq
    have hfG : c * f * c⁻¹ ∈ G := mul_mem (mul_mem hc hf) (inv_mem hc)
    have e0 : (c * f * c⁻¹) ω₀ = ω₀ := by
      have := hconj f p hfp
      rwa [hcp] at this
    have e1 : (c * f * c⁻¹) ω₁ = ω₁ := by
      have := hconj f q hfq
      rwa [hcq] at this
    obtain ⟨j, hj, hfj⟩ := h.eq_pow_b_of_fix_two hω₁ hb hfG e0 e1
    have hne : c * f * c⁻¹ ≠ 1 := by
      intro h1
      apply hf1
      have : f = c⁻¹ * (c * f * c⁻¹) * c := by group
      rw [this, h1]
      group
    have hsq : (c * f * c⁻¹) * (c * f * c⁻¹) = 1 := by
      have : (c * f * c⁻¹) * (c * f * c⁻¹) = c * (f * f) * c⁻¹ := by group
      rw [this, hff]
      group
    rw [hfj] at hne hsq ⊢
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hne (pow_zero b)
    have h4 : b ^ (j + j) = 1 := by rw [pow_add]; exact hsq
    have hdvd : 4 ∣ j + j := by
      rw [← h.orderOf_b]
      exact orderOf_dvd_of_pow_eq_one h4
    have hj2 : j = 2 := by omega
    rw [hj2]
  have e1 := key g hg hg1 hgg hgp hgq
  have e2 := key g' hg' hg1' hgg' hgp' hgq'
  have : c * g * c⁻¹ = c * g' * c⁻¹ := by rw [e1, e2]
  have h3 : g = g' := by
    have := mul_right_cancel (mul_left_cancel (a := c) (b := g * c⁻¹) (c := g' * c⁻¹)
      (by simpa [mul_assoc] using this))
    exact this.symm ▸ rfl
  exact h3

end SixData

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Kst
