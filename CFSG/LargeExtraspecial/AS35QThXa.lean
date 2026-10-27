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
public import Mathlib.GroupTheory.Commutator.Finite
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

namespace CFSG.LargeExtraspecial.AS35QTh

variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem exists_sq_eq_of_odd {u : H} (hu : Odd (orderOf u)) : ∃ k : ℕ, u ^ k * u ^ k = u := by
  obtain ⟨m, hm⟩ := hu
  refine ⟨m + 1, ?_⟩
  rw [← pow_add, show m + 1 + (m + 1) = orderOf u + 1 by omega, pow_succ, pow_orderOf_eq_one,
    one_mul]

omit [Finite H] in
theorem odd_orderOf_of_mem {X : Subgroup H} (hX : Odd (Nat.card X)) {x : H} (hx : x ∈ X) :
    Odd (orderOf x) := by
  have h := Subgroup.orderOf_dvd_natCard X hx
  exact hX.of_dvd_nat h

omit [Finite H] in
theorem exists_fixed_mul_inverted {X : Subgroup H} (hX : Odd (Nat.card X)) {t : H}
    (ht : t * t = 1) (htX : ∀ x ∈ X, t * x * t⁻¹ ∈ X) {x : H} (hx : x ∈ X) :
    ∃ c w : H, c ∈ X ∧ w ∈ Subgroup.zpowers (x⁻¹ * (t * x * t⁻¹)) ∧ t * c * t⁻¹ = c ∧
      t * w * t⁻¹ = w⁻¹ ∧ x = c * w := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  set u := x⁻¹ * (t * x * t⁻¹) with hu
  have huX : u ∈ X := X.mul_mem (X.inv_mem hx) (htX x hx)
  have hσu : t * u * t⁻¹ = u⁻¹ := by
    rw [hu, htinv]
    calc t * (x⁻¹ * (t * x * t)) * t = t * x⁻¹ * t * x * (t * t) := by group
      _ = t * x⁻¹ * t * x := by rw [ht, mul_one]
      _ = (x⁻¹ * (t * x * t))⁻¹ := by
        rw [show (x⁻¹ * (t * x * t))⁻¹ = t⁻¹ * x⁻¹ * t⁻¹ * x by group, htinv]
  obtain ⟨k, hk⟩ := exists_sq_eq_of_odd (odd_orderOf_of_mem hX huX)
  have hσpow : ∀ n : ℕ, t * u ^ n * t⁻¹ = (u ^ n)⁻¹ := by
    intro n
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hσu, inv_pow]
  set w₀ := u ^ k with hw₀
  refine ⟨x * w₀, w₀⁻¹, X.mul_mem hx (X.pow_mem huX k), Subgroup.inv_mem _
    (Subgroup.pow_mem _ (Subgroup.mem_zpowers u) k), ?_, ?_, by group⟩
  · have hxu : x * u = t * x * t⁻¹ := by rw [hu]; group
    calc t * (x * w₀) * t⁻¹ = (t * x * t⁻¹) * (t * w₀ * t⁻¹) := by group
      _ = (t * x * t⁻¹) * w₀⁻¹ := by rw [hw₀, hσpow k]
      _ = x * u * w₀⁻¹ := by rw [hxu]
      _ = x * (w₀ * w₀) * w₀⁻¹ := by rw [hk]
      _ = x * w₀ := by group
  · rw [show t * w₀⁻¹ * t⁻¹ = (t * w₀ * t⁻¹)⁻¹ by group, hσpow k, inv_inv]

theorem card_center_eq_three {X : Type*} [Group X] [Finite X] (hcard : Nat.card X = 27)
    (hnc : ∃ a b : X, a * b ≠ b * a) : Nat.card (Subgroup.center X) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 X := IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  obtain ⟨k, hk0, hk⟩ := IsPGroup.card_center_eq_prime_pow (p := 3) (G := X) (n := 3)
    (by rw [hcard]; norm_num) (by norm_num)
  have hdvd : 3 ^ k ∣ 3 ^ 3 := by
    rw [← hk, show (3 : ℕ) ^ 3 = 27 by norm_num, ← hcard]
    exact Subgroup.card_subgroup_dvd_card _
  have hk3 : k ≤ 3 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  obtain ⟨a, b, hab⟩ := hnc
  have hcomm_of : IsMulCommutative X → False := fun h => hab (h.is_comm.comm a b)
  interval_cases k
  · simpa using hk
  · exfalso
    apply hcomm_of
    have hq : Nat.card (X ⧸ Subgroup.center X) = 3 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
      rw [hcard, hk] at h
      omega
    have : IsCyclic (X ⧸ Subgroup.center X) := isCyclic_of_prime_card hq
    exact isMulCommutative_of_isCyclic_quotient_center_self X
  · exfalso
    apply hcomm_of
    have htop : Subgroup.center X = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hk, hcard]; norm_num)
    exact ⟨⟨fun a b => (Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top b) a)⟩⟩

theorem card_quotient_center {X : Type*} [Group X] [Finite X] (hcard : Nat.card X = 27)
    (hnc : ∃ a b : X, a * b ≠ b * a) : Nat.card (X ⧸ Subgroup.center X) = 9 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
  rw [hcard, card_center_eq_three hcard hnc] at h
  omega

theorem commutator_mem_center {X : Type*} [Group X] [Finite X] (hcard : Nat.card X = 27)
    (hnc : ∃ a b : X, a * b ≠ b * a) (a b : X) : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
    (G := X ⧸ Subgroup.center X) (by rw [card_quotient_center hcard hnc]; norm_num)).is_comm.comm
  rw [← QuotientGroup.eq_one_iff]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [hcomm (a : X ⧸ Subgroup.center X) (b : X ⧸ Subgroup.center X)]
  group

theorem pow_three_mem_center {X : Type*} [Group X] [Finite X] (hcard : Nat.card X = 27)
    (hnc : ∃ a b : X, a * b ≠ b * a) (a : X) : a ^ 3 ∈ Subgroup.center X := by
  have hq := card_quotient_center hcard hnc
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
  set ā : X ⧸ Subgroup.center X := (a : X ⧸ Subgroup.center X)
  have hdvd : orderOf ā ∣ 9 := hq ▸ orderOf_dvd_natCard ā
  have hne : orderOf ā ≠ 9 := by
    intro h9
    have : IsCyclic (X ⧸ Subgroup.center X) :=
      isCyclic_of_orderOf_eq_card ā (by rw [h9, hq])
    obtain ⟨a, b, hab⟩ := hnc
    exact hab ((isMulCommutative_of_isCyclic_quotient_center_self X).is_comm.comm a b)
  have h3 : orderOf ā ∣ 3 := by
    have : orderOf ā ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [hdiv] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h
    · rw [h]; norm_num
    · rw [h]
    · exact absurd h hne
  exact orderOf_dvd_iff_pow_eq_one.mp h3

theorem exists_heisenberg_basis {X : Subgroup H} (hcard : Nat.card X = 27)
    (hnc : ∃ x ∈ X, ∃ y ∈ X, x * y ≠ y * x) {t : H} (ht : t * t = 1)
    (htX : ∀ x ∈ X, t * x * t⁻¹ ∈ X)
    (hC : Nat.card (X ⊓ Subgroup.centralizer {t} : Subgroup H) = 3)
    (hZt : ∀ c ∈ X, (∀ x ∈ X, c * x = x * c) → c * t = t * c) :
    ∃ a b ζ : H, a ∈ X ∧ b ∈ X ∧ ζ ∈ X ∧ (∀ x ∈ X, ζ * x = x * ζ) ∧ ζ ≠ 1 ∧ ζ ^ 3 = 1 ∧
      a * b = ζ * (b * a) ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧
      (∀ x ∈ X, x * t = t * x → x ∈ Subgroup.zpowers ζ) ∧
      (∀ c ∈ X, (∀ x ∈ X, c * x = x * c) → c ∈ Subgroup.zpowers ζ) := by
  classical
  have hodd : Odd (Nat.card X) := by rw [hcard]; decide
  have hncX : ∃ a b : X, a * b ≠ b * a := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩
  set Z : Subgroup H := (Subgroup.center X).map X.subtype with hZ
  have hZcard : Nat.card Z = 3 := by
    rw [hZ, Subgroup.card_map_of_injective X.subtype_injective]
    exact card_center_eq_three hcard hncX
  have hmemZ : ∀ c : H, c ∈ Z ↔ c ∈ X ∧ ∀ x ∈ X, c * x = x * c := by
    intro c
    constructor
    · rintro ⟨c', hc', rfl⟩
      refine ⟨c'.2, fun x hx => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc' ⟨x, hx⟩).symm
    · rintro ⟨hcX, hc⟩
      refine ⟨⟨c, hcX⟩, Subgroup.mem_center_iff.mpr fun x => ?_, rfl⟩
      exact Subtype.ext (hc x x.2).symm
  set C : Subgroup H := X ⊓ Subgroup.centralizer {t} with hCdef
  have hZC : Z ≤ C := by
    intro c hc
    obtain ⟨hcX, hcc⟩ := (hmemZ c).mp hc
    exact ⟨hcX, Subgroup.mem_centralizer_singleton_iff.mpr (hZt c hcX hcc)⟩
  have hZeqC : Z = C := Subgroup.eq_of_le_of_card_ge hZC (by rw [hZcard, hC])
  have hCcent : ∀ c ∈ C, c ∈ X ∧ ∀ x ∈ X, c * x = x * c := fun c hc =>
    (hmemZ c).mp (hZeqC ▸ hc)
  obtain ⟨a₀, ha₀, b₀, hb₀, hab₀⟩ := hnc
  have hdec : ∀ x ∈ X, ∃ c w : H, c ∈ C ∧ w ∈ X ∧ t * w * t⁻¹ = w⁻¹ ∧ x = c * w := by
    intro x hx
    obtain ⟨c, w, hcX, hwz, hc, hw, hxcw⟩ := exists_fixed_mul_inverted hodd ht htX hx
    have hwX : w ∈ X := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hwz
      exact X.zpow_mem (X.mul_mem (X.inv_mem hx) (htX x hx)) k
    refine ⟨c, w, ⟨hcX, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, hwX, hw, hxcw⟩
    calc c * t = t * c * t⁻¹ * t := by rw [hc]
      _ = t * c := by group
  obtain ⟨c₁, w₁, hc₁, hw₁, hσ₁, rfl⟩ := hdec a₀ ha₀
  obtain ⟨c₂, w₂, hc₂, hw₂, hσ₂, rfl⟩ := hdec b₀ hb₀
  obtain ⟨-, hc₁c⟩ := hCcent c₁ hc₁
  obtain ⟨hc₂X, hc₂c⟩ := hCcent c₂ hc₂
  have hw : w₁ * w₂ ≠ w₂ * w₁ := by
    intro h
    apply hab₀
    calc c₁ * w₁ * (c₂ * w₂) = c₁ * (w₁ * c₂) * w₂ := by group
      _ = c₁ * (c₂ * w₁) * w₂ := by rw [← hc₂c w₁ hw₁]
      _ = (c₁ * c₂) * (w₁ * w₂) := by group
      _ = (c₂ * c₁) * (w₂ * w₁) := by rw [hc₁c c₂ hc₂X, h]
      _ = c₂ * (c₁ * w₂) * w₁ := by group
      _ = c₂ * (w₂ * c₁) * w₁ := by rw [hc₁c w₂ hw₂]
      _ = c₂ * w₂ * (c₁ * w₁) := by group
  have hZ3 : ∀ c ∈ Z, c ^ 3 = 1 := by
    intro c hc
    have h := pow_card_eq_one' (G := Z) (x := ⟨c, hc⟩)
    rw [hZcard] at h
    exact congrArg Subtype.val h
  have hcube : ∀ w ∈ X, t * w * t⁻¹ = w⁻¹ → w ^ 3 = 1 := by
    intro w hwX hσ
    have h3 : w ^ 3 ∈ Z := by
      have := pow_three_mem_center hcard hncX ⟨w, hwX⟩
      exact ⟨_, this, rfl⟩
    have hfix : t * w ^ 3 * t⁻¹ = w ^ 3 := by
      have hc := Subgroup.mem_centralizer_singleton_iff.mp (hZC h3).2
      rw [← hc]
      group
    have hinv : t * w ^ 3 * t⁻¹ = (w ^ 3)⁻¹ := by
      rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hσ, inv_pow]
    have h6 : w ^ 6 = 1 := by
      rw [show w ^ 6 = w ^ 3 * w ^ 3 by group]
      calc w ^ 3 * w ^ 3 = w ^ 3 * (w ^ 3)⁻¹ := by rw [← hinv, hfix]
        _ = 1 := mul_inv_cancel _
    have h9 : w ^ 9 = 1 := by rw [show w ^ 9 = (w ^ 3) ^ 3 by group, hZ3 _ h3]
    calc w ^ 3 = w ^ 9 * (w ^ 6)⁻¹ := by group
      _ = 1 := by rw [h9, h6, inv_one, one_mul]
  set ζ := w₁ * w₂ * w₁⁻¹ * w₂⁻¹ with hζ
  have hζZ : ζ ∈ Z := by
    have := commutator_mem_center hcard hncX ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩
    exact ⟨_, this, rfl⟩
  have hζ1 : ζ ≠ 1 := by
    intro h
    apply hw
    calc w₁ * w₂ = ζ * (w₂ * w₁) := by rw [hζ]; group
      _ = w₂ * w₁ := by rw [h, one_mul]
  have hζ3 : ζ ^ 3 = 1 := hZ3 ζ hζZ
  have hZeq : Z = Subgroup.zpowers ζ := by
    have hle : Subgroup.zpowers ζ ≤ Z := (Subgroup.zpowers_le).mpr hζZ
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hZcard, Nat.card_zpowers]
    have : orderOf ζ ∣ 3 := orderOf_dvd_of_pow_eq_one hζ3
    rcases (Nat.dvd_prime Nat.prime_three).mp this with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hζ1
    · rw [h]
  obtain ⟨hζX, hζc⟩ := (hmemZ ζ).mp hζZ
  refine ⟨w₁, w₂, ζ, hw₁, hw₂, hζX, hζc, hζ1, hζ3, by rw [hζ]; group, hcube w₁ hw₁ hσ₁,
    hcube w₂ hw₂ hσ₂, fun x hx hxt => ?_, fun c hcX hc => ?_⟩
  · rw [← hZeq, hZeqC]
    exact ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hxt⟩
  · rw [← hZeq]
    exact (hmemZ c).mpr ⟨hcX, hc⟩

end CFSG.LargeExtraspecial.AS35QTh
