

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
public import Mathlib.GroupTheory.Nilpotent
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

namespace CFSG.HardMathSupport.Foote.SPLScalar

@[expose] def SingerConclusion {G : Type*} [Group G] (E : Subgroup G) : Prop :=
  ∃ c ∈ Subgroup.normalizer (E : Set G), (∀ a ∈ E, c ^ 4 * a * (c ^ 4)⁻¹ = a ^ 2) ∧
    ∀ k : ℕ, 0 < k → k < 4 → ∀ F : Subgroup G, F ≤ E → F.relIndex E = 3 →
      c ^ k ∉ Subgroup.normalizer (F : Set G)

theorem mem_normalizer_map_iff {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (S : Subgroup G) (c : H) :
    e.symm c ∈ Subgroup.normalizer (S : Set G) ↔
      c ∈ Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup H) : Set H) := by
  simp only [Subgroup.mem_set_normalizer_iff, SetLike.mem_coe, Subgroup.mem_map_equiv]
  constructor
  · intro h a
    have := h (e.symm a)
    simpa [map_mul, map_inv] using this
  · intro h a
    have := h (e a)
    simpa [map_mul, map_inv] using this

theorem singerConclusion_of_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (E : Subgroup G) (h : SingerConclusion (E.map e.toMonoidHom)) : SingerConclusion E := by
  obtain ⟨c', hc'N, h4, hk⟩ := h
  refine ⟨e.symm c', (mem_normalizer_map_iff e E c').2 hc'N, ?_, ?_⟩
  · intro a ha
    have := congrArg e.symm (h4 (e a) ⟨a, ha, rfl⟩)
    simpa using this
  · intro k hk0 hk4 F hF hrel hmem
    refine hk k hk0 hk4 (F.map e.toMonoidHom) (Subgroup.map_mono hF) ?_ ?_
    · rw [Subgroup.relIndex_map_map_of_injective _ _ e.injective]; exact hrel
    · have : e.symm (c' ^ k) ∈ Subgroup.normalizer (F : Set G) := by simpa using hmem
      exact (mem_normalizer_map_iff e F _).1 this


theorem zpow_emod_three {G : Type*} [Group G] (x : G) (hx3 : x ^ 3 = 1) (n : ℤ) :
    x ^ n = x ^ (n % 3) := by
  have h3 : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
  conv_lhs => rw [← Int.emod_add_mul_ediv n 3]
  rw [zpow_add, zpow_mul, h3, one_zpow, mul_one]

theorem zpow_eq_one_of_dvd {G : Type*} [Group G] (x : G) (hx3 : x ^ 3 = 1) (n : ℤ)
    (h : 3 ∣ n) : x ^ n = 1 := by
  rw [zpow_emod_three x hx3, Int.emod_eq_zero_of_dvd h, zpow_zero]

theorem three_dvd_of_pair {G : Type*} [Group G] (x y : G) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x) (a b : ℤ) (h : x ^ a * y ^ b = 1) :
    3 ∣ a ∧ 3 ∣ b := by
  have hyb : y ^ b = (x ^ a)⁻¹ := eq_inv_of_mul_eq_one_right h
  have hb : 3 ∣ b := by
    by_contra hb
    have hmem : y ^ b ∈ Subgroup.zpowers x := by
      rw [hyb]; exact Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _)
    rw [zpow_emod_three y hy3] at hmem
    have h2 : b % 3 = 1 ∨ b % 3 = 2 := by omega
    rcases h2 with h2 | h2
    · rw [h2, zpow_one] at hmem; exact hyx hmem
    · rw [h2] at hmem
      apply hyx
      have : y = (y ^ (2 : ℤ)) ^ (2 : ℤ) := by
        rw [← zpow_mul]
        have h4 := zpow_emod_three y hy3 4
        norm_num at h4
        simpa using h4.symm
      rw [this]; exact Subgroup.zpow_mem _ hmem _
  refine ⟨?_, hb⟩
  rw [zpow_eq_one_of_dvd y hy3 b hb, mul_one] at h
  by_contra ha
  rw [zpow_emod_three x hx3] at h
  have h2 : a % 3 = 1 ∨ a % 3 = 2 := by omega
  rcases h2 with h2 | h2
  · rw [h2, zpow_one] at h; exact hx1 h
  · rw [h2] at h
    apply hx1
    have h5 : x ^ ((2 : ℤ) + 1) = x ^ (2 : ℤ) * x ^ (1 : ℤ) := zpow_add x 2 1
    rw [h, one_mul, zpow_one] at h5
    rw [← h5]
    exact_mod_cast hx3

theorem pair_mul {G : Type*} [Group G] (x y : G) (hxy : x * y = y * x) (a b c d : ℤ) :
    x ^ a * y ^ b * (x ^ c * y ^ d) = x ^ (a + c) * y ^ (b + d) := by
  have hc : Commute x y := hxy
  rw [((hc.zpow_zpow c b).symm).mul_mul_mul_comm, zpow_add, zpow_add]

theorem pair_eq {G : Type*} [Group G] (x y : G) (hxy : x * y = y * x) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x) (a b a' b' : ℤ)
    (h : x ^ a * y ^ b = x ^ a' * y ^ b') : 3 ∣ a - a' ∧ 3 ∣ b - b' := by
  have h2 : x ^ (a + -a') * y ^ (b + -b') = 1 := by
    rw [← pair_mul x y hxy, h, pair_mul x y hxy]
    simp
  obtain ⟨h3, h4⟩ := three_dvd_of_pair x y hx3 hy3 hx1 hyx _ _ h2
  exact ⟨by omega, by omega⟩

theorem conj_pair {G : Type*} [Group G] (x y c : G) (hxy : x * y = y * x)
    (hcx : c * x * c⁻¹ = x * y⁻¹) (hcy : c * y * c⁻¹ = x * y) (i j : ℤ) :
    c * (x ^ i * y ^ j) * c⁻¹ = x ^ (i + j) * y ^ (j - i) := by
  have hc : Commute x y := hxy
  calc c * (x ^ i * y ^ j) * c⁻¹ = (c * x * c⁻¹) ^ i * (c * y * c⁻¹) ^ j := by
        rw [conj_zpow, conj_zpow]; group
    _ = (x * y⁻¹) ^ i * (x * y) ^ j := by rw [hcx, hcy]
    _ = x ^ i * y ^ (-i) * (x ^ j * y ^ j) := by
        rw [(hc.inv_right).mul_zpow, hc.mul_zpow, inv_zpow']
    _ = x ^ (i + j) * y ^ (j - i) := by
        rw [pair_mul x y hxy]; congr 2; ring

theorem conj_pow_succ {G : Type*} [Group G] (c a : G) (k : ℕ) :
    c ^ (k + 1) * a * (c ^ (k + 1))⁻¹ = c * (c ^ k * a * (c ^ k)⁻¹) * c⁻¹ := by
  rw [pow_succ']; group

section
variable {G : Type*} [Group G] (x y c : G) (hxy : x * y = y * x)
    (hcx : c * x * c⁻¹ = x * y⁻¹) (hcy : c * y * c⁻¹ = x * y) (i j : ℤ)
include hxy hcx hcy

theorem conj_pow_two : c ^ 2 * (x ^ i * y ^ j) * (c ^ 2) ⁻¹ = x ^ (2 * j) * y ^ (-2 * i) := by
  rw [show (2:ℕ) = 1 + 1 from rfl, conj_pow_succ, pow_one, conj_pair x y c hxy hcx hcy,
    conj_pair x y c hxy hcx hcy]
  congr 2 <;> ring

theorem conj_pow_three : c ^ 3 * (x ^ i * y ^ j) * (c ^ 3) ⁻¹ =
    x ^ (2 * j - 2 * i) * y ^ (-2 * i - 2 * j) := by
  rw [show (3:ℕ) = 2 + 1 from rfl, conj_pow_succ, conj_pow_two x y c hxy hcx hcy,
    conj_pair x y c hxy hcx hcy]
  congr 2
  ring

theorem conj_pow_four : c ^ 4 * (x ^ i * y ^ j) * (c ^ 4) ⁻¹ = x ^ (-4 * i) * y ^ (-4 * j) := by
  rw [show (4:ℕ) = 3 + 1 from rfl, conj_pow_succ, conj_pow_three x y c hxy hcx hcy,
    conj_pair x y c hxy hcx hcy]
  congr 2 <;> ring

end

theorem exists_pair_of_mem {G : Type*} [Group G] [Finite G] (E : Subgroup G)
    (hE9 : Nat.card E = 9) (x y : G) (hx : x ∈ E) (hy : y ∈ E) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x) :
    ∀ a ∈ E, ∃ i j : ℤ, a = x ^ i * y ^ j := by
  let f : Fin 3 × Fin 3 → E := fun p =>
    ⟨x ^ (p.1 : ℕ) * y ^ (p.2 : ℕ), mul_mem (pow_mem hx _) (pow_mem hy _)⟩
  have hinj : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h1 : x ^ (i : ℕ) * y ^ (j : ℕ) = x ^ (i' : ℕ) * y ^ (j' : ℕ) := congrArg Subtype.val h
    simp only [← zpow_natCast] at h1
    obtain ⟨h2, h3⟩ := pair_eq x y hxy hx3 hy3 hx1 hyx _ _ _ _ h1
    have := i.isLt; have := i'.isLt; have := j.isLt; have := j'.isLt
    ext <;> simp <;> omega
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by simp [hE9])
  intro a ha
  obtain ⟨⟨i, j⟩, hij⟩ := hbij.2 ⟨a, ha⟩
  refine ⟨(i : ℕ), (j : ℕ), ?_⟩
  have := congrArg Subtype.val hij
  simp only [f] at this
  rw [← this]
  simp [zpow_natCast]

theorem finite_check : ∀ I J N : ZMod 3, (I ≠ 0 ∨ J ≠ 0) →
    ¬ (I + J = I * N ∧ J - I = J * N) ∧ ¬ (2 * J = I * N ∧ -2 * I = J * N) ∧
    ¬ (2 * J - 2 * I = I * N ∧ -2 * I - 2 * J = J * N) := by decide

theorem zmod_of_dvd {a b : ℤ} (h : 3 ∣ a - b) : (a : ZMod 3) = b := by
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 h
  push_cast at this
  exact sub_eq_zero.mp this


theorem singerConclusion_of_action {G : Type*} [Group G] [Finite G] (E : Subgroup G)
    (hE9 : Nat.card E = 9) (x y c : G) (hx : x ∈ E) (hy : y ∈ E) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x)
    (hcx : c * x * c⁻¹ = x * y⁻¹) (hcy : c * y * c⁻¹ = x * y) : SingerConclusion E := by
  have hrep := exists_pair_of_mem E hE9 x y hx hy hx3 hy3 hxy hx1 hyx
  have hc : Commute x y := hxy
  have hfwd : ∀ a ∈ E, c * a * c⁻¹ ∈ E := by
    intro a ha
    obtain ⟨i, j, rfl⟩ := hrep a ha
    rw [conj_pair x y c hxy hcx hcy]
    exact mul_mem (Subgroup.zpow_mem _ hx _) (Subgroup.zpow_mem _ hy _)
  have hfwdk : ∀ k : ℕ, ∀ a ∈ E, c ^ k * a * (c ^ k)⁻¹ ∈ E := by
    intro k
    induction k with
    | zero => intro a ha; simpa using ha
    | succ k ih => intro a ha; rw [conj_pow_succ]; exact hfwd _ (ih a ha)
  have ha3 : ∀ a ∈ E, a ^ 3 = 1 := by
    intro a ha
    obtain ⟨i, j, rfl⟩ := hrep a ha
    have h1 : (x ^ i) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul]
      exact zpow_eq_one_of_dvd x hx3 _ ⟨i, by push_cast; ring⟩
    have h2 : (y ^ j) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul]
      exact zpow_eq_one_of_dvd y hy3 _ ⟨j, by push_cast; ring⟩
    rw [(hc.zpow_zpow i j).mul_pow, h1, h2, one_mul]
  have h4' : ∀ a ∈ E, c ^ 4 * a * (c ^ 4)⁻¹ = a ^ 2 := by
    intro a ha
    obtain ⟨i, j, rfl⟩ := hrep a ha
    rw [conj_pow_four x y c hxy hcx hcy, pow_two, pair_mul x y hxy,
      zpow_emod_three x hx3 (-4 * i), zpow_emod_three x hx3 (i + i),
      zpow_emod_three y hy3 (-4 * j), zpow_emod_three y hy3 (j + j)]
    have e1 : (-4 * i) % 3 = (i + i) % 3 := by omega
    have e2 : (-4 * j) % 3 = (j + j) % 3 := by omega
    rw [e1, e2]
  have hinvcl : ∀ a ∈ E, c⁻¹ * a * c ∈ E := by
    intro a ha
    have h := h4' (a ^ 2) (pow_mem ha 2)
    have h' : (a ^ 2) ^ 2 = a := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, ha3 a ha, one_mul]
    have : c⁻¹ * a * c = c ^ 3 * a ^ 2 * (c ^ 3)⁻¹ := by
      calc c⁻¹ * a * c = c⁻¹ * (c ^ 4 * a ^ 2 * (c ^ 4)⁻¹) * c := by rw [h, h']
        _ = c ^ 3 * a ^ 2 * (c ^ 3)⁻¹ := by group
    rw [this]
    exact hfwdk 3 _ (pow_mem ha 2)
  have hnorm : c ∈ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    simp only [SetLike.mem_coe]
    constructor
    · intro hh; exact hfwd h hh
    · intro hh
      have := hinvcl _ hh
      simpa [mul_assoc] using this
  refine ⟨c, hnorm, h4', ?_⟩
  intro k hk0 hk4 F hFE hrel hN
  have hFcard : Nat.card F = 3 := by
    have := Subgroup.relIndex_mul_card (H := F) (K := E)
    rw [inf_of_le_left hFE, hrel, hE9] at this
    omega
  have hF1 : F ≠ ⊥ := fun h => by rw [h] at hFcard; simp at hFcard
  obtain ⟨⟨e, heF⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hF1
  have hne : e ≠ 1 := fun h => he1 (Subtype.ext h)
  have heE : e ∈ E := hFE heF
  have he3 : e ^ 3 = 1 := ha3 e heE
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf e = 3 := orderOf_eq_prime he3 hne
  have hzF : Subgroup.zpowers e = F :=
    Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 heF)
      (by simp [Nat.card_zpowers, hord, hFcard])
  obtain ⟨i, j, rfl⟩ := hrep e heE
  have hnot : ¬ (3 ∣ i ∧ 3 ∣ j) := by
    rintro ⟨hi, hj⟩
    apply hne
    rw [zpow_eq_one_of_dvd x hx3 i hi, zpow_eq_one_of_dvd y hy3 j hj, one_mul]
  have hconj : c ^ k * (x ^ i * y ^ j) * (c ^ k)⁻¹ ∈ Subgroup.zpowers (x ^ i * y ^ j) := by
    rw [hzF]
    exact (Subgroup.mem_set_normalizer_iff.mp hN _).mp heF
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hconj
  have hpow : (x ^ i * y ^ j) ^ n = x ^ (i * n) * y ^ (j * n) := by
    rw [(hc.zpow_zpow i j).mul_zpow, ← zpow_mul, ← zpow_mul]
  have hcheck := finite_check (i : ZMod 3) (j : ZMod 3) (n : ZMod 3) (by
    by_contra hh
    push Not at hh
    apply hnot
    constructor
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd i 3).1 hh.1
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd j 3).1 hh.2)
  rw [hpow] at hn
  interval_cases k
  · rw [pow_one, conj_pair x y c hxy hcx hcy] at hn
    obtain ⟨d1, d2⟩ := pair_eq x y hxy hx3 hy3 hx1 hyx _ _ _ _ hn
    have a1 := zmod_of_dvd d1
    have a2 := zmod_of_dvd d2
    push_cast at a1 a2
    exact hcheck.1 ⟨a1.symm, a2.symm⟩
  · rw [conj_pow_two x y c hxy hcx hcy] at hn
    obtain ⟨d1, d2⟩ := pair_eq x y hxy hx3 hy3 hx1 hyx _ _ _ _ hn
    have a1 := zmod_of_dvd d1
    have a2 := zmod_of_dvd d2
    push_cast at a1 a2
    exact hcheck.2.1 ⟨a1.symm, a2.symm⟩
  · rw [conj_pow_three x y c hxy hcx hcy] at hn
    obtain ⟨d1, d2⟩ := pair_eq x y hxy hx3 hy3 hx1 hyx _ _ _ _ hn
    have a1 := zmod_of_dvd d1
    have a2 := zmod_of_dvd d2
    push_cast at a1 a2
    exact hcheck.2.2 ⟨a1.symm, a2.symm⟩

end CFSG.HardMathSupport.Foote.SPLScalar

