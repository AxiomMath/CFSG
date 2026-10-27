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

namespace CFSG.KC.Misc.HeisThree

variable {G : Type*} [Group G]

theorem cube_of_rel {u v w : G} (h : v * u = u * v * w) (hwu : Commute w u) (hwv : Commute w v) :
    (u * v) ^ 3 = u ^ 3 * v ^ 3 * w ^ 3 := by
  have h1 : v * u = u * (v * w) := by rw [h, mul_assoc]
  have h2 : ∀ x, v * (u * x) = u * (v * (w * x)) := fun x => by
    rw [← mul_assoc, h1]; simp only [mul_assoc]
  have h3 : w * u = u * w := hwu.eq
  have h4 : ∀ x, w * (u * x) = u * (w * x) := fun x => by rw [← mul_assoc, h3, mul_assoc]
  have h5 : w * v = v * w := hwv.eq
  have h6 : ∀ x, w * (v * x) = v * (w * x) := fun x => by rw [← mul_assoc, h5, mul_assoc]
  simp only [pow_three, mul_assoc, h1, h2, h3, h4, h5, h6]

section Heis

variable {a b c : G} (hc3 : c ^ 3 = 1) (hab : a * b = b * a * c) (hca : Commute c a)
  (hcb : Commute c b)

include hc3 hab hca hcb

theorem heis_ba : b * a = a * b * c ^ 2 := by
  have h : c * c ^ 2 = 1 := by rw [← pow_succ', hc3]
  rw [hab, mul_assoc, h, mul_one]

theorem heis_bpow_a (j : ℕ) : b ^ j * a = a * b ^ j * c ^ (2 * j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : 2 * (j + 1) = 2 + 2 * j := by ring
    calc b ^ (j + 1) * a = b * (b ^ j * a) := by rw [pow_succ', mul_assoc]
      _ = b * a * b ^ j * c ^ (2 * j) := by rw [ih]; simp only [mul_assoc]
      _ = a * b * (c ^ 2 * b ^ j) * c ^ (2 * j) := by
        rw [heis_ba hc3 hab hca hcb]; simp only [mul_assoc]
      _ = a * b ^ (j + 1) * c ^ (2 * (j + 1)) := by
        rw [(hcb.pow_pow 2 j).eq, e, pow_add c 2 (2 * j), pow_succ' b j]; simp only [mul_assoc]

theorem heis_bpow_apow (i j : ℕ) : b ^ j * a ^ i = a ^ i * b ^ j * c ^ (2 * i * j) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : 2 * (i + 1) * j = 2 * j + 2 * i * j := by ring
    calc b ^ j * a ^ (i + 1) = b ^ j * a ^ i * a := by rw [pow_succ, mul_assoc]
      _ = a ^ i * b ^ j * (c ^ (2 * i * j) * a) := by rw [ih]; simp only [mul_assoc]
      _ = a ^ i * (b ^ j * a) * c ^ (2 * i * j) := by
        rw [(hca.pow_left _).eq]; simp only [mul_assoc]
      _ = a ^ (i + 1) * b ^ j * c ^ (2 * (i + 1) * j) := by
        rw [heis_bpow_a hc3 hab hca hcb, e, pow_add c (2 * j) (2 * i * j), pow_succ a i]
        simp only [mul_assoc]

theorem heis_mul_a (i j k : ℕ) :
    a ^ i * b ^ j * c ^ k * a = a ^ (i + 1) * b ^ j * c ^ (2 * j + k) := by
  rw [mul_assoc, ((hca.pow_left k)).eq, ← mul_assoc, mul_assoc (a ^ i),
    heis_bpow_a hc3 hab hca hcb, pow_succ a i, pow_add c]
  simp only [mul_assoc]

theorem heis_mul_b (i j k : ℕ) :
    a ^ i * b ^ j * c ^ k * b = a ^ i * b ^ (j + 1) * c ^ k := by
  rw [mul_assoc, ((hcb.pow_left k)).eq, ← mul_assoc, mul_assoc (a ^ i), ← pow_succ]

theorem heis_cube (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (i j k : ℕ) :
    (a ^ i * b ^ j * c ^ k) ^ 3 = 1 := by
  have hcom : Commute (a ^ i * b ^ j) (c ^ k) :=
    (hca.pow_pow k i).symm.mul_left (hcb.pow_pow k j).symm
  rw [hcom.mul_pow, ← pow_mul, mul_comm k, pow_mul, hc3, one_pow, mul_one,
    cube_of_rel (heis_bpow_apow hc3 hab hca hcb i j) (hca.pow_pow _ i) (hcb.pow_pow _ j),
    ← pow_mul, ← pow_mul, ← pow_mul, mul_comm i, mul_comm j, mul_comm (2 * i * j), pow_mul,
    pow_mul, pow_mul, ha3, hb3, hc3, one_pow, one_pow, one_pow, mul_one, mul_one]

end Heis

theorem heis_pow_three {a b : G} (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (hca : (a⁻¹ * b⁻¹ * a * b) * a = a * (a⁻¹ * b⁻¹ * a * b))
    (hcb : (a⁻¹ * b⁻¹ * a * b) * b = b * (a⁻¹ * b⁻¹ * a * b)) (hc3 : (a⁻¹ * b⁻¹ * a * b) ^ 3 = 1) :
    ∀ x ∈ Subgroup.closure ({a, b} : Set G), x ^ 3 = 1 := by
  set c := a⁻¹ * b⁻¹ * a * b
  have hab : a * b = b * a * c := by simp only [c]; group
  have hca' : Commute c a := hca
  have hcb' : Commute c b := hcb
  have hstep : ∀ x : G, (∃ i j k : ℕ, x = a ^ i * b ^ j * c ^ k) → ∀ y ∈ ({a, b} : Set G),
      ∃ i j k : ℕ, x * y = a ^ i * b ^ j * c ^ k := by
    rintro x ⟨i, j, k, rfl⟩ y hy
    rcases hy with rfl | rfl
    · exact ⟨i + 1, j, 2 * j + k, heis_mul_a hc3 hab hca' hcb' i j k⟩
    · exact ⟨i, j + 1, k, heis_mul_b hc3 hab hca' hcb' i j k⟩
  have hinv : ∀ y ∈ ({a, b} : Set G), y⁻¹ = y * y := by
    intro y hy
    apply inv_eq_of_mul_eq_one_right
    rcases hy with rfl | rfl
    · rw [← pow_three]; exact ha3
    · rw [← pow_three]; exact hb3
  intro x hx
  obtain ⟨i, j, k, rfl⟩ : ∃ i j k : ℕ, x = a ^ i * b ^ j * c ^ k := by
    induction hx using Subgroup.closure_induction_right with
    | one => exact ⟨0, 0, 0, by simp⟩
    | mul_right x _ y hy ih => exact hstep x ih y hy
    | mul_inv_cancel x _ y hy ih =>
      rw [hinv y hy, ← mul_assoc]
      exact hstep _ (hstep x ih y hy) y hy
  exact heis_cube hc3 hab hca' hcb' ha3 hb3 i j k

theorem isPGroup_heis {a b : G} (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (hca : (a⁻¹ * b⁻¹ * a * b) * a = a * (a⁻¹ * b⁻¹ * a * b))
    (hcb : (a⁻¹ * b⁻¹ * a * b) * b = b * (a⁻¹ * b⁻¹ * a * b)) (hc3 : (a⁻¹ * b⁻¹ * a * b) ^ 3 = 1) :
    IsPGroup 3 (Subgroup.closure ({a, b} : Set G)) := by
  rintro ⟨x, hx⟩
  refine ⟨1, Subtype.ext ?_⟩
  rw [SubgroupClass.coe_pow, pow_one]
  exact heis_pow_three ha3 hb3 hca hcb hc3 x hx

theorem mem_of_nonabelian_sylow [Finite G] {p : ℕ} [hp : Fact p.Prime] {A P H : Subgroup G}
    (hPA : P ≤ A) (h4 : ¬ p ^ 4 ∣ Nat.card A) (hHA : H ≤ A) (hH : IsPGroup p H)
    (hnc : ∃ x ∈ H, ∃ y ∈ H, x * y ≠ y * x) {σ : G} (hσA : σ ∈ A) {n : ℕ} (hσ : σ ^ p ^ n = 1)
    (h9 : p ^ 2 ∣ Nat.card ↥(P ⊓ Subgroup.centralizer {σ})) : σ ∈ P := by
  by_contra hσP
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  obtain ⟨T₀, hT₀⟩ := Sylow.exists_subgroup_card_pow_prime p h9
  set T : Subgroup G := T₀.map (P ⊓ Subgroup.centralizer {σ}).subtype
  have hTcard : Nat.card T = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hT₀]
  have hTle : T ≤ P ⊓ Subgroup.centralizer {σ} := by
    rintro _ ⟨t, -, rfl⟩
    exact t.2
  set TA := T.subgroupOf A
  have hTA : Nat.card TA = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (hTle.trans (inf_le_left.trans hPA))).toEquiv, hTcard]
  set s : A := ⟨σ, hσA⟩
  have hsT : s ∈ Subgroup.centralizer (TA : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact Subgroup.mem_centralizer_singleton_iff.1 (hTle (Subgroup.mem_subgroupOf.1 ht)).2
  set Z := Subgroup.zpowers s
  have hZT : Z ≤ Subgroup.centralizer (TA : Set A) := Subgroup.zpowers_le.2 hsT
  have hs : s ^ p ^ n = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hσ)
  have hZp : IsPGroup p Z := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨n, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow]
    change (s ^ k) ^ p ^ n = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs, one_zpow]
  have hTp : IsPGroup p TA := IsPGroup.of_card hTA
  set R := Z ⊔ TA
  have hRp : IsPGroup p R :=
    IsPGroup.to_sup_of_normal_right' hZp hTp (hZT.trans (Subgroup.centralizer_le_normalizer _))
  have hTc : TA ≤ Subgroup.centralizer (TA : Set A) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact congrArg Subtype.val (IsPGroup.commutative_of_card_eq_prime_sq hTA ⟨u, hu⟩ ⟨t, ht⟩)
  have hZc : Z ≤ Subgroup.centralizer (Z : Set A) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact zpow_mul_comm s l k
  have hRc : R ≤ Subgroup.centralizer (R : Set A) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      exact sup_le hZc (Subgroup.le_centralizer_iff.2 hZT)
    · rw [Subgroup.le_centralizer_iff]
      exact sup_le hZT hTc
  have hsR : s ∈ R := Subgroup.mem_sup_left (Subgroup.mem_zpowers s)
  have hsTA : s ∉ TA := fun h => hσP (hTle (Subgroup.mem_subgroupOf.1 h)).1
  have hlt : TA < R := lt_of_le_of_ne le_sup_right (fun e => hsTA (e ▸ hsR))
  have hcardlt := Subgroup.card_lt_of_lt hlt
  obtain ⟨k, hk⟩ := hRp.exists_card_eq
  have hkA : p ^ k ∣ Nat.card A := hk ▸ Subgroup.card_subgroup_dvd_card R
  have hk3 : k = 3 := by
    rw [hTA, hk] at hcardlt
    have h2 : 2 < k := (Nat.pow_lt_pow_iff_right hp.out.one_lt).1 hcardlt
    by_contra hne
    exact h4 ((Nat.pow_dvd_pow p (by omega)).trans hkA)
  have hidx : ¬ p ∣ R.index := by
    rintro ⟨m, hm⟩
    have h := R.card_mul_index
    rw [hk, hk3, hm] at h
    exact h4 ⟨m, by rw [← h]; ring⟩
  set RS : Sylow p A := hRp.toSylow hidx
  have hRS : ∀ u v : (RS : Subgroup A), u * v = v * u := by
    intro u v
    have hu : (u : A) ∈ R := u.2
    have hv : (v : A) ∈ R := v.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact Subgroup.mem_centralizer_iff.1 (hRc hv) u hu
  have hHAp : IsPGroup p (H.subgroupOf A) := hH.of_equiv (Subgroup.subgroupOfEquivOfLe hHA).symm
  obtain ⟨Q, hQ⟩ := hHAp.exists_le_sylow
  have hQc : ∀ u v : (Q : Subgroup A), u * v = v * u := by
    intro u v
    have h := congrArg (Sylow.equiv RS Q) (hRS ((Sylow.equiv RS Q).symm u)
      ((Sylow.equiv RS Q).symm v))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h
  apply hxy
  have hx' : (⟨x, hHA hx⟩ : A) ∈ (Q : Subgroup A) := hQ (Subgroup.mem_subgroupOf.2 hx)
  have hy' : (⟨y, hHA hy⟩ : A) ∈ (Q : Subgroup A) := hQ (Subgroup.mem_subgroupOf.2 hy)
  exact congrArg (fun w : (Q : Subgroup A) => ((w : A) : G)) (hQc ⟨_, hx'⟩ ⟨_, hy'⟩)

end CFSG.KC.Misc.HeisThree
