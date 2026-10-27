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
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
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

namespace CFSG.ClassicalInvolution.Asc77.T3CII.T3V

section Fixed

theorem exists_fixed_of_pow_map {α : Type*} [Finite α] {p n : ℕ} [Fact p.Prime] {Ψ : Set α}
    (hcard : ¬ p ∣ Nat.card Ψ) {f : α → α} (hinj : Function.Injective f)
    (hmaps : ∀ x ∈ Ψ, f x ∈ Ψ) (hpow : ∀ x ∈ Ψ, f^[p ^ n] x = x) : ∃ x ∈ Ψ, f x = x := by
  classical
  let φ : ↥Ψ → ↥Ψ := fun y => ⟨f y, hmaps y y.2⟩
  have hφinj : Function.Injective φ := fun a b h => Subtype.ext (hinj (congrArg Subtype.val h))
  have hbij : Function.Bijective φ := Finite.injective_iff_bijective.mp hφinj
  let σ : Equiv.Perm ↥Ψ := Equiv.ofBijective φ hbij
  have h1 : ∀ (k : ℕ) (y : ↥Ψ), (((σ ^ k) y : ↥Ψ) : α) = f^[k] (y : α) := by
    intro k
    induction k with
    | zero => intro y; rfl
    | succ k ih =>
      intro y
      rw [pow_succ', Equiv.Perm.mul_apply, Function.iterate_succ_apply']
      show f (((σ ^ k) y : ↥Ψ) : α) = f (f^[k] (y : α))
      rw [ih]
  have hσ : σ ^ p ^ n = 1 := by
    ext y
    rw [h1]
    exact hpow y y.2
  have : Fintype ↥Ψ := Fintype.ofFinite ↥Ψ
  have hndvd : ¬ p ∣ Fintype.card ↥Ψ := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  obtain ⟨y, hy⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := p) (n := n) hndvd hσ
  refine ⟨y, y.2, ?_⟩
  have := congrArg Subtype.val hy
  exact this


variable {G : Type*} [Group G]

theorem conj_iterate (c : G) (k : ℕ) (y : G) :
    (fun x : G => c * x * c⁻¹)^[k] y = c ^ k * y * (c ^ k)⁻¹ := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, pow_succ, mul_inv_rev]
    group

theorem exists_fixed_conj_of_pow [Finite G] {p n : ℕ} [Fact p.Prime] {Ψ : Set G}
    (hcard : ¬ p ∣ Nat.card Ψ) {c : G} (hc : c ^ p ^ n = 1)
    (hstab : ∀ y ∈ Ψ, c * y * c⁻¹ ∈ Ψ) : ∃ y ∈ Ψ, c * y * c⁻¹ = y := by
  refine exists_fixed_of_pow_map (p := p) (n := n) hcard (f := fun x : G => c * x * c⁻¹) ?_
    hstab ?_
  · intro a b h
    simpa using h
  · intro y _
    rw [conj_iterate, hc]
    group

theorem exists_fixed_conj_of_odd [Finite G] {Ψ : Set G} (hΨ : Odd (Nat.card Ψ)) {a : G}
    (ha : a * a = 1) (hstab : ∀ y ∈ Ψ, a * y * a⁻¹ ∈ Ψ) : ∃ y ∈ Ψ, a * y * a⁻¹ = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine exists_fixed_conj_of_pow (p := 2) (n := 1) ?_ ?_ hstab
  · exact hΨ.not_two_dvd_nat
  · rw [pow_one, pow_two]; exact ha

theorem exists_pow_three_part (x : G) (hx : IsOfFinOrder x) :
    ∃ k e : ℕ, k % 3 = 1 ∧ (x ^ k) ^ 3 ^ e = 1 := by
  obtain ⟨e, m', hm', hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos_iff.mpr hx).ne'
    3 (by norm_num)
  refine ⟨m' ^ 2, e, ?_, ?_⟩
  · have h3 : m' % 3 = 1 ∨ m' % 3 = 2 := by omega
    rcases h3 with h | h <;> simp [pow_two, Nat.mul_mod, h]
  · rw [← pow_mul]
    have : m' ^ 2 * 3 ^ e = orderOf x * m' := by rw [hm]; ring
    rw [this, pow_mul, pow_orderOf_eq_one, one_pow]

end Fixed

section Cop

variable {G : Type*} [Group G]

theorem centralizes_of_odd_of_invol {W : Subgroup G} {q : G}
    (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hW2 : ∀ w ∈ W, ∃ k : ℕ, w ^ 2 ^ k = 1)
    (hq : q ∈ Subgroup.normalizer (W : Set G)) (hqodd : Odd (orderOf q))
    (hfix : ∀ w ∈ W, w * w = 1 → q * w * q⁻¹ = w) : ∀ w ∈ W, q * w * q⁻¹ = w := by
  have hconj : ∀ w ∈ W, q * w * q⁻¹ ∈ W := fun w hw => (Subgroup.mem_normalizer_iff.mp hq w).mp hw
  have key : ∀ (k : ℕ) (w : G), w ∈ W → w ^ 2 ^ k = 1 → q * w * q⁻¹ = w := by
    intro k
    induction k with
    | zero =>
      intro w _ hw
      rw [pow_zero, pow_one] at hw
      rw [hw]
      group
    | succ k ih =>
      intro w hw hwk
      have hw2 : w * w ∈ W := W.mul_mem hw hw
      have h2 : q * (w * w) * q⁻¹ = w * w := by
        refine ih (w * w) hw2 ?_
        rw [← pow_two, ← pow_mul, ← pow_succ']
        exact hwk
      set c : G := (q * w * q⁻¹) * w⁻¹ with hc
      have hcW : c ∈ W := W.mul_mem (hconj w hw) (W.inv_mem hw)
      have hc2 : c * c = 1 := by
        have hcomm : (q * w * q⁻¹) * w⁻¹ = w⁻¹ * (q * w * q⁻¹) :=
          hWab _ (hconj w hw) _ (W.inv_mem hw)
        calc c * c = (q * w * q⁻¹) * w⁻¹ * ((q * w * q⁻¹) * w⁻¹) := rfl
          _ = (q * w * q⁻¹) * (q * w * q⁻¹) * (w⁻¹ * w⁻¹) := by
            rw [mul_assoc, ← mul_assoc w⁻¹, ← hcomm]
            group
          _ = (q * (w * w) * q⁻¹) * (w * w)⁻¹ := by group
          _ = 1 := by rw [h2]; group
      have hqc : q * c * q⁻¹ = c := hfix c hcW hc2
      have hqw : q * w * q⁻¹ = c * w := by rw [hc]; group
      have hj : ∀ j : ℕ, q ^ j * w * (q ^ j)⁻¹ = c ^ j * w := by
        intro j
        induction j with
        | zero => simp
        | succ j ihj =>
          have h3 : q ^ (j + 1) * w * (q ^ (j + 1))⁻¹ = q * (q ^ j * w * (q ^ j)⁻¹) * q⁻¹ := by
            rw [pow_succ', mul_inv_rev]
            group
          rw [h3, ihj]
          have h4 : q * (c ^ j * w) * q⁻¹ = (q * c * q⁻¹) ^ j * (q * w * q⁻¹) := by
            have : q * c ^ j * q⁻¹ = (q * c * q⁻¹) ^ j := by
              rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_pow]
            calc q * (c ^ j * w) * q⁻¹ = (q * c ^ j * q⁻¹) * (q * w * q⁻¹) := by group
              _ = _ := by rw [this]
          rw [h4, hqc, hqw, pow_succ]
          group
      have hm := hj (orderOf q)
      rw [pow_orderOf_eq_one] at hm
      have hcm : c ^ orderOf q = 1 := by
        have : c ^ orderOf q * w = 1 * w * 1 := by
          calc c ^ orderOf q * w = 1 * w * (1 : G)⁻¹ := hm.symm
            _ = 1 * w * 1 := by simp
        simpa using this
      obtain ⟨m, hm'⟩ := hqodd
      have hc1 : c = 1 := by
        have h5 : c ^ orderOf q = c := by
          rw [hm', pow_succ, pow_mul, pow_two, hc2, one_pow, one_mul]
        rw [← h5]
        exact hcm
      rw [hqw, hc1, one_mul]
  intro w hw
  obtain ⟨k, hk⟩ := hW2 w hw
  exact key k w hw hk

end Cop

section Dihedral

theorem dihedral6_pow_six (a : DihedralGroup 6) : a ^ 6 = 1 := by
  revert a
  decide

theorem dihedral6_pow_three_of_odd {a : DihedralGroup 6} (ha : Odd (orderOf a)) : a ^ 3 = 1 := by
  have h6 : orderOf a ∣ 6 := orderOf_dvd_of_pow_eq_one (dihedral6_pow_six a)
  have h3 : orderOf a ∣ 3 := by
    have : Nat.Coprime (orderOf a) 2 := ha.coprime_two_right
    have h6' : orderOf a ∣ 3 * 2 := h6
    exact this.dvd_of_dvd_mul_right h6'
  exact orderOf_dvd_iff_pow_eq_one.mp h3

theorem dihedral6_eq_of_odd {a b : DihedralGroup 6} (ha : Odd (orderOf a))
    (hb : Odd (orderOf b)) (h : (a⁻¹ * b) * (a⁻¹ * b) = 1) : a = b := by
  have ha3 := dihedral6_pow_three_of_odd ha
  have hb3 := dihedral6_pow_three_of_odd hb
  clear ha hb
  revert a b
  decide

end Dihedral

section Lift

variable {H : Type*} [Group H] [Finite H]

theorem exists_mod_fixed (W' Q' : Subgroup H) [W'.Normal] {x s : H}
    (hQ : Odd (Nat.card Q')) (hQW : ∀ q ∈ Q', q ∈ W' → q = 1)
    (hQx : ∀ q ∈ Q', x * q * x⁻¹ ∈ Q') (hQs : ∀ q ∈ Q', s * q * s⁻¹ ∈ Q')
    (hss : s * s = 1) (hsx : ∃ q₂ ∈ Q', ∃ w₂ ∈ W', s * x * s⁻¹ = x * q₂ * w₂) :
    ∃ q ∈ Q', ∃ w ∈ W', s * (q * x) * s⁻¹ = (q * x) * w := by
  obtain ⟨q₂, hq₂, w₂, hw₂, hsxe⟩ := hsx
  let π : H →* H ⧸ W' := QuotientGroup.mk' W'
  set Ψ : Set (H ⧸ W') := (fun q : H => π (q * x)) '' (Q' : Set H) with hΨ
  have hinj : Set.InjOn (fun q : H => π (q * x)) (Q' : Set H) := by
    intro q₁ h₁ q₂ h₂ h
    simp only [π, QuotientGroup.mk'_apply] at h
    have h3 := QuotientGroup.eq.mp h
    have h4 : q₁⁻¹ * q₂ ∈ W' := by
      have := Subgroup.Normal.conj_mem inferInstance _ h3 x
      simpa [mul_assoc] using this
    have h5 : q₁⁻¹ * q₂ ∈ Q' := Q'.mul_mem (Q'.inv_mem h₁) h₂
    exact inv_mul_eq_one.mp (hQW _ h5 h4)
  have hcard : Nat.card Ψ = Nat.card Q' := by
    rw [hΨ, Nat.card_image_of_injOn hinj]
    rfl
  have hss' : π s * π s = 1 := by rw [← map_mul, hss, map_one]
  have hstab : ∀ y ∈ Ψ, π s * y * (π s)⁻¹ ∈ Ψ := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨(s * q * s⁻¹) * (x * q₂ * x⁻¹), Q'.mul_mem (hQs q hq) (hQx q₂ hq₂), ?_⟩
    show π ((s * q * s⁻¹) * (x * q₂ * x⁻¹) * x) = π s * π (q * x) * (π s)⁻¹
    have e : s * (q * x) * s⁻¹ = (s * q * s⁻¹) * (x * q₂ * x⁻¹) * x * w₂ := by
      calc s * (q * x) * s⁻¹ = (s * q * s⁻¹) * (s * x * s⁻¹) := by group
        _ = (s * q * s⁻¹) * (x * q₂ * w₂) := by rw [hsxe]
        _ = _ := by group
    have hw : π w₂ = 1 := (QuotientGroup.eq_one_iff w₂).mpr hw₂
    have h1 : π s * π (q * x) * (π s)⁻¹ = π (s * (q * x) * s⁻¹) := by simp [map_mul, map_inv]
    rw [h1, e]
    simp only [map_mul, hw, mul_one]
  obtain ⟨_, ⟨q, hq, rfl⟩, hfix⟩ := T3V.exists_fixed_conj_of_odd (G := H ⧸ W') (Ψ := Ψ)
    (by rw [hcard]; exact hQ) hss' hstab
  refine ⟨q, hq, (q * x)⁻¹ * (s * (q * x) * s⁻¹), ?_, by group⟩
  have : π (s * (q * x) * s⁻¹) = π (q * x) := by
    simpa [map_mul, map_inv] using hfix
  exact (QuotientGroup.eq.mp this.symm)

end Lift

section Cycle

variable {G : Type*} [Group G]

theorem pow_three_comm {x z t : G} (hz2 : z * z = 1) (hzt : z * t = t * z)
    (hxz : x * z * x⁻¹ = z * t) (hxt : x * t * x⁻¹ = z) :
    x ^ 3 * z * (x ^ 3)⁻¹ = z ∧ x ^ 3 * t * (x ^ 3)⁻¹ = t := by
  have hxzt : x * (z * t) * x⁻¹ = t := by
    have : x * (z * t) * x⁻¹ = (x * z * x⁻¹) * (x * t * x⁻¹) := by group
    rw [this, hxz, hxt]
    calc z * t * z = z * (t * z) := by rw [mul_assoc]
      _ = z * (z * t) := by rw [← hzt]
      _ = (z * z) * t := by rw [mul_assoc]
      _ = t := by rw [hz2, one_mul]
  rw [pow_three']
  constructor
  · calc x * x * x * z * (x * x * x)⁻¹ = x * (x * (x * z * x⁻¹) * x⁻¹) * x⁻¹ := by group
      _ = z := by rw [hxz, hxzt, hxt]
  · calc x * x * x * t * (x * x * x)⁻¹ = x * (x * (x * t * x⁻¹) * x⁻¹) * x⁻¹ := by group
      _ = t := by rw [hxt, hxz, hxzt]

theorem conj_pow_eq_of_comm {c a : G} (h : c * a * c⁻¹ = a) (m : ℕ) :
    c ^ m * a * (c ^ m)⁻¹ = a := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc c ^ (m + 1) * a * (c ^ (m + 1))⁻¹ = c * (c ^ m * a * (c ^ m)⁻¹) * c⁻¹ := by
          rw [pow_succ', mul_inv_rev]; group
      _ = a := by rw [ih, h]

theorem pow_act_of_mod {x z t : G} (hz2 : z * z = 1) (hzt : z * t = t * z)
    (hxz : x * z * x⁻¹ = z * t) (hxt : x * t * x⁻¹ = z) {k : ℕ} (hk : k % 3 = 1) :
    x ^ k * z * (x ^ k)⁻¹ = z * t ∧ x ^ k * t * (x ^ k)⁻¹ = z := by
  obtain ⟨hcz, hct⟩ := pow_three_comm hz2 hzt hxz hxt
  have hcz' : ∀ m : ℕ, (x ^ 3) ^ m * z * ((x ^ 3) ^ m)⁻¹ = z := fun m => conj_pow_eq_of_comm hcz m
  have hct' : ∀ m : ℕ, (x ^ 3) ^ m * t * ((x ^ 3) ^ m)⁻¹ = t := fun m => conj_pow_eq_of_comm hct m
  have hk' : k = 3 * (k / 3) + 1 := by omega
  have hxk : x ^ k = (x ^ 3) ^ (k / 3) * x := by
    rw [← pow_mul, ← pow_succ]
    rw [hk']
    congr 1
    omega
  have hzt' : ∀ m : ℕ, (x ^ 3) ^ m * (z * t) * ((x ^ 3) ^ m)⁻¹ = z * t := by
    intro m
    have : (x ^ 3) ^ m * (z * t) * ((x ^ 3) ^ m)⁻¹ =
        ((x ^ 3) ^ m * z * ((x ^ 3) ^ m)⁻¹) * ((x ^ 3) ^ m * t * ((x ^ 3) ^ m)⁻¹) := by group
    rw [this, hcz', hct']
  constructor
  · rw [hxk]
    calc (x ^ 3) ^ (k / 3) * x * z * ((x ^ 3) ^ (k / 3) * x)⁻¹
        = (x ^ 3) ^ (k / 3) * (x * z * x⁻¹) * ((x ^ 3) ^ (k / 3))⁻¹ := by group
      _ = z * t := by rw [hxz, hzt']
  · rw [hxk]
    calc (x ^ 3) ^ (k / 3) * x * t * ((x ^ 3) ^ (k / 3) * x)⁻¹
        = (x ^ 3) ^ (k / 3) * (x * t * x⁻¹) * ((x ^ 3) ^ (k / 3))⁻¹ := by group
      _ = z := by rw [hxt, hcz']

theorem pow_mul_mem {W : Subgroup G} {x w : G} (hx : x ∈ Subgroup.normalizer (W : Set G))
    (hw : w ∈ W) (k : ℕ) : ∃ w' ∈ W, (x * w) ^ k = x ^ k * w' := by
  induction k with
  | zero => exact ⟨1, W.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨w', hw', h⟩ := ih
    have hxi : x⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ hx
    have : x⁻¹ * w' * x⁻¹⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hxi w').mp hw'
    refine ⟨(x⁻¹ * w' * x) * w, W.mul_mem (by simpa using this) hw, ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem mem_normalizer_centralizer {W : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (W : Set G), ∀ c ∈ Subgroup.centralizer (W : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (W : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro w hw
    have hgi : g⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ hg
    have h1 : g⁻¹ * w * g ∈ W := by simpa using (Subgroup.mem_normalizer_iff.mp hgi w).mp hw
    have h2 := hc _ h1
    calc w * (g * c * g⁻¹) = g * ((g⁻¹ * w * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * w * g)) * g⁻¹ := by rw [h2]
      _ = (g * c * g⁻¹) * w := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    exact key g hg c hc
  · intro hc
    have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hc
    simpa [mul_assoc] using this

end Cycle

section Closure

variable {G : Type*} [Group G]

theorem conj_eq_of_mem_closure {s : G} {T : Set G} (h : ∀ a ∈ T, s * a * s⁻¹ = a) :
    ∀ c ∈ Subgroup.closure T, s * c * s⁻¹ = c := by
  intro c hc
  have hle : Subgroup.closure T ≤ Subgroup.centralizer ({s} : Set G) := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have : s * a = a * s := by
      calc s * a = (s * a * s⁻¹) * s := by group
        _ = a * s := by rw [h a ha]
    exact this.symm
  have := Subgroup.mem_centralizer_singleton_iff.mp (hle hc)
  calc s * c * s⁻¹ = c * s * s⁻¹ := by rw [this]
    _ = c := by group

theorem mem_normalizer_of_conj_eq {s : G} {Z : Subgroup G} (h : ∀ c ∈ Z, s * c * s⁻¹ = c) :
    s ∈ Subgroup.normalizer (Z : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [h c hc]
    exact hc
  · intro hc
    have h1 := h _ hc
    have h2 : c = s * c * s⁻¹ := by
      have h3 : s⁻¹ * (s * c * s⁻¹) * s = c := by group
      have h4 : s⁻¹ * (s * c * s⁻¹) * s = s * c * s⁻¹ := by
        have h5 : s * (s * c * s⁻¹) = (s * c * s⁻¹) * s := by
          calc s * (s * c * s⁻¹) = (s * (s * c * s⁻¹) * s⁻¹) * s := by group
            _ = (s * c * s⁻¹) * s := by rw [h1]
        calc s⁻¹ * (s * c * s⁻¹) * s = s⁻¹ * ((s * c * s⁻¹) * s) := by group
          _ = s⁻¹ * (s * (s * c * s⁻¹)) := by rw [h5]
          _ = s * c * s⁻¹ := by group
      exact h3.symm.trans h4
    rw [h2]
    exact hc

end Closure

end CFSG.ClassicalInvolution.Asc77.T3CII.T3V
