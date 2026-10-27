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
public import Mathlib.Data.Int.Star
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

public section

namespace CFSG.Holt.H78

open Subgroup

namespace L16

section Arith

theorem not_dvd_two_pow_sub_one_and_add_one {N k g : ℕ}
    (hk : (k = 2 ^ N - 1 ∧ 3 ≤ N) ∨ (3 * k = 2 ^ N - 1 ∧ 6 ≤ N)) (hg1 : 1 ≤ g) (hgN : g < N) :
    ¬ k ∣ 2 ^ g - 1 ∧ ¬ k ∣ 2 ^ g + 1 := by
  have h2g : 2 ≤ 2 ^ g := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg1
  rcases hk with ⟨rfl, hN⟩ | ⟨hk, hN⟩
  ·
    obtain ⟨M, hM⟩ : ∃ M, 2 ^ N = 2 * M ∧ 2 ^ g ≤ M ∧ 4 ≤ M := by
      refine ⟨2 ^ (N - 1), ?_, Nat.pow_le_pow_right (by norm_num) (by omega), ?_⟩
      · rw [← pow_succ']; congr 1; omega
      · calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (N - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := Nat.le_of_dvd (by omega) h; omega
    · have := Nat.le_of_dvd (by omega) h; omega
  ·
    obtain ⟨M, hM4, hM16⟩ : ∃ M, 2 ^ N = 4 * M ∧ 16 ≤ M := by
      refine ⟨2 ^ (N - 2), ?_, ?_⟩
      · rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
      · calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ (N - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    by_cases hg : g ≤ N - 2
    · have hgM : 2 ^ g ≤ M := by
        calc 2 ^ g ≤ 2 ^ (N - 2) := Nat.pow_le_pow_right (by norm_num) hg
          _ = M := by
            have h4 : 2 ^ N = 4 * 2 ^ (N - 2) := by
              rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
            omega
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have := Nat.le_of_dvd (by omega) h; omega
      · have := Nat.le_of_dvd (by omega) h; omega
    · have hgeq : 2 ^ g = 2 * M := by
        have h4 : 2 ^ N = 2 * 2 ^ g := by rw [← pow_succ']; congr 1; omega
        omega
      refine ⟨fun h => ?_, fun h => ?_⟩
      ·
        have h1 : k ∣ 2 * (2 ^ g - 1) := Dvd.dvd.mul_left h 2
        have h3 : k ∣ 3 * k := Dvd.intro_left 3 rfl
        have : k ∣ 3 * k - 2 * (2 ^ g - 1) := Nat.dvd_sub h3 h1
        rw [show 3 * k - 2 * (2 ^ g - 1) = 1 by omega] at this
        have := Nat.le_of_dvd (by norm_num) this; omega
      ·
        have h1 : k ∣ 2 * (2 ^ g + 1) := Dvd.dvd.mul_left h 2
        have h3 : k ∣ 3 * k := Dvd.intro_left 3 rfl
        have : k ∣ 2 * (2 ^ g + 1) - 3 * k := Nat.dvd_sub h1 h3
        rw [show 2 * (2 ^ g + 1) - 3 * k = 3 by omega] at this
        have := Nat.le_of_dvd (by norm_num) this; omega

theorem exists_natAbs_eq_two_pow_of_sq {W : ℤ} {m : ℕ} (h : W ^ 2 = 2 ^ m) :
    ∃ h' : ℕ, W.natAbs = 2 ^ h' ∧ m = 2 * h' := by
  have hn : W.natAbs ^ 2 = 2 ^ m := by
    have := congrArg Int.natAbs h
    rwa [Int.natAbs_pow, Int.natAbs_pow] at this
  have hdvd : W.natAbs ∣ 2 ^ m := hn ▸ Dvd.intro_left _ (sq _).symm
  obtain ⟨h', -, hh'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  refine ⟨h', hh', ?_⟩
  rw [hh', ← pow_mul] at hn
  exact (Nat.pow_right_injective le_rfl hn).symm.trans (mul_comm _ _)

theorem eq_zero_of_sq_eq_two_pow {N a r b k : ℕ}
    (hk : (k = 2 ^ N - 1 ∧ 3 ≤ N) ∨ (3 * k = 2 ^ N - 1 ∧ 6 ≤ N)) (hkb : k ∣ b)
    (hb : b < 2 ^ (N + a)) (har : a ≤ r)
    (hsq : ((2 : ℤ) ^ (N + a) - 2 * b) ^ 2 = 2 ^ (N + a + r)) : b = 0 := by
  have hN : 3 ≤ N := by rcases hk with h | h <;> omega
  obtain ⟨h, hW, hh⟩ := exists_natAbs_eq_two_pow_of_sq hsq
  by_contra hb0
  set W : ℤ := (2 : ℤ) ^ (N + a) - 2 * b with hWdef
  have hpowpos : (0 : ℤ) < 2 ^ (N + a) := by positivity
  have hlt : h < N + a := by
    have h1 : W < 2 ^ (N + a) := by
      have : (1 : ℤ) ≤ b := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hb0
      omega
    have h2 : -(2 ^ (N + a) : ℤ) < W := by
      have : (b : ℤ) < 2 ^ (N + a) := by exact_mod_cast hb
      omega
    have h3 : (W.natAbs : ℤ) < 2 ^ (N + a) := by
      rcases Int.natAbs_eq W with h4 | h4 <;> omega
    have h5 : 2 ^ h < 2 ^ (N + a) := by
      rw [← hW]; exact_mod_cast h3
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h5
  have hkN : (k : ℤ) ∣ 2 ^ N - 1 := by
    have : k ∣ 2 ^ N - 1 := by
      rcases hk with ⟨rfl, -⟩ | ⟨hk, -⟩
      · exact dvd_rfl
      · exact hk ▸ Dvd.intro_left 3 rfl
    have h1 : (1 : ℕ) ≤ 2 ^ N := Nat.one_le_two_pow
    have h2 := Int.natCast_dvd_natCast.2 this
    rw [Nat.cast_sub h1] at h2
    simpa using h2
  have hmod : (k : ℤ) ∣ W - 2 ^ a := by
    have : W - 2 ^ a = 2 ^ a * (2 ^ N - 1) - 2 * b := by
      rw [hWdef, pow_add]; ring
    rw [this]
    exact dvd_sub (dvd_mul_of_dvd_right hkN _) (dvd_mul_of_dvd_right (by exact_mod_cast hkb) _)
  obtain ⟨g, rfl⟩ : ∃ g, h = a + g := ⟨h - a, by omega⟩
  have hg1 : 1 ≤ g := by omega
  have hgN : g < N := by omega
  have hcop : IsCoprime (k : ℤ) (2 ^ a) := by
    have hkodd : Odd k := by
      have h1 : 1 ≤ 2 ^ N := Nat.one_le_two_pow
      have hodd : Odd (2 ^ N - 1) := by
        rcases Nat.even_or_odd (2 ^ N - 1) with he | ho
        · exfalso
          have : Even (2 ^ N) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
          rcases he with ⟨x, hx⟩; rcases this with ⟨y, hy⟩; omega
        · exact ho
      rcases hk with ⟨rfl, -⟩ | ⟨hk, -⟩
      · exact hodd
      · rw [← hk] at hodd; exact (Nat.odd_mul.1 hodd).2
    have : IsCoprime (k : ℤ) 2 := by
      rcases hkodd with ⟨m, rfl⟩
      exact ⟨1, -m, by push_cast; ring⟩
    exact this.pow_right
  have hcases : (k : ℤ) ∣ 2 ^ g - 1 ∨ (k : ℤ) ∣ 2 ^ g + 1 := by
    rcases Int.natAbs_eq W with h4 | h4
    · left
      have : W - 2 ^ a = 2 ^ a * (2 ^ g - 1) := by
        rw [h4, hW]; push_cast; rw [pow_add]; ring
      rw [this] at hmod
      exact hcop.dvd_of_dvd_mul_left hmod
    · right
      have : W - 2 ^ a = -(2 ^ a * (2 ^ g + 1)) := by
        rw [h4, hW]; push_cast; rw [pow_add]; ring
      rw [this, dvd_neg] at hmod
      exact hcop.dvd_of_dvd_mul_left hmod
  have hnot := not_dvd_two_pow_sub_one_and_add_one hk hg1 hgN
  have h1 : (1 : ℕ) ≤ 2 ^ g := Nat.one_le_two_pow
  rcases hcases with h5 | h5
  · apply hnot.1
    exact_mod_cast (show ((k : ℤ) ∣ ((2 ^ g - 1 : ℕ) : ℤ)) by push_cast [Nat.cast_sub h1]; exact h5)
  · apply hnot.2
    exact_mod_cast h5

end Arith

section FreeAction

theorem natCard_dvd_natCard_of_free {G X : Type*} [Group G] [Finite G] [MulAction G X]
    [Finite X] (hfree : ∀ (g : G) (x : X), g • x = x → g = 1) : Nat.card G ∣ Nat.card X := by
  classical
  have := Fintype.ofFinite G
  have := Fintype.ofFinite X
  have := Fintype.ofFinite (Quotient (MulAction.orbitRel G X))
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
  have hsum : ∑ g : G, Fintype.card (MulAction.fixedBy X g) = Fintype.card X := by
    rw [Finset.sum_eq_single (1 : G)]
    · rw [Fintype.card_congr (Equiv.subtypeUnivEquiv (fun x => MulAction.mem_fixedBy.2
        (one_smul G x)))]
    · intro g _ hg
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun x => hg (hfree g x x.2)⟩
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsum] at hB
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hB]
  exact Dvd.intro_left _ rfl

theorem dvd_natCard_of_perm {X : Type*} [Finite X] (σ : Equiv.Perm X) {k : ℕ} (hk : σ ^ k = 1)
    (hfree : ∀ (x : X) (j : ℕ), (σ ^ j) x = x → k ∣ j) : k ∣ Nat.card X := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · rw [Nat.card_of_isEmpty]; exact dvd_zero k
  have hord : orderOf σ = k := by
    apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hk)
    exact hfree x₀ _ (by rw [pow_orderOf_eq_one]; rfl)
  have hfreeG : ∀ (g : Subgroup.zpowers σ) (x : X), g • x = x → g = 1 := by
    rintro ⟨g, hg⟩ x hgx
    obtain ⟨m, rfl⟩ := ((isOfFinOrder_of_finite σ).mem_powers_iff_mem_zpowers).2 hg
    have hkm : k ∣ m := hfree x m hgx
    apply Subtype.ext
    obtain ⟨c, rfl⟩ := hkm
    simp [pow_mul, hk]
  have := natCard_dvd_natCard_of_free hfreeG
  rwa [Nat.card_zpowers, hord] at this

end FreeAction

section AutComm

variable {S : Type*} [Group S] (φ : MulAut S)

@[expose] def autComm (A : Subgroup S) : Subgroup S :=
  Subgroup.closure ((fun a => a⁻¹ * φ a) '' (A : Set S))

variable {φ}

theorem twist_mem_autComm {A : Subgroup S} {a : S} (ha : a ∈ A) : a⁻¹ * φ a ∈ autComm φ A :=
  Subgroup.subset_closure ⟨a, ha, rfl⟩

theorem twist_mul (a b : S) :
    (a * b)⁻¹ * φ (a * b) = b⁻¹ * (a⁻¹ * φ a) * b * (b⁻¹ * φ b) := by
  rw [map_mul]; group

theorem conj_mem_autComm {A : Subgroup S} {a : S} (ha : a ∈ A) {x : S}
    (hx : x ∈ autComm φ A) : a * x * a⁻¹ ∈ autComm φ A := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, rfl⟩ := hy
    have : a * (b⁻¹ * φ b) * a⁻¹ =
        ((b * a⁻¹)⁻¹ * φ (b * a⁻¹)) * (a⁻¹⁻¹ * φ a⁻¹)⁻¹ := by
      rw [map_mul, map_inv]; group
    rw [this]
    exact mul_mem (twist_mem_autComm (mul_mem hb (inv_mem ha)))
      (inv_mem (twist_mem_autComm (inv_mem ha)))
  | one => simp
  | mul x y _ _ hx hy =>
    have : a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
    rw [this]; exact mul_mem hx hy
  | inv x _ hx =>
    have : a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
    rw [this]; exact inv_mem hx

theorem map_mem_autComm {A : Subgroup S} (hA : ∀ a ∈ A, φ a ∈ A) {x : S}
    (hx : x ∈ autComm φ A) : φ x ∈ autComm φ A := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, rfl⟩ := hy
    rw [map_mul, map_inv]
    exact twist_mem_autComm (hA b hb)
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

theorem autComm_le {A : Subgroup S} (hA : ∀ a ∈ A, φ a ∈ A) : autComm φ A ≤ A := by
  rw [autComm, Subgroup.closure_le]
  rintro _ ⟨a, ha, rfl⟩
  exact mul_mem (inv_mem ha) (hA a ha)

theorem autComm_le_of {A T V : Subgroup S} (hTA : T ≤ A)
    (hVn : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ ∈ V) (hφV : ∀ v ∈ V, φ v ∈ V)
    (hAVT : ∀ a ∈ A, ∃ v ∈ V, ∃ t ∈ T, a = v * t) (hTV : ∀ t ∈ T, t⁻¹ * φ t ∈ V) :
    autComm φ A ≤ V := by
  rw [autComm, Subgroup.closure_le]
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨v, hv, t, ht, rfl⟩ := hAVT a ha
  change (v * t)⁻¹ * φ (v * t) ∈ V
  rw [twist_mul]
  refine mul_mem ?_ (hTV t ht)
  have := hVn t⁻¹ (inv_mem (hTA ht)) _ (mul_mem (inv_mem hv) (hφV v hv))
  simpa using this

end AutComm

section SettingDef

variable {S : Type*} [Group S]

theorem comm_mem_of_sq_mem {A X : Subgroup S} (hn : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X)
    (hsq : ∀ a ∈ A, a ^ 2 ∈ X) {a b : S} (ha : a ∈ A) (hb : b ∈ A) :
    a * b * a⁻¹ * b⁻¹ ∈ X := by
  have h1 := hsq _ (mul_mem ha hb)
  have h2 := hsq a ha
  have h3 := hsq b hb
  rw [pow_two] at h1 h2 h3
  have e : a * b * a⁻¹ * b⁻¹ = (a * b * (a * b)) * (b⁻¹ * (a * a)⁻¹ * b⁻¹⁻¹) * (b * b)⁻¹ := by
    group
  rw [e]
  exact mul_mem (mul_mem h1 (hn _ (inv_mem hb) _ (inv_mem h2))) (inv_mem h3)

structure Setting (φ : MulAut S) (A T R : Subgroup S) (N : ℕ) : Prop where
  pgroup : IsPGroup 2 S
  le_TA : T ≤ A
  le_RT : R ≤ T
  normT : ∀ a ∈ A, ∀ t ∈ T, a * t * a⁻¹ ∈ T
  normR : ∀ a ∈ A, ∀ r ∈ R, a * r * a⁻¹ ∈ R
  mapA : ∀ a ∈ A, φ a ∈ A
  mapR : ∀ r ∈ R, φ r ∈ R
  trivT : ∀ t ∈ T, t⁻¹ * φ t ∈ R
  sq : ∀ a ∈ A, a ^ 2 ∈ T
  index : T.relIndex A = 2 ^ N
  three_le : 3 ≤ N
  semi : ∀ (j : ℕ), ∀ a ∈ A, a⁻¹ * (φ ^ j) a ∈ T → a ∈ T ∨ φ ^ j = 1
  order : orderOf φ = 2 ^ N - 1 ∨ (3 * orderOf φ = 2 ^ N - 1 ∧ 6 ≤ N)

namespace Setting

variable {φ : MulAut S} {A T R : Subgroup S} {N : ℕ} (h : Setting φ A T R N)
include h

theorem comm_mem {a b : S} (ha : a ∈ A) (hb : b ∈ A) : a * b * a⁻¹ * b⁻¹ ∈ T :=
  comm_mem_of_sq_mem h.normT h.sq ha hb

theorem order' : (orderOf φ = 2 ^ N - 1 ∧ 3 ≤ N) ∨ (3 * orderOf φ = 2 ^ N - 1 ∧ 6 ≤ N) :=
  h.order.imp (fun h' => ⟨h', h.three_le⟩) id

theorem seven_le_orderOf : 7 ≤ orderOf φ := by
  have h8 : 8 ≤ 2 ^ N := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) h.three_le
  rcases h.order with h1 | ⟨h1, h6⟩
  · omega
  · have : 64 ≤ 2 ^ N := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) h6
    omega

theorem ne_one : φ ≠ 1 := by
  intro h1
  have := h.seven_le_orderOf
  rw [h1, orderOf_one] at this
  omega

theorem twist_mem_iff {a : S} (ha : a ∈ A) : a⁻¹ * φ a ∈ T ↔ a ∈ T := by
  refine ⟨fun h1 => ?_, fun h1 => h.le_RT (h.trivT a h1)⟩
  have := h.semi 1 a ha (by simpa using h1)
  exact this.resolve_right (by simpa using h.ne_one)

variable [Finite S]

theorem exists_twist {B : Subgroup S} (hBA : B ≤ A)
    (hφB : ∀ b ∈ B, φ b ∈ B) {b : S} (hb : b ∈ B) : ∃ w ∈ B, b⁻¹ * (w⁻¹ * φ w) ∈ T := by
  let f : B → B := fun w => ⟨(w : S)⁻¹ * φ w, mul_mem (inv_mem w.2) (hφB _ w.2)⟩
  have hf : ∀ w w' : B, ((f w : S)⁻¹ * f w' ∈ T ↔ (w : S)⁻¹ * w' ∈ T) := by
    intro w w'
    set u : S := (w : S)⁻¹ * w' with hu
    have hw' : (w' : S) = w * u := by rw [hu]; group
    have huA : u ∈ A := hBA (mul_mem (inv_mem w.2) w'.2)
    have hfw : (f w' : S) = (w' : S)⁻¹ * φ w' := rfl
    rw [hfw, hw', twist_mul]
    set c : S := (w : S)⁻¹ * φ w with hc
    have hcA : c ∈ A := hBA (mul_mem (inv_mem w.2) (hφB _ w.2))
    have hcomm := h.comm_mem (inv_mem hcA) (inv_mem huA)
    have e1 : (f w : S)⁻¹ * (u⁻¹ * c * u * (u⁻¹ * φ u)) =
        (c⁻¹ * u⁻¹ * c⁻¹⁻¹ * u⁻¹⁻¹) * (u⁻¹ * φ u) := by
      change c⁻¹ * (u⁻¹ * c * u * (u⁻¹ * φ u)) = _
      group
    rw [e1]
    constructor
    · intro hmem
      have h2 : u⁻¹ * φ u ∈ T := by
        have := mul_mem (inv_mem hcomm) hmem
        rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
      exact (h.twist_mem_iff huA).1 h2
    · intro huT
      exact mul_mem hcomm ((h.twist_mem_iff huA).2 huT)
  let F : B ⧸ T.subgroupOf B → B ⧸ T.subgroupOf B :=
    Quotient.map' f (fun w w' hww' => by
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hww' ⊢
      exact (hf w w').2 (by simpa using hww'))
  have hFmk : ∀ w : B, F (QuotientGroup.mk w) = QuotientGroup.mk (f w) := fun _ => rfl
  have hFinj : Function.Injective F := by
    intro x y hxy
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨w', rfl⟩ := QuotientGroup.mk_surjective y
    rw [hFmk, hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hxy
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact (hf w w').1 (by simpa using hxy)
  obtain ⟨q, hq⟩ := Finite.injective_iff_surjective.mp hFinj (QuotientGroup.mk ⟨b, hb⟩)
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨w, w.2, ?_⟩
  rw [hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
  have h' : ((w : S)⁻¹ * φ w)⁻¹ * b ∈ T := by simpa [f] using hq
  have := inv_mem h'
  rwa [mul_inv_rev, inv_inv] at this

theorem exists_autComm_mul {a : S} (ha : a ∈ A) : ∃ c ∈ autComm φ A, ∃ t ∈ T, a = c * t := by
  obtain ⟨w, hw, hwT⟩ := h.exists_twist le_rfl h.mapA ha
  refine ⟨w⁻¹ * φ w, twist_mem_autComm hw, (w⁻¹ * φ w)⁻¹ * a, ?_, by group⟩
  have := inv_mem hwT
  rwa [mul_inv_rev, inv_inv] at this

theorem exists_map_eq {x : S} (hx : x ∈ A) : ∃ y ∈ A, φ y = x := by
  have hle : A.map φ.toMonoidHom ≤ A := by
    rintro _ ⟨y, hy, rfl⟩; exact h.mapA y hy
  have heq : A.map φ.toMonoidHom = A := Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective φ.injective])
  rw [← heq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, hy, rfl⟩

theorem map_mem_iff (x : S) : φ x ∈ A ↔ x ∈ A := by
  refine ⟨fun hx => ?_, h.mapA x⟩
  obtain ⟨y, hy, hyx⟩ := h.exists_map_eq hx
  rwa [φ.injective hyx] at hy

end Setting

end SettingDef

end L16

end CFSG.Holt.H78
