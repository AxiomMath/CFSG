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
public import Mathlib.GroupTheory.Transfer
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.RankTwoShapes

open scoped BigOperators

abbrev HomocyclicGroup (n : ℕ) : Type :=
  Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))

abbrev HomocyclicVector (n : ℕ) : Type := ZMod (2 ^ n) × ZMod (2 ^ n)

section Vector

variable {n : ℕ}

theorem zmod_add_self_eq_zero_iff (hn : 1 ≤ n) (x : ZMod (2 ^ n)) :
    x + x = 0 ↔ x = 0 ∨ x = 2 ^ (n - 1) := by
  have hpow : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  constructor
  · intro hx
    rw [← ZMod.natCast_zmod_val x, ← Nat.cast_add, CharP.cast_eq_zero_iff (ZMod (2 ^ n)) (2 ^ n),
      ← two_mul] at hx
    have hx' : 2 * 2 ^ (n - 1) ∣ 2 * x.val := by rw [← hpow]; exact hx
    have hdvd : 2 ^ (n - 1) ∣ x.val := (Nat.mul_dvd_mul_iff_left (by norm_num)).mp hx'
    obtain ⟨k, hk⟩ := hdvd
    have hlt : x.val < 2 * 2 ^ (n - 1) := lt_of_lt_of_eq (ZMod.val_lt x) hpow
    rw [hk] at hlt
    have hk2 : k < 2 := by
      by_contra hge
      have : 2 ^ (n - 1) * 2 ≤ 2 ^ (n - 1) * k := Nat.mul_le_mul_left _ (Nat.le_of_not_lt hge)
      linarith
    interval_cases k
    · left
      rw [← ZMod.natCast_zmod_val x, hk]
      simp
    · right
      rw [← ZMod.natCast_zmod_val x, hk]
      simp
  · rintro (rfl | rfl)
    · simp
    · rw [← two_mul, ← pow_succ']
      have : n - 1 + 1 = n := by omega
      rw [this]
      exact_mod_cast ZMod.natCast_self (2 ^ n)

theorem zmod_half_ne_zero (hn : 1 ≤ n) : (2 : ZMod (2 ^ n)) ^ (n - 1) ≠ 0 := by
  intro h
  have h' : ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (ZMod (2 ^ n)) (2 ^ n)] at h'
  have hle := Nat.le_of_dvd (by positivity) h'
  have hlt : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem zmod_half_add_self (hn : 1 ≤ n) :
    (2 : ZMod (2 ^ n)) ^ (n - 1) + 2 ^ (n - 1) = 0 :=
  (zmod_add_self_eq_zero_iff hn _).mpr (Or.inr rfl)

theorem vector_add_self_eq_zero_iff (hn : 1 ≤ n) (v : HomocyclicVector n) :
    v + v = 0 ↔ v = 0 ∨ v = (2 ^ (n - 1), 0) ∨ v = (0, 2 ^ (n - 1)) ∨
      v = (2 ^ (n - 1), 2 ^ (n - 1)) := by
  obtain ⟨x, y⟩ := v
  have hxy : (x, y) + (x, y) = ((x + x, y + y) : HomocyclicVector n) := rfl
  rw [hxy, Prod.mk_eq_zero, zmod_add_self_eq_zero_iff hn, zmod_add_self_eq_zero_iff hn]
  simp only [Prod.mk.injEq, Prod.mk_eq_zero]
  tauto

theorem vector_klein (hn : 1 ≤ n) (x w u : HomocyclicVector n) (hx : x + x = 0) (hw : w + w = 0)
    (hu : u + u = 0) (hw0 : w ≠ 0) (hu0 : u ≠ 0) (huw : u ≠ w) (hx0 : x ≠ 0) (hxw : x ≠ w) :
    x = u ∨ x = u + w := by
  have hh := zmod_half_ne_zero hn
  have hhh := zmod_half_add_self hn
  rcases (vector_add_self_eq_zero_iff hn x).mp hx with rfl | rfl | rfl | rfl <;>
  rcases (vector_add_self_eq_zero_iff hn w).mp hw with rfl | rfl | rfl | rfl <;>
  rcases (vector_add_self_eq_zero_iff hn u).mp hu with rfl | rfl | rfl | rfl <;>
  simp_all [Prod.ext_iff]

theorem iterate_odd_fixed {α : Type*} (T : α → α) {m : ℕ} (hm : Odd m)
    (hT : ∀ v, T^[m] v = v) (v : α) (h2 : T (T v) = v) : T v = v := by
  obtain ⟨k, rfl⟩ := hm
  have heven : ∀ j, T^[2 * j] v = v := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [show 2 * (j + 1) = 2 + 2 * j by ring, Function.iterate_add_apply, ih]
      simpa using h2
  have h := hT v
  rw [show 2 * k + 1 = 1 + 2 * k by ring, Function.iterate_add_apply, heven k] at h
  simpa using h

theorem iterate_odd_injective {α : Type*} (T : α → α) {m : ℕ} (hm : Odd m)
    (hT : ∀ v, T^[m] v = v) : Function.Injective T := by
  intro a b hab
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [← hT a, ← hT b, hk, Function.iterate_succ_apply, Function.iterate_succ_apply, hab]

theorem vector_two_pow_nsmul (v : HomocyclicVector n) : (2 ^ n : ℕ) • v = 0 := by
  obtain ⟨x, y⟩ := v
  ext <;> simp [nsmul_eq_mul]

theorem vector_odd_endomorphism_eq_id_of_fixed (hn : 1 ≤ n)
    (T : HomocyclicVector n →+ HomocyclicVector n) {m : ℕ} (hm : Odd m)
    (hT : ∀ v, (⇑T)^[m] v = v) (v : HomocyclicVector n) (hv : v ≠ 0) (hfix : T v = v) :
    ∀ w, T w = w := by
  have hinj := iterate_odd_injective (⇑T) hm hT
  have hexists : ∃ k : ℕ, (2 ^ k : ℕ) • v = 0 := ⟨n, vector_two_pow_nsmul v⟩
  classical
  set k₀ := Nat.find hexists with hk₀
  have hk₀spec : (2 ^ k₀ : ℕ) • v = 0 := Nat.find_spec hexists
  have hk₀pos : k₀ ≠ 0 := by
    intro h
    rw [h] at hk₀spec
    simp at hk₀spec
    exact hv hk₀spec
  set w₀ := (2 ^ (k₀ - 1) : ℕ) • v with hw₀
  have hw₀ne : w₀ ≠ 0 := Nat.find_min hexists (by omega : k₀ - 1 < k₀)
  have hw₀two : w₀ + w₀ = 0 := by
    rw [hw₀, ← two_nsmul, smul_smul, ← pow_succ']
    have : k₀ - 1 + 1 = k₀ := by omega
    rw [this]
    exact hk₀spec
  have hw₀fix : T w₀ = w₀ := by rw [hw₀, map_nsmul, hfix]
  have homega : ∀ u, u + u = 0 → T u = u := by
    intro u hu
    by_cases hu0 : u = 0
    · rw [hu0, map_zero]
    by_cases huw : u = w₀
    · rw [huw, hw₀fix]
    have hTu : T u + T u = 0 := by rw [← map_add, hu, map_zero]
    have hTu0 : T u ≠ 0 := by
      intro h
      apply hu0
      apply hinj
      rw [h, map_zero]
    have hTuw : T u ≠ w₀ := by
      intro h
      apply huw
      apply hinj
      rw [h, hw₀fix]
    rcases vector_klein hn (T u) w₀ u hTu hw₀two hu hw₀ne hu0 huw hTu0 hTuw with h | h
    · exact h
    ·
      have h2 : T (T u) = u := by
        rw [h, map_add, h, hw₀fix, add_assoc, hw₀two, add_zero]
      have h1 := iterate_odd_fixed (⇑T) hm hT u h2
      rw [h1] at h
      have : w₀ = 0 := by simpa using h.symm
      exact absurd this hw₀ne
  have hind : ∀ k : ℕ, ∀ x : HomocyclicVector n, (2 ^ k : ℕ) • x = 0 → T x = x := by
    intro k
    induction k with
    | zero =>
      intro x hx
      simp at hx
      rw [hx, map_zero]
    | succ k ih =>
      intro x hx
      have h2x : T (2 • x) = 2 • x := by
        apply ih
        rw [smul_smul, ← pow_succ]
        exact hx
      set d := T x - x with hd
      have hd2 : d + d = 0 := by
        rw [hd, ← two_nsmul, nsmul_sub, ← map_nsmul, h2x, sub_self]
      have hdfix : T d = d := homega d hd2
      have hTx : T x = x + d := by rw [hd]; abel
      have hTTx : T (T x) = x := by
        rw [hTx, map_add, hTx, hdfix, add_assoc, hd2, add_zero]
      exact iterate_odd_fixed (⇑T) hm hT x hTTx
  intro w
  exact hind n w (vector_two_pow_nsmul w)

theorem vector_odd_endomorphism_square (hn : 1 ≤ n)
    (T : HomocyclicVector n →+ HomocyclicVector n) {m : ℕ} (hm : Odd m)
    (hT : ∀ v, (⇑T)^[m] v = v) (hne : ∃ v, T v ≠ v) (a : HomocyclicVector n) (ha2 : a + a = 0)
    (ha0 : a ≠ 0) :
    T a + T a = 0 ∧ T a ≠ 0 ∧ T a ≠ a ∧ T (T a) = T a + a := by
  have hinj := iterate_odd_injective (⇑T) hm hT
  have hfpf : ∀ v, v ≠ 0 → T v ≠ v := by
    intro v hv hfix
    obtain ⟨w, hw⟩ := hne
    exact hw (vector_odd_endomorphism_eq_id_of_fixed hn T hm hT v hv hfix w)
  have hTa0 : T a ≠ 0 := by
    intro h
    apply ha0
    apply hinj
    rw [h, map_zero]
  have hTa2 : T a + T a = 0 := by rw [← map_add, ha2, map_zero]
  have hTaa : T a ≠ a := hfpf a ha0
  have hTTa2 : T (T a) + T (T a) = 0 := by rw [← map_add, hTa2, map_zero]
  have hTTa0 : T (T a) ≠ 0 := by
    intro h
    apply hTa0
    apply hinj
    rw [h, map_zero]
  have hTTaTa : T (T a) ≠ T a := hfpf (T a) hTa0
  have hTTaa : T (T a) ≠ a := by
    intro h
    exact hTaa (iterate_odd_fixed (⇑T) hm hT a h)
  refine ⟨hTa2, hTa0, hTaa, ?_⟩
  rcases vector_klein hn (T (T a)) a (T a) hTTa2 ha2 hTa2 ha0 hTa0 hTaa hTTa0 hTTaa with h | h
  · exact absurd h hTTaTa
  · exact h

theorem vector_odd_endomorphism_cube (hn : 1 ≤ n)
    (T : HomocyclicVector n →+ HomocyclicVector n) {m : ℕ} (hm : Odd m)
    (hT : ∀ v, (⇑T)^[m] v = v) (hne : ∃ v, T v ≠ v) :
    (∀ v, v ≠ 0 → T v ≠ v) ∧ ∀ v, T (T (T v)) = v := by
  have hinj := iterate_odd_injective (⇑T) hm hT
  have hfpf : ∀ v, v ≠ 0 → T v ≠ v := by
    intro v hv hfix
    obtain ⟨w, hw⟩ := hne
    exact hw (vector_odd_endomorphism_eq_id_of_fixed hn T hm hT v hv hfix w)
  refine ⟨hfpf, ?_⟩
  set a : HomocyclicVector n := (2 ^ (n - 1), 0) with ha
  have ha2 : a + a = 0 := (vector_add_self_eq_zero_iff hn a).mpr (Or.inr (Or.inl rfl))
  have ha0 : a ≠ 0 := by
    intro h
    exact zmod_half_ne_zero hn (congrArg Prod.fst h)
  have hTa0 : T a ≠ 0 := by
    intro h
    apply ha0
    apply hinj
    rw [h, map_zero]
  have hTa2 : T a + T a = 0 := by rw [← map_add, ha2, map_zero]
  have hTaa : T a ≠ a := hfpf a ha0
  have hTTa2 : T (T a) + T (T a) = 0 := by rw [← map_add, hTa2, map_zero]
  have hTTa0 : T (T a) ≠ 0 := by
    intro h
    apply hTa0
    apply hinj
    rw [h, map_zero]
  have hTTaTa : T (T a) ≠ T a := hfpf (T a) hTa0
  have hTTaa : T (T a) ≠ a := by
    intro h
    exact hTaa (iterate_odd_fixed (⇑T) hm hT a h)
  have hthird : T (T a) = T a + a := by
    rcases vector_klein hn (T (T a)) a (T a) hTTa2 ha2 hTa2 ha0 hTa0 hTaa hTTa0 hTTaa with h | h
    · exact absurd h hTTaTa
    · exact h
  have hcube : T (T (T a)) = a := by
    rw [hthird, map_add, hthird, add_comm (T a) a, add_assoc, hTa2, add_zero]
  let T3 : HomocyclicVector n →+ HomocyclicVector n := T.comp (T.comp T)
  have hT3 : ∀ v, (⇑T3)^[m] v = v := by
    intro v
    have hcomm : (⇑T3) = (⇑T)^[3] := by
      funext x
      rfl
    rw [hcomm, ← Function.iterate_mul, mul_comm, Function.iterate_mul]
    have hiter : ∀ j, ((⇑T)^[m])^[j] v = v := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih => rw [Function.iterate_succ_apply', ih, hT]
    exact hiter 3
  intro v
  exact vector_odd_endomorphism_eq_id_of_fixed hn T3 hm hT3 a ha0 hcube v

end Vector

section Coordinates

variable {G : Type*} [Group G] {n : ℕ} {S : Subgroup G}

@[expose] def homocyclicEmbed (e : S ≃* HomocyclicGroup n) (v : HomocyclicVector n) : G :=
  (e.symm (Multiplicative.ofAdd v.1, Multiplicative.ofAdd v.2) : S)

@[expose] def homocyclicCoord (e : S ≃* HomocyclicGroup n) (s : S) : HomocyclicVector n :=
  (Multiplicative.toAdd (e s).1, Multiplicative.toAdd (e s).2)

variable (e : S ≃* HomocyclicGroup n)

theorem homocyclicEmbed_mem (v : HomocyclicVector n) : homocyclicEmbed e v ∈ S :=
  (e.symm _).property

theorem homocyclicEmbed_add (v w : HomocyclicVector n) :
    homocyclicEmbed e (v + w) = homocyclicEmbed e v * homocyclicEmbed e w := by
  unfold homocyclicEmbed
  rw [← Subgroup.coe_mul, ← map_mul]
  rfl

theorem homocyclicEmbed_zero : homocyclicEmbed e 0 = 1 := by
  unfold homocyclicEmbed
  have h : ((Multiplicative.ofAdd (0 : HomocyclicVector n).1,
      Multiplicative.ofAdd (0 : HomocyclicVector n).2) : HomocyclicGroup n) = 1 := rfl
  rw [h, map_one, Subgroup.coe_one]

theorem homocyclicEmbed_neg (v : HomocyclicVector n) :
    homocyclicEmbed e (-v) = (homocyclicEmbed e v)⁻¹ := by
  have h := homocyclicEmbed_add e (-v) v
  rw [neg_add_cancel, homocyclicEmbed_zero] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem homocyclicEmbed_nsmul (k : ℕ) (v : HomocyclicVector n) :
    homocyclicEmbed e (k • v) = homocyclicEmbed e v ^ k := by
  induction k with
  | zero => simp [homocyclicEmbed_zero]
  | succ k ih => rw [succ_nsmul, homocyclicEmbed_add, ih, pow_succ]

theorem homocyclicEmbed_injective : Function.Injective (homocyclicEmbed e) := by
  intro v w h
  have h' := e.symm.injective (Subtype.ext h)
  obtain ⟨h1, h2⟩ := Prod.mk.inj h'
  exact Prod.ext (Multiplicative.ofAdd.injective h1) (Multiplicative.ofAdd.injective h2)

theorem homocyclicEmbed_coord (s : S) : homocyclicEmbed e (homocyclicCoord e s) = s := by
  unfold homocyclicEmbed homocyclicCoord
  simp

theorem exists_homocyclicEmbed (s : G) (hs : s ∈ S) : ∃ v, homocyclicEmbed e v = s :=
  ⟨homocyclicCoord e ⟨s, hs⟩, homocyclicEmbed_coord e ⟨s, hs⟩⟩

theorem homocyclicEmbed_eq_one_iff (v : HomocyclicVector n) : homocyclicEmbed e v = 1 ↔ v = 0 := by
  rw [← homocyclicEmbed_zero e]
  exact (homocyclicEmbed_injective e).eq_iff

include e in
theorem homocyclic_mul_comm (a b : G) (ha : a ∈ S) (hb : b ∈ S) : a * b = b * a := by
  obtain ⟨v, rfl⟩ := exists_homocyclicEmbed e a ha
  obtain ⟨w, rfl⟩ := exists_homocyclicEmbed e b hb
  rw [← homocyclicEmbed_add, ← homocyclicEmbed_add, add_comm]

include e in
theorem homocyclic_isMulCommutative : IsMulCommutative S :=
  ⟨⟨fun a b => Subtype.ext (homocyclic_mul_comm e a b a.2 b.2)⟩⟩

include e in
theorem homocyclic_card : Nat.card S = 4 ^ n := by
  rw [Nat.card_congr e.toEquiv, Nat.card_prod]
  have h : Nat.card (Multiplicative (ZMod (2 ^ n))) = 2 ^ n := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [h, ← pow_two, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm]

theorem conj_mem_of_mem_normalizer {g : G} (hg : g ∈ Subgroup.normalizer (S : Set G)) {s : G}
    (hs : s ∈ S) :
    g * s * g⁻¹ ∈ S :=
  (Subgroup.mem_normalizer_iff.mp hg s).mp hs

@[expose] noncomputable def homocyclicConj (g : G) (hg : g ∈ Subgroup.normalizer (S : Set G)) :
    HomocyclicVector n →+ HomocyclicVector n where
  toFun v := homocyclicCoord e ⟨g * homocyclicEmbed e v * g⁻¹,
    conj_mem_of_mem_normalizer hg (homocyclicEmbed_mem e v)⟩
  map_zero' := by
    apply homocyclicEmbed_injective e
    simp only [homocyclicEmbed_coord, homocyclicEmbed_zero]
    group
  map_add' v w := by
    apply homocyclicEmbed_injective e
    simp only [homocyclicEmbed_coord, homocyclicEmbed_add]
    group

@[simp] theorem homocyclicEmbed_conj (g : G) (hg : g ∈ Subgroup.normalizer (S : Set G))
    (v : HomocyclicVector n) :
    homocyclicEmbed e (homocyclicConj e g hg v) = g * homocyclicEmbed e v * g⁻¹ :=
  homocyclicEmbed_coord e _

theorem homocyclicConj_iterate (g : G) (hg : g ∈ Subgroup.normalizer (S : Set G)) (k : ℕ)
    (v : HomocyclicVector n) :
    homocyclicEmbed e ((⇑(homocyclicConj e g hg))^[k] v) =
      g ^ k * homocyclicEmbed e v * (g ^ k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', homocyclicEmbed_conj, ih, pow_succ', mul_inv_rev]
    group

theorem homocyclicConj_eq_iff (g : G) (hg : g ∈ Subgroup.normalizer (S : Set G))
    (v : HomocyclicVector n) :
    homocyclicConj e g hg v = v ↔ g * homocyclicEmbed e v * g⁻¹ = homocyclicEmbed e v := by
  rw [← (homocyclicEmbed_injective e).eq_iff, homocyclicEmbed_conj]

theorem homocyclicConj_eq_id_iff (g : G) (hg : g ∈ Subgroup.normalizer (S : Set G)) :
    (∀ v, homocyclicConj e g hg v = v) ↔ g ∈ Subgroup.centralizer (S : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨v, rfl⟩ := exists_homocyclicEmbed e s hs
    have hv := (homocyclicConj_eq_iff e g hg v).mp (h v)
    calc homocyclicEmbed e v * g = (g * homocyclicEmbed e v * g⁻¹) * g := by rw [hv]
      _ = g * homocyclicEmbed e v := by group
  · intro h v
    rw [homocyclicConj_eq_iff]
    have hc := Subgroup.mem_centralizer_iff.mp h (homocyclicEmbed e v) (homocyclicEmbed_mem e v)
    rw [← hc]
    group

end Coordinates

section SylowStructure

variable {G : Type*} [Group G] [Finite G] {n : ℕ} (S : Sylow 2 G)
  (e : (S : Subgroup G) ≃* HomocyclicGroup n)

omit [Finite G] in
theorem mem_sylow_of_mem_normalizer_of_pow {x : G}
    (hx : x ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (a : ℕ) (hpow : x ^ (2 ^ a) = 1) : x ∈ (S : Subgroup G) := by
  have hp : IsPGroup 2 (Subgroup.zpowers x) := IsPGroup.of_card_dvd_pow (n := a)
    (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hpow)
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr hx
  have hsup := IsPGroup.to_sup_of_normal_right' hp S.isPGroup' hle
  have heq := S.is_maximal' hsup le_sup_right
  rw [← heq]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)

theorem homocyclicConj_odd_iterate (g : G)
    (hg : g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) :
    ∃ m, Odd m ∧ ∀ v, (⇑(homocyclicConj e g hg))^[m] v = v := by
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨m, hm, fun v => ?_⟩
  apply homocyclicEmbed_injective e
  rw [homocyclicConj_iterate]
  have hpow : (g ^ m) ^ (2 ^ a) = 1 := by
    rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hgm := mem_sylow_of_mem_normalizer_of_pow S (Subgroup.pow_mem _ hg m) a hpow
  rw [homocyclic_mul_comm e (g ^ m) (homocyclicEmbed e v) hgm (homocyclicEmbed_mem e v),
    mul_inv_cancel_right]

include e in
theorem homocyclic_normalizer_fixed_point_free (hn : 1 ≤ n) {g : G}
    (hg : g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hgC : g ∉ Subgroup.centralizer ((S : Subgroup G) : Set G))
    {s : G} (hs : s ∈ (S : Subgroup G)) (hfix : g * s * g⁻¹ = s) : s = 1 := by
  by_contra hs1
  obtain ⟨v, rfl⟩ := exists_homocyclicEmbed e s hs
  have hv : v ≠ 0 := fun h => hs1 (by rw [h, homocyclicEmbed_zero])
  obtain ⟨m, hm, hT⟩ := homocyclicConj_odd_iterate S e g hg
  have hfixv : homocyclicConj e g hg v = v := (homocyclicConj_eq_iff e g hg v).mpr hfix
  have hid := vector_odd_endomorphism_eq_id_of_fixed hn _ hm hT v hv hfixv
  exact hgC ((homocyclicConj_eq_id_iff e g hg).mp hid)

include e in
theorem homocyclic_mem_centralizer_of_fixed (hn : 1 ≤ n) {g : G}
    (hg : g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) {s : G}
    (hs : s ∈ (S : Subgroup G)) (hs1 : s ≠ 1)
    (hfix : g * s * g⁻¹ = s) : g ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
  by_contra hgC
  exact hs1 (homocyclic_normalizer_fixed_point_free S e hn hg hgC hs hfix)

theorem homocyclic_half_vector (hn : 1 ≤ n) :
    ((2 ^ (n - 1), 0) : HomocyclicVector n) + (2 ^ (n - 1), 0) = 0 ∧
      ((2 ^ (n - 1), 0) : HomocyclicVector n) ≠ 0 :=
  ⟨(vector_add_self_eq_zero_iff hn _).mpr (Or.inr (Or.inl rfl)),
    fun h => zmod_half_ne_zero hn (congrArg Prod.fst h)⟩

include e in
theorem homocyclic_normalizer_trichotomy (hn : 1 ≤ n) {g₀ : G}
    (hg₀ : g₀ ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hg₀C : g₀ ∉ Subgroup.centralizer ((S : Subgroup G) : Set G))
    {h : G} (hh : h ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) :
    h ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) ∨
      g₀⁻¹ * h ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) ∨
      g₀⁻¹ * (g₀⁻¹ * h) ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
  classical
  obtain ⟨ha2, ha0⟩ := homocyclic_half_vector hn
  set a : HomocyclicVector n := (2 ^ (n - 1), 0)
  set T := homocyclicConj e g₀ hg₀
  set R := homocyclicConj e h hh
  obtain ⟨m, hm, hT⟩ := homocyclicConj_odd_iterate S e g₀ hg₀
  obtain ⟨m', hm', hR⟩ := homocyclicConj_odd_iterate S e h hh
  have hTne : ∃ v, T v ≠ v := by
    by_contra hall
    push Not at hall
    exact hg₀C ((homocyclicConj_eq_id_iff e g₀ hg₀).mp hall)
  obtain ⟨hTa2, hTa0, hTaa, hTTa⟩ := vector_odd_endomorphism_square hn T hm hT hTne a ha2 ha0
  have hRinj := iterate_odd_injective (⇑R) hm' hR
  have hRa2 : R a + R a = 0 := by rw [← map_add, ha2, map_zero]
  have hRa0 : R a ≠ 0 := by
    intro h0
    apply ha0
    apply hRinj
    rw [h0, map_zero]
  have hembed_a : homocyclicEmbed e a ≠ 1 := fun h1 => ha0 ((homocyclicEmbed_eq_one_iff e a).mp h1)
  have hRdef : homocyclicEmbed e (R a) = h * homocyclicEmbed e a * h⁻¹ :=
    homocyclicEmbed_conj e h hh a
  have hTdef : ∀ v, homocyclicEmbed e (T v) = g₀ * homocyclicEmbed e v * g₀⁻¹ :=
    fun v => homocyclicEmbed_conj e g₀ hg₀ v
  by_cases hRa : R a = a
  · left
    apply homocyclic_mem_centralizer_of_fixed S e hn hh (homocyclicEmbed_mem e a) hembed_a
    rw [← hRdef, hRa]
  · rcases vector_klein hn (R a) a (T a) hRa2 ha2 hTa2 ha0 hTa0 hTaa hRa0 hRa with h1 | h2
    · right; left
      apply homocyclic_mem_centralizer_of_fixed S e hn
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg₀) hh) (homocyclicEmbed_mem e a) hembed_a
      have hx : h * homocyclicEmbed e a * h⁻¹ = g₀ * homocyclicEmbed e a * g₀⁻¹ := by
        rw [← hRdef, ← hTdef, h1]
      calc g₀⁻¹ * h * homocyclicEmbed e a * (g₀⁻¹ * h)⁻¹ =
          g₀⁻¹ * (h * homocyclicEmbed e a * h⁻¹) * g₀ := by group
        _ = homocyclicEmbed e a := by rw [hx]; group
    · right; right
      apply homocyclic_mem_centralizer_of_fixed S e hn
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg₀)
          (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg₀) hh)) (homocyclicEmbed_mem e a) hembed_a
      have hx : h * homocyclicEmbed e a * h⁻¹ =
          g₀ * (g₀ * homocyclicEmbed e a * g₀⁻¹) * g₀⁻¹ := by
        rw [← hRdef, ← hTdef, ← hTdef, h2, ← hTTa]
      calc g₀⁻¹ * (g₀⁻¹ * h) * homocyclicEmbed e a * (g₀⁻¹ * (g₀⁻¹ * h))⁻¹ =
          g₀⁻¹ * (g₀⁻¹ * (h * homocyclicEmbed e a * h⁻¹) * g₀) * g₀ := by
            simp only [mul_inv_rev, inv_inv, mul_assoc]
        _ = homocyclicEmbed e a := by rw [hx]; simp only [mul_assoc, inv_mul_cancel_left,
            inv_mul_cancel, mul_one]

end SylowStructure

section Fusion

variable {G : Type*} [Group G] [Finite G] {n : ℕ} (S : Sylow 2 G)
  (e : (S : Subgroup G) ≃* HomocyclicGroup n)

include e in
theorem homocyclic_isConj_iff_normalizer {s t : G} (hs : s ∈ (S : Subgroup G))
    (ht : t ∈ (S : Subgroup G)) :
    IsConj s t ↔ ∃ g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), g * s * g⁻¹ = t := by
  have := homocyclic_isMulCommutative e
  constructor
  · intro hconj
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    have hy : c⁻¹⁻¹ * s * c⁻¹ ∈ (S : Subgroup G) := by rw [inv_inv, hc]; exact ht
    obtain ⟨x, hx, hxeq⟩ := Sylow.conj_eq_normalizer_conj_of_mem S s c⁻¹ hs hy
    refine ⟨x⁻¹, Subgroup.inv_mem _ hx, ?_⟩
    rw [inv_inv, ← hxeq, inv_inv, hc]
  · rintro ⟨g, -, rfl⟩
    exact isConj_iff.mpr ⟨g, rfl⟩

include e in
theorem homocyclic_sq_not_mem_centralizer {g₀ : G}
    (hg₀ : g₀ ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hg₀C : g₀ ∉ Subgroup.centralizer ((S : Subgroup G) : Set G)) :
    g₀ * g₀ ∉ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
  intro hsq
  apply hg₀C
  rw [← homocyclicConj_eq_id_iff e g₀ hg₀]
  obtain ⟨m, hm, hT⟩ := homocyclicConj_odd_iterate S e g₀ hg₀
  intro v
  apply iterate_odd_fixed _ hm hT v
  apply homocyclicEmbed_injective e
  rw [homocyclicEmbed_conj, homocyclicEmbed_conj]
  have hc := Subgroup.mem_centralizer_iff.mp hsq (homocyclicEmbed e v) (homocyclicEmbed_mem e v)
  calc g₀ * (g₀ * homocyclicEmbed e v * g₀⁻¹) * g₀⁻¹ =
      (g₀ * g₀) * homocyclicEmbed e v * (g₀ * g₀)⁻¹ := by group
    _ = homocyclicEmbed e v := by rw [← hc]; group

include e in
theorem homocyclic_orbit_distinct (hn : 1 ≤ n) {g₀ : G}
    (hg₀ : g₀ ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hg₀C : g₀ ∉ Subgroup.centralizer ((S : Subgroup G) : Set G))
    {s : G} (hs : s ∈ (S : Subgroup G)) (hs1 : s ≠ 1) :
    s ≠ g₀ * s * g₀⁻¹ ∧ g₀ * s * g₀⁻¹ ≠ g₀ * (g₀ * s * g₀⁻¹) * g₀⁻¹ ∧
      s ≠ g₀ * (g₀ * s * g₀⁻¹) * g₀⁻¹ := by
  have h1 : s ≠ g₀ * s * g₀⁻¹ := fun h =>
    hs1 (homocyclic_normalizer_fixed_point_free S e hn hg₀ hg₀C hs h.symm)
  refine ⟨h1, ?_, ?_⟩
  · intro h
    apply h1
    have := congrArg (fun x => g₀⁻¹ * x * g₀) h
    calc s = g₀⁻¹ * (g₀ * s * g₀⁻¹) * g₀ := by group
      _ = g₀⁻¹ * (g₀ * (g₀ * s * g₀⁻¹) * g₀⁻¹) * g₀ := this
      _ = g₀ * s * g₀⁻¹ := by group
  · intro h
    have hsq : (g₀ * g₀) * s * (g₀ * g₀)⁻¹ = s :=
      calc (g₀ * g₀) * s * (g₀ * g₀)⁻¹ = g₀ * (g₀ * s * g₀⁻¹) * g₀⁻¹ := by group
        _ = s := h.symm
    exact homocyclic_sq_not_mem_centralizer S e hg₀ hg₀C
      (homocyclic_mem_centralizer_of_fixed S e hn
        (Subgroup.mul_mem _ hg₀ hg₀) hs hs1 hsq)

include e in
theorem homocyclic_isConj_iff (hn : 1 ≤ n) {g₀ : G}
    (hg₀ : g₀ ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hg₀C : g₀ ∉ Subgroup.centralizer ((S : Subgroup G) : Set G))
    {s t : G} (hs : s ∈ (S : Subgroup G)) (ht : t ∈ (S : Subgroup G)) :
    IsConj s t ↔ t = s ∨ t = g₀ * s * g₀⁻¹ ∨ t = g₀ * (g₀ * s * g₀⁻¹) * g₀⁻¹ := by
  rw [homocyclic_isConj_iff_normalizer S e hs ht]
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hcomm : ∀ c ∈ Subgroup.centralizer ((S : Subgroup G) : Set G), c * s * c⁻¹ = s := by
      intro c hc
      rw [← Subgroup.mem_centralizer_iff.mp hc s hs]
      group
    rcases homocyclic_normalizer_trichotomy S e hn hg₀ hg₀C hh with h0 | h1 | h2
    · left
      exact hcomm h h0
    · right; left
      calc h * s * h⁻¹ = g₀ * ((g₀⁻¹ * h) * s * (g₀⁻¹ * h)⁻¹) * g₀⁻¹ := by group
        _ = g₀ * s * g₀⁻¹ := by rw [hcomm _ h1]
    · right; right
      calc h * s * h⁻¹ = g₀ * (g₀ * ((g₀⁻¹ * (g₀⁻¹ * h)) * s * (g₀⁻¹ * (g₀⁻¹ * h))⁻¹) * g₀⁻¹) *
            g₀⁻¹ := by group
        _ = g₀ * (g₀ * s * g₀⁻¹) * g₀⁻¹ := by rw [hcomm _ h2]
  · rintro (rfl | rfl | rfl)
    · exact ⟨1, Subgroup.one_mem _, by group⟩
    · exact ⟨g₀, hg₀, rfl⟩
    · exact ⟨g₀ * g₀, Subgroup.mul_mem _ hg₀ hg₀, by group⟩

end Fusion

theorem exists_normalizer_not_centralizer {G : Type*} [Group G] (S : Subgroup G)
    (hNC : Subgroup.normalizer (S : Set G) ≠ Subgroup.centralizer (S : Set G)) :
    ∃ g ∈ Subgroup.normalizer (S : Set G), g ∉ Subgroup.centralizer (S : Set G) := by
  by_contra hall
  push Not at hall
  exact hNC (le_antisymm (fun g hg => hall g hg) (Subgroup.centralizer_le_normalizer _))

section Complements

variable {G : Type*} [Group G] [Finite G]

theorem exists_normal_complement_in_subgroup (S : Sylow 2 G) (H : Subgroup G)
    (hSH : (S : Subgroup G) ≤ H)
    (hNC : ∀ h ∈ H, h ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) →
      h ∈ Subgroup.centralizer ((S : Subgroup G) : Set G)) :
    ∃ K : Subgroup H, K.Normal ∧ K.IsComplement' ((S : Subgroup G).subgroupOf H) := by
  let S' : Sylow 2 H := S.subtype hSH
  have hS' : (S' : Subgroup H) = (S : Subgroup G).subgroupOf H := Sylow.coe_subtype _ _
  have hconj : ∀ x : H, x ∈ Subgroup.normalizer (S' : Set H) →
      ∀ y ∈ (S : Subgroup G), (x : G) * y * (x : G)⁻¹ ∈ (S : Subgroup G) := by
    intro x hx y hy
    have hmem : (⟨y, hSH hy⟩ : H) ∈ (S' : Subgroup H) := by
      rw [hS', Subgroup.mem_subgroupOf]
      exact hy
    have := (Subgroup.mem_normalizer_iff.mp hx ⟨y, hSH hy⟩).mp hmem
    rw [hS', Subgroup.mem_subgroupOf] at this
    simpa using this
  have hle : Subgroup.normalizer (S' : Set H) ≤ Subgroup.centralizer (S' : Set H) := by
    intro x hx
    have hxN : (x : G) ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · exact hconj x hx y
      · intro hy
        have h2 := hconj x⁻¹ (Subgroup.inv_mem _ hx) _ hy
        simpa [mul_assoc] using h2
    have hxC := hNC x x.property hxN
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : (z : G) ∈ (S : Subgroup G) := by
      have : z ∈ (S' : Subgroup H) := hz
      rw [hS', Subgroup.mem_subgroupOf] at this
      exact this
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hxC z hz'
  refine ⟨(MonoidHom.transferSylow S' hle).ker, inferInstance, ?_⟩
  rw [← hS']
  exact MonoidHom.ker_transferSylow_isComplement' S' hle

theorem normal_complement_structure (S : Sylow 2 G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H)
    (K : Subgroup H) (hKn : K.Normal) (hK : K.IsComplement' ((S : Subgroup G).subgroupOf H)) :
    (Odd (Nat.card K) ∧ K.index = Nat.card S) ∧
    (∀ K' : Subgroup H, K'.Normal → Odd (Nat.card K') → K'.index = Nat.card S → K' = K) ∧
    K.Characteristic ∧ K ⊔ (S : Subgroup G).subgroupOf H = ⊤ ∧
      K ⊓ (S : Subgroup G).subgroupOf H = ⊥ := by
  let S' : Sylow 2 H := S.subtype hSH
  have hS' : (S' : Subgroup H) = (S : Subgroup G).subgroupOf H := Sylow.coe_subtype _ _
  have hcardS' : Nat.card ((S : Subgroup G).subgroupOf H) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv
  have hindex : K.index = Nat.card S := by
    rw [hK.symm.index_eq_card, hcardS']
  have hodd : Odd (Nat.card K) := by
    have hnd := Sylow.not_dvd_index S'
    rw [hS', hK.index_eq_card] at hnd
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hnd)
  have hHK : ∀ K' : Subgroup H, Nat.card K' * K'.index = Nat.card H := fun K' =>
    Subgroup.card_mul_index K'
  have hS2 : ∃ k : ℕ, Nat.card S = 2 ^ k := (IsPGroup.iff_card).mp S.isPGroup'
  have huniq : ∀ K' : Subgroup H, K'.Normal → Odd (Nat.card K') → K'.index = Nat.card S →
      K' = K := by
    intro K' hK'n hK'odd hK'index
    have hle : K' ≤ K := by
      intro x hx
      obtain ⟨k, hk⟩ := hS2
      have hq : orderOf (x : H ⧸ K) ∣ 2 ^ k := by
        rw [← hk, ← hindex, Subgroup.index_eq_card]
        exact orderOf_dvd_natCard _
      have hq' : orderOf (x : H ⧸ K) ∣ Nat.card K' :=
        (orderOf_map_dvd (QuotientGroup.mk' K) x).trans (Subgroup.orderOf_dvd_natCard K' hx)
      have hcop : Nat.Coprime (orderOf (x : H ⧸ K)) (2 ^ k) := by
        have hodd' : Odd (orderOf (x : H ⧸ K)) := hK'odd.of_dvd_nat hq'
        exact (Nat.coprime_two_right.mpr hodd').pow_right k
      have h1 := Nat.Coprime.eq_one_of_dvd hcop hq
      rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
      exact h1
    apply Subgroup.eq_of_le_of_card_ge hle
    have h1 := hHK K
    have h2 := hHK K'
    rw [hindex] at h1
    rw [hK'index] at h2
    have hpos : 0 < Nat.card S := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)).le
  refine ⟨⟨hodd, hindex⟩, huniq, ?_, hK.sup_eq_top, disjoint_iff.mp hK.disjoint⟩
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  apply huniq
  · exact hKn.map φ.toMonoidHom φ.surjective
  · rw [Subgroup.card_map_of_injective φ.injective]
    exact hodd
  · have h1 := hHK (K.map φ.toMonoidHom)
    have h2 := hHK K
    rw [Subgroup.card_map_of_injective φ.injective] at h1
    rw [← hindex]
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := K)) (h1.trans h2.symm)

end Complements

section Node

variable {G : Type*} [Group G] [Finite G] {n : ℕ} (S : Sylow 2 G)
  (e : (S : Subgroup G) ≃* HomocyclicGroup n)

theorem card_quotient_eq_three {N : Type*} [Group N] (C : Subgroup N) (x : N) (hx : x ∉ C)
    (hx2 : x * x ∉ C) (htri : ∀ h, h ∈ C ∨ x⁻¹ * h ∈ C ∨ x⁻¹ * (x⁻¹ * h) ∈ C) :
    Nat.card (N ⧸ C) = 3 := by
  let f : Fin 3 → N ⧸ C := fun k => ((x ^ (k : ℕ) : N) : N ⧸ C)
  have hmk : ∀ a b : N, ((a : N ⧸ C) = (b : N ⧸ C)) ↔ a⁻¹ * b ∈ C := fun a b => QuotientGroup.eq
  have hxinv : x⁻¹ ∉ C := fun h => hx (by simpa using C.inv_mem h)
  have hx2inv : x⁻¹ * x⁻¹ ∉ C := fun h => hx2 (by simpa [mul_inv_rev] using C.inv_mem h)
  have hbij : Function.Bijective f := by
    constructor
    · intro i j hij
      simp only [f, hmk] at hij
      fin_cases i <;> fin_cases j
      · rfl
      · exact absurd (by simpa using hij) hx
      · exact absurd (by simpa [pow_two] using hij) hx2
      · exact absurd (by simpa using hij) hxinv
      · rfl
      · exact absurd (by simpa [pow_two, mul_assoc] using hij) hx
      · exact absurd (by simpa [pow_two] using hij) hx2inv
      · exact absurd (by simpa [pow_two, mul_assoc] using hij) hxinv
      · rfl
    · intro q
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
      rcases htri h with h0 | h1 | h2
      · exact ⟨0, by simpa [f, hmk] using h0⟩
      · exact ⟨1, by simpa [f, hmk] using h1⟩
      · exact ⟨2, by simpa [f, hmk, pow_two, mul_assoc] using h2⟩
  rw [← Nat.card_eq_of_bijective f hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

include e in
theorem homocyclic_card_normalizer_quotient (hn : 1 ≤ n) {g₀ : G}
    (hg₀ : g₀ ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hg₀C : g₀ ∉ Subgroup.centralizer ((S : Subgroup G) : Set G)) :
    Nat.card (Subgroup.normalizer ((S : Subgroup G) : Set G) ⧸
      (Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
        (Subgroup.normalizer ((S : Subgroup G) : Set G))) = 3 := by
  apply card_quotient_eq_three _ ⟨g₀, hg₀⟩
  · rw [Subgroup.mem_subgroupOf]
    exact hg₀C
  · rw [Subgroup.mem_subgroupOf]
    exact homocyclic_sq_not_mem_centralizer S e hg₀ hg₀C
  · intro h
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact homocyclic_normalizer_trichotomy S e hn hg₀ hg₀C h.property

include e in
theorem homocyclic_normalizer_inf_centralizer (hn : 1 ≤ n) {s : G}
    (hs : s ∈ (S : Subgroup G)) (hs1 : s ≠ 1) :
    Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓ Subgroup.centralizer {s} =
      Subgroup.centralizer ((S : Subgroup G) : Set G) := by
  ext h
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hN, hcomm⟩
    apply homocyclic_mem_centralizer_of_fixed S e hn hN hs hs1
    rw [hcomm]
    group
  · intro hC
    exact ⟨Subgroup.centralizer_le_normalizer _ hC,
      (Subgroup.mem_centralizer_iff.mp hC s hs).symm⟩

include e in
theorem homocyclic_centralizer_normalizer_le (hn : 1 ≤ n) {s : G}
    (hs : s ∈ (S : Subgroup G)) (hs1 : s ≠ 1) (H : Subgroup G)
    (hH : ∀ h ∈ H, h * s = s * h) :
    ∀ h ∈ H, h ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) →
      h ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
  intro h hh hN
  apply homocyclic_mem_centralizer_of_fixed S e hn hN hs hs1
  rw [hH h hh]
  group

include e in
theorem homocyclic_centralizer_zpowers_complement (hn : 1 ≤ n) {s : G}
    (hs : s ∈ (S : Subgroup G)) (hs1 : s ≠ 1) :
    ∃ (K : Subgroup (Subgroup.centralizer (Subgroup.zpowers s : Set G))) (_ : K.Normal),
      Nat.Coprime 2 (Nat.card K) ∧
      IsPGroup 2 (Subgroup.centralizer (Subgroup.zpowers s : Set G) ⧸ K) ∧
      Nat.card (Subgroup.centralizer (Subgroup.zpowers s : Set G) ⧸ K) = Nat.card S := by
  set H := Subgroup.centralizer (Subgroup.zpowers s : Set G)
  have hSH : (S : Subgroup G) ≤ H := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (homocyclic_mul_comm e _ _ (Subgroup.zpow_mem _ hs k) hx)
  have hHs : ∀ h ∈ H, h * s = s * h := fun h hh =>
    (Subgroup.mem_centralizer_iff.mp hh s (Subgroup.mem_zpowers s)).symm
  obtain ⟨K, hKn, hK⟩ := exists_normal_complement_in_subgroup S H hSH
    (homocyclic_centralizer_normalizer_le S e hn hs hs1 H hHs)
  obtain ⟨⟨hodd, hindex⟩, -⟩ := normal_complement_structure S H hSH K hKn hK
  have hquot : Nat.card (H ⧸ K) = Nat.card S := by rw [← Subgroup.index_eq_card, hindex]
  refine ⟨K, hKn, Nat.coprime_two_left.mpr hodd, ?_, hquot⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp S.isPGroup'
  exact IsPGroup.of_card (n := k) (hquot.trans hk)

include e in
theorem homocyclic_involutions_conjugate (hn : 1 ≤ n) {g₀ : G}
    (hg₀ : g₀ ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hg₀C : g₀ ∉ Subgroup.centralizer ((S : Subgroup G) : Set G))
    {x y : G} (hx : x ∈ (S : Subgroup G)) (hy : y ∈ (S : Subgroup G)) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1) : IsConj x y := by
  rw [homocyclic_isConj_iff S e hn hg₀ hg₀C hx hy]
  obtain ⟨v, rfl⟩ := exists_homocyclicEmbed e x hx
  obtain ⟨w, rfl⟩ := exists_homocyclicEmbed e y hy
  have hv0 : v ≠ 0 := fun h => hx1 (by rw [h, homocyclicEmbed_zero])
  have hw0 : w ≠ 0 := fun h => hy1 (by rw [h, homocyclicEmbed_zero])
  have hv2 : v + v = 0 := by
    rw [← homocyclicEmbed_eq_one_iff e, homocyclicEmbed_add, ← pow_two, hx2]
  have hw2 : w + w = 0 := by
    rw [← homocyclicEmbed_eq_one_iff e, homocyclicEmbed_add, ← pow_two, hy2]
  set T := homocyclicConj e g₀ hg₀
  obtain ⟨m, hm, hT⟩ := homocyclicConj_odd_iterate S e g₀ hg₀
  have hTne : ∃ v, T v ≠ v := by
    by_contra hall
    push Not at hall
    exact hg₀C ((homocyclicConj_eq_id_iff e g₀ hg₀).mp hall)
  obtain ⟨hTv2, hTv0, hTvv, hTTv⟩ := vector_odd_endomorphism_square hn T hm hT hTne v hv2 hv0
  by_cases hwv : w = v
  · left
    rw [hwv]
  · right
    rcases vector_klein hn w v (T v) hw2 hv2 hTv2 hv0 hTv0 hTvv hw0 hwv with h1 | h2
    · left
      rw [h1, homocyclicEmbed_conj]
    · right
      rw [h2, ← hTTv, homocyclicEmbed_conj, homocyclicEmbed_conj]

include e in
theorem homocyclic_sylow_normalizer_local_complements (hn : 1 ≤ n)
    (hNC : Subgroup.normalizer ((S : Subgroup G) : Set G) ≠
      Subgroup.centralizer ((S : Subgroup G) : Set G)) :
    Nat.card (Subgroup.normalizer ((S : Subgroup G) : Set G) ⧸
      (Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
        (Subgroup.normalizer ((S : Subgroup G) : Set G))) = 3 ∧
    (∀ g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G),
      g ∉ Subgroup.centralizer ((S : Subgroup G) : Set G) →
        ∀ s ∈ (S : Subgroup G), g * s * g⁻¹ = s → s = 1) ∧
    (∀ s ∈ (S : Subgroup G), s ≠ 1 →
      ((S : Set G) ∩ {t | IsConj s t} =
        {t | ∃ g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), t = g * s * g⁻¹}) ∧
      ((S : Set G) ∩ {t | IsConj s t}).ncard = 3 ∧
      Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓ Subgroup.centralizer {s} =
        Subgroup.centralizer ((S : Subgroup G) : Set G) ∧
      ∃ K : Subgroup (Subgroup.centralizer {s}),
        (K.Normal ∧ Odd (Nat.card K) ∧ K.index = Nat.card S) ∧
        (∀ K' : Subgroup (Subgroup.centralizer {s}),
          K'.Normal → Odd (Nat.card K') → K'.index = Nat.card S → K' = K) ∧
        K.Characteristic ∧
        K ⊔ (S : Subgroup G).subgroupOf (Subgroup.centralizer {s}) = ⊤ ∧
        K ⊓ (S : Subgroup G).subgroupOf (Subgroup.centralizer {s}) = ⊥) ∧
    (∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x ≠ 1 → y ≠ 1 → x ^ 2 = 1 → y ^ 2 = 1 →
      IsConj x y) := by
  obtain ⟨g₀, hg₀, hg₀C⟩ := exists_normalizer_not_centralizer (S : Subgroup G) hNC
  refine ⟨homocyclic_card_normalizer_quotient S e hn hg₀ hg₀C,
    fun g hg hgC s hs hfix => homocyclic_normalizer_fixed_point_free S e hn hg hgC hs hfix,
    fun s hs hs1 => ?_,
    fun x hx y hy hx1 hy1 hx2 hy2 =>
      homocyclic_involutions_conjugate S e hn hg₀ hg₀C hx hy hx1 hy1 hx2 hy2⟩
  have horbit : (S : Set G) ∩ {t | IsConj s t} =
      {t | ∃ g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), t = g * s * g⁻¹} := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, SetLike.mem_coe]
    constructor
    · rintro ⟨ht, hconj⟩
      obtain ⟨g, hg, hgt⟩ := (homocyclic_isConj_iff_normalizer S e hs ht).mp hconj
      exact ⟨g, hg, hgt.symm⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨conj_mem_of_mem_normalizer hg hs, isConj_iff.mpr ⟨g, rfl⟩⟩
  have hthree : (S : Set G) ∩ {t | IsConj s t} =
      {s, g₀ * s * g₀⁻¹, g₀ * (g₀ * s * g₀⁻¹) * g₀⁻¹} := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, SetLike.mem_coe, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨ht, hconj⟩
      exact (homocyclic_isConj_iff S e hn hg₀ hg₀C hs ht).mp hconj
    · intro ht
      have htS : t ∈ (S : Subgroup G) := by
        rcases ht with rfl | rfl | rfl
        · exact hs
        · exact conj_mem_of_mem_normalizer hg₀ hs
        · exact conj_mem_of_mem_normalizer hg₀ (conj_mem_of_mem_normalizer hg₀ hs)
      exact ⟨htS, (homocyclic_isConj_iff S e hn hg₀ hg₀C hs htS).mpr ht⟩
  obtain ⟨hd1, hd2, hd3⟩ := homocyclic_orbit_distinct S e hn hg₀ hg₀C hs hs1
  have hcard : ((S : Set G) ∩ {t | IsConj s t}).ncard = 3 := by
    rw [hthree, Set.ncard_eq_three]
    exact ⟨_, _, _, hd1, hd3, hd2, rfl⟩
  refine ⟨horbit, hcard, homocyclic_normalizer_inf_centralizer S e hn hs hs1, ?_⟩
  have hSH : (S : Subgroup G) ≤ Subgroup.centralizer {s} := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact homocyclic_mul_comm e x s hx hs
  obtain ⟨K, hKn, hK⟩ := exists_normal_complement_in_subgroup S (Subgroup.centralizer {s}) hSH
    (homocyclic_centralizer_normalizer_le S e hn hs hs1 _
      (fun h hh => Subgroup.mem_centralizer_singleton_iff.mp hh))
  obtain ⟨⟨hodd, hindex⟩, huniq, hchar, hsup, hinf⟩ :=
    normal_complement_structure S _ hSH K hKn hK
  exact ⟨K, ⟨hKn, hodd, hindex⟩, huniq, hchar, hsup, hinf⟩

include e in
theorem homocyclic_normalizer_ne_centralizer_of_simple [IsSimpleGroup G] (hn : 1 ≤ n)
    (hnonab : ∃ a b : G, a * b ≠ b * a) :
    Subgroup.normalizer ((S : Subgroup G) : Set G) ≠
      Subgroup.centralizer ((S : Subgroup G) : Set G) := by
  intro heq
  have hle : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
      Subgroup.centralizer ((S : Subgroup G) : Set G) := heq.le
  have hcomp := MonoidHom.ker_transferSylow_isComplement' S hle
  rcases Subgroup.Normal.eq_bot_or_eq_top (MonoidHom.transferSylow S hle).ker with hbot | htop
  · rw [hbot, Subgroup.isComplement'_bot_left] at hcomp
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    exact homocyclic_mul_comm e a b (by rw [hcomp]; trivial) (by rw [hcomp]; trivial)
  · rw [htop, Subgroup.isComplement'_top_left] at hcomp
    have hcard := homocyclic_card e
    rw [hcomp, Subgroup.card_bot] at hcard
    have : (1 : ℕ) < 4 ^ n := Nat.one_lt_pow (by omega) (by norm_num)
    omega

end Node

end CFSG.RankTwoShapes
