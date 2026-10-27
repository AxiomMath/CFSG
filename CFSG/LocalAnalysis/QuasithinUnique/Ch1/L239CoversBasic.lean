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

open scoped commutatorElement

namespace CFSG.QuasithinUnique.Vol2Native.L239.Covers

abbrev Letter : Type := Fin 2 × Bool

section Words

variable {M : Type*} [Group M]

@[expose] def letterVal (x : Fin 2 → M) (l : Letter) : M := if l.2 then x l.1 else (x l.1)⁻¹

@[expose] def wordVal (x : Fin 2 → M) (w : List Letter) : M := (w.map (letterVal x)).prod

@[simp] theorem wordVal_nil (x : Fin 2 → M) : wordVal x [] = 1 := rfl

theorem wordVal_cons (x : Fin 2 → M) (l : Letter) (w : List Letter) :
    wordVal x (l :: w) = letterVal x l * wordVal x w := by
  simp [wordVal]

theorem wordVal_append (x : Fin 2 → M) (u v : List Letter) :
    wordVal x (u ++ v) = wordVal x u * wordVal x v := by
  simp [wordVal]

theorem map_letterVal {N : Type*} [Group N] (f : M →* N) (x : Fin 2 → M) (l : Letter) :
    f (letterVal x l) = letterVal (fun i => f (x i)) l := by
  unfold letterVal
  split <;> simp

theorem map_wordVal {N : Type*} [Group N] (f : M →* N) (x : Fin 2 → M) (w : List Letter) :
    f (wordVal x w) = wordVal (fun i => f (x i)) w := by
  induction w with
  | nil => simp
  | cons l w ih => rw [wordVal_cons, wordVal_cons, map_mul, ih, map_letterVal]

theorem wordVal_eq_lift (x : Fin 2 → M) (w : List Letter) :
    wordVal x w = FreeGroup.lift x (FreeGroup.mk w) := by
  induction w with
  | nil => simp only [wordVal_nil]; exact (map_one _).symm
  | cons l w ih =>
    rw [wordVal_cons, ih]
    have h : FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w := rfl
    rw [h, map_mul]
    congr 1
    obtain ⟨i, b⟩ := l
    cases b
    · rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
        FreeGroup.lift_apply_of]
      rfl
    · rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
      rfl

theorem wordVal_inv_letter (x : Fin 2 → M) (i : Fin 2) :
    letterVal x (i, false) = (letterVal x (i, true))⁻¹ := rfl

end Words

section Central

variable {M : Type*} [Group M]

@[expose] def expsum (i : Fin 2) (w : List Letter) : ℤ :=
  (w.map fun l => if l.1 = i then (if l.2 then (1 : ℤ) else -1) else 0).sum

@[simp] theorem expsum_nil (i : Fin 2) : expsum i [] = 0 := rfl

theorem expsum_cons (i : Fin 2) (l : Letter) (w : List Letter) :
    expsum i (l :: w) = (if l.1 = i then (if l.2 then (1 : ℤ) else -1) else 0) + expsum i w := by
  simp [expsum]

theorem letterVal_eq_zpow (x : Fin 2 → M) (l : Letter) :
    letterVal x l = x l.1 ^ (if l.2 then (1 : ℤ) else -1) := by
  unfold letterVal
  split_ifs <;> simp

theorem center_zpow_comm {z : M} (hz : z ∈ Subgroup.center M) (g : M) (n : ℤ) :
    g * z ^ n = z ^ n * g :=
  (Commute.zpow_right (Subgroup.mem_center_iff.mp hz g) n).eq

theorem wordVal_mul_central (x z : Fin 2 → M) (hz : ∀ i, z i ∈ Subgroup.center M)
    (w : List Letter) :
    wordVal (fun i => x i * z i) w = wordVal x w * wordVal z w := by
  induction w with
  | nil => simp
  | cons l w ih =>
    rw [wordVal_cons, wordVal_cons, wordVal_cons, ih]
    have hxz : letterVal (fun i => x i * z i) l = letterVal x l * letterVal z l := by
      rw [letterVal_eq_zpow, letterVal_eq_zpow, letterVal_eq_zpow]
      exact Commute.mul_zpow (Subgroup.mem_center_iff.mp (hz l.1) (x l.1)) _
    have hc : letterVal z l * wordVal x w = wordVal x w * letterVal z l := by
      rw [letterVal_eq_zpow]
      exact (center_zpow_comm (hz l.1) (wordVal x w) _).symm
    rw [hxz]
    calc letterVal x l * letterVal z l * (wordVal x w * wordVal z w)
        = letterVal x l * ((letterVal z l * wordVal x w) * wordVal z w) := by
          simp only [mul_assoc]
      _ = letterVal x l * ((wordVal x w * letterVal z l) * wordVal z w) := by rw [hc]
      _ = letterVal x l * wordVal x w * (letterVal z l * wordVal z w) := by
          simp only [mul_assoc]

theorem wordVal_central (z : Fin 2 → M) (hz : ∀ i, z i ∈ Subgroup.center M) (w : List Letter) :
    wordVal z w = z 0 ^ expsum 0 w * z 1 ^ expsum 1 w := by
  induction w with
  | nil => simp
  | cons l w ih =>
    rw [wordVal_cons, ih, expsum_cons, expsum_cons, letterVal_eq_zpow]
    obtain ⟨i, b⟩ := l
    simp only
    set s : ℤ := if b then 1 else -1 with hs
    by_cases h0 : i = 0
    · subst h0
      have h10 : ¬ ((0 : Fin 2) = 1) := by decide
      simp only [h10, ↓reduceIte, zero_add, zpow_add, mul_assoc]
    · have h1 : i = 1 := by revert h0; fin_cases i <;> simp
      subst h1
      have h01 : ¬ ((1 : Fin 2) = 0) := by decide
      simp only [h01, ↓reduceIte, zero_add, zpow_add]
      have := center_zpow_comm (hz 1) (z 0 ^ expsum 0 w) s
      calc z 1 ^ s * (z 0 ^ expsum 0 w * z 1 ^ expsum 1 w)
          = (z 1 ^ s * z 0 ^ expsum 0 w) * z 1 ^ expsum 1 w := by simp only [mul_assoc]
        _ = (z 0 ^ expsum 0 w * z 1 ^ s) * z 1 ^ expsum 1 w := by rw [← this]
        _ = z 0 ^ expsum 0 w * (z 1 ^ s * z 1 ^ expsum 1 w) := by simp only [mul_assoc]

theorem zpow_eq_of_mul_self_eq_one {z : M} (hz : z * z = 1) (n : ℤ) :
    z ^ n = if Even n then 1 else z := by
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' n
  · have h : Even (2 * k) := even_two_mul k
    simp only [h, ↓reduceIte, zpow_mul, h2, one_zpow]
  · have h : ¬ Even (2 * k + 1) := by simp
    simp only [h, ↓reduceIte, zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

theorem wordVal_adjust_sq (x z : Fin 2 → M) (hz : ∀ i, z i ∈ Subgroup.center M)
    (hsq : ∀ i, z i * z i = 1) (w : List Letter) :
    wordVal (fun i => x i * z i) w = wordVal x w *
      ((if Even (expsum 0 w) then 1 else z 0) * (if Even (expsum 1 w) then 1 else z 1)) := by
  rw [wordVal_mul_central x z hz, wordVal_central z hz, zpow_eq_of_mul_self_eq_one (hsq 0),
    zpow_eq_of_mul_self_eq_one (hsq 1)]

end Central

section Generation

variable {M : Type*} [Group M]

theorem commutator_mul_center_left {a c z : M} (hz : z ∈ Subgroup.center M) :
    ⁅a * z, c⁆ = ⁅a, c⁆ := by
  have hzc : c * z = z * c := Subgroup.mem_center_iff.mp hz c
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * c * (a * z)⁻¹ * c⁻¹ = a * (z * c) * (z⁻¹ * a⁻¹) * c⁻¹ := by
        simp only [mul_assoc, mul_inv_rev]
    _ = a * (c * z) * (z⁻¹ * a⁻¹) * c⁻¹ := by rw [← hzc]
    _ = a * c * a⁻¹ * c⁻¹ := by group

theorem commutator_mul_center_right {a c z : M} (hz : z ∈ Subgroup.center M) :
    ⁅a, c * z⁆ = ⁅a, c⁆ := by
  rw [← commutatorElement_inv, commutator_mul_center_left hz, commutatorElement_inv]

variable {E G : Type*} [Group E] [Group G]

theorem closure_eq_top_of_lifts (π : E →* G)
    (hz : ∀ z, π z = 1 → z ∈ Subgroup.center E) (hperf : commutator E = ⊤) (S : Set E)
    (hS : Subgroup.closure (π '' S) = ⊤) : Subgroup.closure S = ⊤ := by
  set E₀ := Subgroup.closure S with hE₀
  have hmap : E₀.map π = ⊤ := by
    rw [hE₀, MonoidHom.map_closure, hS]
  have hdec : ∀ e : E, ∃ e₀ ∈ E₀, ∃ z, π z = 1 ∧ e = e₀ * z := by
    intro e
    have : π e ∈ E₀.map π := by rw [hmap]; trivial
    obtain ⟨e₀, he₀, he⟩ := this
    exact ⟨e₀, he₀, e₀⁻¹ * e, by simp [he], by simp⟩
  have hcomm : commutator E ≤ E₀ := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr ?_
    intro a _ b _
    obtain ⟨a₀, ha₀, za, hza, rfl⟩ := hdec a
    obtain ⟨b₀, hb₀, zb, hzb, rfl⟩ := hdec b
    rw [commutator_mul_center_left (hz za hza), commutator_mul_center_right (hz zb hzb),
      commutatorElement_def]
    exact E₀.mul_mem (E₀.mul_mem (E₀.mul_mem ha₀ hb₀) (E₀.inv_mem ha₀)) (E₀.inv_mem hb₀)
  rw [hperf] at hcomm
  exact top_le_iff.mp hcomm

theorem card_eq_card_mul_card_ker (π : E →* G) (hπ : Function.Surjective π) :
    Nat.card E = Nat.card G * Nat.card π.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv]

end Generation

section Reduction

universe u

theorem ker_eq_bot_of_exp2 {Q : Type*} [Group Q]
    (hexp2 : ∀ (E' : Type u) [Group E'] [Finite E'] (π' : E' →* Q), Function.Surjective π' →
      (∀ z, π' z = 1 → z ∈ Subgroup.center E') → (∀ z, π' z = 1 → z * z = 1) →
      commutator E' = ⊤ → π'.ker = ⊥)
    {E : Type u} [Group E] [Finite E] (π : E →* Q) (hz : ∀ z, π z = 1 → z ∈ Subgroup.center E)
    (hp2 : IsPGroup 2 π.ker) (hperf : commutator E = ⊤) (hπ : Function.Surjective π) :
    π.ker = ⊥ := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hp2
  have hm1 : 1 ≤ m := by
    by_contra h
    have h0 : m = 0 := by omega
    rw [h0, pow_zero] at hm
    exact hne (Subgroup.card_eq_one.mp hm)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥π.ker) 2 (n := m - 1)
    (by rw [hm]; exact pow_dvd_pow 2 (Nat.sub_le m 1))
  set Z₁ : Subgroup E := K.map π.ker.subtype with hZ₁
  have hZ₁ker : ∀ e ∈ Z₁, π e = 1 := by
    intro e he
    obtain ⟨k, -, rfl⟩ := he
    exact k.2
  have hZ₁c : ∀ e ∈ Z₁, e ∈ Subgroup.center E := fun e he => hz e (hZ₁ker e he)
  have hnorm : Z₁.Normal := by
    refine ⟨fun e he g => ?_⟩
    have h1 := Subgroup.mem_center_iff.mp (hZ₁c e he) g
    have h3 : g * e * g⁻¹ = e := by rw [h1, mul_assoc, mul_inv_cancel, mul_one]
    rw [h3]
    exact he
  let π' : E ⧸ Z₁ →* Q := QuotientGroup.lift Z₁ π hZ₁ker
  have hπ'surj : Function.Surjective π' := by
    intro q
    obtain ⟨e, rfl⟩ := hπ q
    exact ⟨QuotientGroup.mk e, rfl⟩
  have hπ'z : ∀ z', π' z' = 1 → z' ∈ Subgroup.center (E ⧸ Z₁) := by
    intro z' hz'
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective z'
    have he : π e = 1 := hz'
    rw [Subgroup.mem_center_iff]
    intro g'
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp (hz e he) g]
  have hKn : K.Normal := by
    refine ⟨fun k hk g => ?_⟩
    have h1 := Subgroup.mem_center_iff.mp (hz k k.2) g
    have h3 : g * k * g⁻¹ = k := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [h1, mul_assoc, mul_inv_cancel, mul_one]
    rw [h3]
    exact hk
  have hcardq : Nat.card (↥π.ker ⧸ K) = 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    rw [hm, hK, show (2 : ℕ) ^ m = 2 ^ (m - 1) * 2 by
      rw [← pow_succ]; congr 1; omega] at h
    have hpos : 0 < 2 ^ (m - 1) := by positivity
    exact (Nat.eq_of_mul_eq_mul_left hpos (by linarith [h])).symm
  have hπ'2 : ∀ z', π' z' = 1 → z' * z' = 1 := by
    intro z' hz'
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective z'
    have he : π e = 1 := hz'
    have hsq : (QuotientGroup.mk (⟨e, he⟩ : ↥π.ker) : ↥π.ker ⧸ K) ^ 2 = 1 := by
      rw [← hcardq]
      exact pow_card_eq_one'
    rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff] at hsq
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact ⟨_, hsq, rfl⟩
  have hperf' : commutator (E ⧸ Z₁) = ⊤ := by
    have hsurj : Function.Surjective (QuotientGroup.mk' Z₁) := QuotientGroup.mk'_surjective Z₁
    have h := Subgroup.map_commutator (⊤ : Subgroup E) ⊤ (QuotientGroup.mk' Z₁)
    rw [Subgroup.map_top_of_surjective _ hsurj] at h
    rw [commutator_def, ← h]
    change Subgroup.map _ (commutator E) = ⊤
    rw [hperf, Subgroup.map_top_of_surjective _ hsurj]
  have hbot := hexp2 (E ⧸ Z₁) π' hπ'surj hπ'z hπ'2 hperf'
  have hex : ∃ e : ↥π.ker, e ∉ K := by
    by_contra h
    have hK' : K = ⊤ := eq_top_iff.mpr fun e _ => by_contra fun hn => h ⟨e, hn⟩
    rw [hK', Subgroup.card_top, hm] at hK
    have : 2 ^ m = 2 ^ (m - 1) := hK
    have h2 := Nat.pow_right_injective (le_refl 2) this
    omega
  obtain ⟨e, he⟩ := hex
  have hmem : (QuotientGroup.mk (e : E) : E ⧸ Z₁) ∈ π'.ker := by
    rw [MonoidHom.mem_ker]
    exact e.2
  rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
  obtain ⟨k, hk, hke⟩ := hmem
  apply he
  have : k = e := Subtype.ext hke
  rw [← this]
  exact hk

end Reduction

end CFSG.QuasithinUnique.Vol2Native.L239.Covers
