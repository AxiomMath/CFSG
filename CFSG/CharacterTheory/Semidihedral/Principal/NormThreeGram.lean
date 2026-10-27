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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Semidihedral.Principal

open Finset

namespace NormThreeGram

theorem int_cases_of_mul_self_le_two {z : ℤ} (h : z * z ≤ 2) : z = -1 ∨ z = 0 ∨ z = 1 := by
  have h1 : -1 ≤ z := by nlinarith
  have h2 : z ≤ 1 := by nlinarith
  omega

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
theorem sum_mul_of_support_pair (f u : X → ℤ) {p q : X} (hpq : p ≠ q)
    (hu : ∀ x, u x ≠ 0 → x = p ∨ x = q) : ∑ x, f x * u x = f p * u p + f q * u q := by
  refine Fintype.sum_eq_add p q hpq fun x hx => ?_
  have hux : u x = 0 := by
    by_contra h
    rcases hu x h with h' | h'
    · exact hx.1 h'
    · exact hx.2 h'
  rw [hux, mul_zero]

omit [DecidableEq X] in
theorem support_card_of_norm_two (u : X → ℤ) (hu : ∀ x, u x = -1 ∨ u x = 0 ∨ u x = 1)
    (hnorm : ∑ x, u x * u x = 2) : (univ.filter (fun x => u x ≠ 0)).card = 2 := by
  have hcard : ((univ.filter (fun x => u x ≠ 0)).card : ℤ) = ∑ x, u x * u x := by
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rcases hu x with h | h | h <;> simp [h]
  omega

theorem exists_other_of_support_card_two (u : X → ℤ)
    (hcard : (univ.filter (fun x => u x ≠ 0)).card = 2) {a : X} (ha : u a ≠ 0) :
    ∃ b, b ≠ a ∧ u b ≠ 0 ∧ ∀ x, u x ≠ 0 → x = a ∨ x = b := by
  obtain ⟨p, q, hpq, hS⟩ := Finset.card_eq_two.mp hcard
  have hmem : ∀ x, u x ≠ 0 ↔ x = p ∨ x = q := by
    intro x
    have h := congrArg (fun s : Finset X => x ∈ s) hS
    simpa using h
  rcases (hmem a).mp ha with rfl | rfl
  · exact ⟨q, hpq.symm, (hmem q).mpr (Or.inr rfl), fun x hx => (hmem x).mp hx⟩
  · refine ⟨p, hpq, (hmem p).mpr (Or.inl rfl), fun x hx => ?_⟩
    rcases (hmem x).mp hx with h | h
    · exact Or.inr h
    · exact Or.inl h

theorem unique_common_of_inner_eq_one (u w : X → ℤ) (hu : ∀ x, u x = -1 ∨ u x = 0 ∨ u x = 1)
    (hw : ∀ x, w x = -1 ∨ w x = 0 ∨ w x = 1)
    (hcard : (univ.filter (fun x => u x ≠ 0)).card = 2) (hinner : ∑ x, u x * w x = 1) :
    ∃ a, u a ≠ 0 ∧ w a ≠ 0 ∧ u a = w a ∧ ∀ x, u x ≠ 0 → w x ≠ 0 → x = a := by
  set T := univ.filter (fun x => u x ≠ 0 ∧ w x ≠ 0) with hT
  have hmemT : ∀ x, x ∈ T ↔ u x ≠ 0 ∧ w x ≠ 0 := fun x => by simp [hT]
  have hsum : ∑ x ∈ T, u x * w x = 1 := by
    rw [← hinner]
    refine Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_
    rw [hmemT, not_and_or, not_not, not_not] at hx
    rcases hx with h | h <;> simp [h]
  have hprod : ∀ x ∈ T, u x * w x = 1 ∨ u x * w x = -1 := by
    intro x hx
    obtain ⟨hux, hwx⟩ := (hmemT x).mp hx
    rcases hu x with h | h | h <;> rcases hw x with h' | h' | h' <;> simp_all
  have hTcard : T.card ≤ 2 := by
    rw [← hcard]
    exact Finset.card_le_card fun x hx => by simpa using ((hmemT x).mp hx).1
  rcases (show T.card = 0 ∨ T.card = 1 ∨ T.card = 2 by omega) with h0 | h1 | h2
  · rw [Finset.card_eq_zero.mp h0, Finset.sum_empty] at hsum
    omega
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
    have haT : a ∈ T := ha ▸ Finset.mem_singleton_self a
    rw [ha, Finset.sum_singleton] at hsum
    obtain ⟨hua, hwa⟩ := (hmemT a).mp haT
    refine ⟨a, hua, hwa, ?_, fun x hx hx' => ?_⟩
    · rcases hu a with h | h | h <;> rcases hw a with h' | h' | h' <;> simp_all
    · have hxT : x ∈ T := (hmemT x).mpr ⟨hx, hx'⟩
      rw [ha] at hxT
      exact Finset.mem_singleton.mp hxT
  · obtain ⟨p, q, hpq, hpqT⟩ := Finset.card_eq_two.mp h2
    have hp : p ∈ T := hpqT ▸ by simp
    have hq : q ∈ T := hpqT ▸ by simp
    rw [hpqT, Finset.sum_pair hpq] at hsum
    have := hprod p hp
    have := hprod q hq
    omega

end NormThreeGram

open NormThreeGram

theorem integral_norm_three_degree_zero_gram_family_common_coordinate
    {X I : Type*} [Fintype X] [DecidableEq X] [Fintype I] (hI : 2 ≤ Fintype.card I)
    (o : X) (d : X → ℤ) (hd : ∀ x, 0 < d x) (hdo : d o = 1) (v : I → X → ℤ)
    (hvo : ∀ i, v i o = 1) (hnorm : ∀ i, ∑ x, v i x ^ 2 = 3)
    (hdeg : ∀ i, ∑ x, d x * v i x = 0)
    (hgram : ∀ i j, i ≠ j → ∑ x, v i x * v j x = 2) :
    ∃ a : X, a ≠ o ∧ ∃ b : I → X, Function.Injective b ∧ (∀ i, b i ≠ o ∧ b i ≠ a) ∧
      ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧ ∀ i,
        v i = Pi.single o 1 + δ • Pi.single a 1 - δ • Pi.single (b i) 1 ∧
        d (b i) = d a + δ ∧ 0 < d a + δ ∧
        ∀ x, v i x ≠ 0 ↔ x = o ∨ x = a ∨ x = b i := by
  let u : I → X → ℤ := fun i x => if x = o then 0 else v i x
  have huo : ∀ i, u i o = 0 := fun i => by simp [u]
  have huv : ∀ i x, x ≠ o → u i x = v i x := fun i x hx => by simp [u, hx]
  have hprod : ∀ i j x, v i x * v j x = u i x * u j x + (Pi.single o (1 : ℤ) : X → ℤ) x := by
    intro i j x
    by_cases hx : x = o
    · subst hx
      simp [huo, hvo]
    · simp [huv i x hx, huv j x hx, hx]
  have hinner : ∀ i j, ∑ x, v i x * v j x = ∑ x, u i x * u j x + 1 := by
    intro i j
    rw [Finset.sum_congr rfl fun x _ => hprod i j x, Finset.sum_add_distrib,
      Finset.sum_pi_single']
    simp
  have hunorm : ∀ i, ∑ x, u i x * u i x = 2 := by
    intro i
    have h := hinner i i
    simp only [← sq] at h
    rw [hnorm i] at h
    simp only [sq] at h ⊢
    omega
  have huinner : ∀ i j, i ≠ j → ∑ x, u i x * u j x = 1 := by
    intro i j hij
    have h := hinner i j
    rw [hgram i j hij] at h
    omega
  have hudeg : ∀ i, ∑ x, d x * u i x = -1 := by
    intro i
    have hsplit : ∀ x, d x * v i x = d x * u i x + d x * (Pi.single o (1 : ℤ) : X → ℤ) x := by
      intro x
      by_cases hx : x = o
      · subst hx
        simp [huo, hvo]
      · simp [huv i x hx, hx]
    have h := hdeg i
    rw [Finset.sum_congr rfl fun x _ => hsplit x, Finset.sum_add_distrib] at h
    have h' : ∑ x, d x * (Pi.single o (1 : ℤ) : X → ℤ) x = 1 := by
      rw [Fintype.sum_eq_single o fun x hx => by simp [hx], Pi.single_eq_same, mul_one, hdo]
    omega
  have hvals : ∀ i x, u i x = -1 ∨ u i x = 0 ∨ u i x = 1 := by
    intro i x
    apply int_cases_of_mul_self_le_two
    rw [← hunorm i]
    exact Finset.single_le_sum (f := fun y => u i y * u i y)
      (fun y _ => mul_self_nonneg (u i y)) (Finset.mem_univ x)
  have hcard : ∀ i, (univ.filter (fun x => u i x ≠ 0)).card = 2 :=
    fun i => support_card_of_norm_two (u i) (hvals i) (hunorm i)
  have hcommon : ∀ i j, i ≠ j → ∃ a, u i a ≠ 0 ∧ u j a ≠ 0 ∧ u i a = u j a ∧
      ∀ x, u i x ≠ 0 → u j x ≠ 0 → x = a :=
    fun i j hij => unique_common_of_inner_eq_one (u i) (u j) (hvals i) (hvals j) (hcard i)
      (huinner i j hij)
  obtain ⟨i₀, i₁, hi⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card I)
  obtain ⟨a, ha₀, ha₁, ha₀₁, hauniq⟩ := hcommon i₀ i₁ hi
  have hall : ∀ k, u k a ≠ 0 := by
    intro k hka
    obtain ⟨b₀, hb₀a, hb₀, hb₀supp⟩ := exists_other_of_support_card_two (u i₀) (hcard i₀) ha₀
    obtain ⟨c₁, hc₁a, hc₁, hc₁supp⟩ := exists_other_of_support_card_two (u i₁) (hcard i₁) ha₁
    have hk₀ : k ≠ i₀ := fun h => ha₀ (h ▸ hka)
    have hk₁ : k ≠ i₁ := fun h => ha₁ (h ▸ hka)
    obtain ⟨y, hky, hy₀, hky₀, -⟩ := hcommon k i₀ hk₀
    obtain ⟨z, hkz, hz₁, hkz₁, -⟩ := hcommon k i₁ hk₁
    have hyb : y = b₀ := by
      rcases hb₀supp y hy₀ with h | h
      · exact (hky (by rw [h]; exact hka)).elim
      · exact h
    have hzc : z = c₁ := by
      rcases hc₁supp z hz₁ with h | h
      · exact (hkz (by rw [h]; exact hka)).elim
      · exact h
    subst hyb hzc
    have hbc : y ≠ z := by
      intro h
      exact hb₀a (hauniq y hy₀ (h ▸ hz₁))
    have hksupp : ∀ x, u k x ≠ 0 → x = y ∨ x = z := by
      obtain ⟨w, hwy, hw, hwsupp⟩ := exists_other_of_support_card_two (u k) (hcard k) hky
      rcases hwsupp z hkz with h | h
      · exact absurd h.symm hbc
      · subst h
        exact hwsupp
    have hd₀ := hudeg i₀
    have hd₁ := hudeg i₁
    have hdk := hudeg k
    rw [sum_mul_of_support_pair d (u i₀) hb₀a.symm hb₀supp] at hd₀
    rw [sum_mul_of_support_pair d (u i₁) hc₁a.symm hc₁supp] at hd₁
    rw [sum_mul_of_support_pair d (u k) hbc hksupp] at hdk
    rw [← ha₀₁] at hd₁
    rw [hky₀, hkz₁] at hdk
    omega
  have hother : ∀ k, ∃ b, b ≠ a ∧ u k b ≠ 0 ∧ ∀ x, u k x ≠ 0 → x = a ∨ x = b :=
    fun k => exists_other_of_support_card_two (u k) (hcard k) (hall k)
  choose b hba hb hbsupp using hother
  have hao : a ≠ o := fun h => ha₀ (h ▸ huo i₀)
  have hbo : ∀ k, b k ≠ o := fun k h => hb k (h ▸ huo k)
  have hbinj : Function.Injective b := by
    intro k l hkl
    by_contra hne
    obtain ⟨y, -, -, -, hyuniq⟩ := hcommon k l hne
    have hya : a = y := hyuniq a (hall k) (hall l)
    have hyb : b k = y := hyuniq (b k) (hb k) (hkl ▸ hb l)
    exact hba k (hyb.trans hya.symm)
  set δ := u i₀ a with hδ
  have hδk : ∀ k, u k a = δ := by
    intro k
    by_cases hk : k = i₀
    · rw [hk]
    · obtain ⟨y, -, -, hyeq, hyuniq⟩ := hcommon k i₀ hk
      have hya : a = y := hyuniq a (hall k) (hall i₀)
      rw [hya, hyeq]
      exact congrArg (u i₀) hya.symm
  have hδsign : δ = 1 ∨ δ = -1 := by
    rcases hvals i₀ a with h | h | h
    · exact Or.inr h
    · exact absurd h ha₀
    · exact Or.inl h
  have hεk : ∀ k, u k (b k) = -δ ∧ d (b k) = d a + δ := by
    intro k
    have hdk := hudeg k
    rw [sum_mul_of_support_pair d (u k) (hba k).symm (hbsupp k), hδk k] at hdk
    have hda := hd a
    have hdb := hd (b k)
    rcases hvals k (b k) with h | h | h
    · rw [h] at hdk ⊢
      rcases hδsign with h' | h' <;> rw [h'] at hdk ⊢ <;> omega
    · exact absurd h (hb k)
    · rw [h] at hdk ⊢
      rcases hδsign with h' | h' <;> rw [h'] at hdk ⊢ <;> omega
  refine ⟨a, hao, b, hbinj, fun k => ⟨hbo k, hba k⟩, δ, hδsign, fun k => ?_⟩
  have hvx : ∀ x, v k x = (Pi.single o (1 : ℤ) : X → ℤ) x + δ * (Pi.single a (1 : ℤ) : X → ℤ) x -
      δ * (Pi.single (b k) (1 : ℤ) : X → ℤ) x := by
    intro x
    by_cases hxo : x = o
    · subst hxo
      simp [hvo, hao.symm, (hbo k).symm]
    · rw [← huv k x hxo]
      by_cases hxa : x = a
      · subst hxa
        simp [hδk k, hxo, (hba k).symm]
      · by_cases hxb : x = b k
        · subst hxb
          simp [(hεk k).1, hxo, hxa]
        · have hux : u k x = 0 := by
            by_contra h
            rcases hbsupp k x h with h' | h'
            · exact hxa h'
            · exact hxb h'
          simp [hux, hxo, hxa, hxb]
  refine ⟨funext fun x => by simpa using hvx x, (hεk k).2, (hεk k).2 ▸ hd (b k), fun x => ?_⟩
  rw [hvx x]
  by_cases hxo : x = o
  · subst hxo
    simp [hao.symm, (hbo k).symm]
  · by_cases hxa : x = a
    · subst hxa
      rcases hδsign with h | h <;> simp [h, hxo, (hba k).symm]
    · by_cases hxb : x = b k
      · subst hxb
        rcases hδsign with h | h <;> simp [h, hxo, hxa]
      · simp [hxo, hxa, hxb]

end CFSG.Semidihedral.Principal
