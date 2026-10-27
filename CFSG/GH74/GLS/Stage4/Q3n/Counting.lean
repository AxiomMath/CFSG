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
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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

namespace CFSG.GH74.GLS.Stage4.Q3n

open CommGroup

theorem card_fixedCharacters {Q : Type} [CommGroup Q] [Finite Q] (α : Q →* Q) :
    Nat.card {χ : Q →* ℂˣ // ∀ q, χ (α q) = χ q} = Nat.card {q : Q // α q = q} := by
  classical
  let f : Q →* Q :=
    MonoidHom.mk' (fun q => α q * q⁻¹) (by intro a b; simp [mul_comm, mul_left_comm, mul_assoc])
  have hf : ∀ q, f q = α q * q⁻¹ := fun q => rfl
  have h1 : Nat.card {χ : Q →* ℂˣ // ∀ q, χ (α q) = χ q} = Nat.card (Q ⧸ f.range) := by
    rw [← card_subgroupOrderIsoSubgroupMonoidHom ℂ f.range]
    refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
    intro χ
    rw [mem_subgroupOrderIsoSubgroupMonoidHom_iff]
    constructor
    · rintro h g ⟨q, rfl⟩
      rw [hf, map_mul, map_inv, h q, mul_inv_cancel]
    · intro h q
      have := h (f q) ⟨q, rfl⟩
      rw [hf, map_mul, map_inv, mul_inv_eq_one] at this
      exact this
  have h2 : Nat.card f.ker * Nat.card f.range = Nat.card Q := Subgroup.card_ker_mul_card_range f
  have h3 : Nat.card f.range * f.range.index = Nat.card Q := Subgroup.card_mul_index f.range
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have h4 : Nat.card f.ker = f.range.index := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [mul_comm, h2, h3]
  have h5 : Nat.card f.ker = Nat.card {q : Q // α q = q} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
    intro q
    rw [MonoidHom.mem_ker, hf, mul_inv_eq_one]
  rw [h1, ← h5, h4]
  rfl

theorem exists_pow_orderOf_prime {W : Type*} [Group W] {w : W} (hw0 : orderOf w ≠ 0)
    (hw : w ≠ 1) : ∃ n : ℕ, (orderOf (w ^ n)).Prime := by
  have h1 : orderOf w ≠ 1 := by simpa using hw
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
  refine ⟨orderOf w / p, ?_⟩
  rw [orderOf_pow_orderOf_div hw0 hpd]
  exact hp

theorem prime_dvd_twelve {p : ℕ} (hp : p.Prime) (h : p ∣ 12) : p = 2 ∨ p = 3 := by
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) h
  interval_cases p <;> first | (left; rfl) | (right; rfl) | (exfalso; revert hp h; decide)

theorem d12_card_central_or_order_three :
    (Finset.univ.filter (fun x : DihedralGroup 6 =>
      x = DihedralGroup.r 3 ∨ (x ^ 3 = 1 ∧ x ≠ 1))).card = 3 := by
  decide

theorem d12_card_noncentral_involutions :
    (Finset.univ.filter (fun x : DihedralGroup 6 =>
      x ^ 2 = 1 ∧ x ≠ 1 ∧ x ≠ DihedralGroup.r 3)).card = 6 := by
  decide

theorem exists_finset_card_of_equiv {W : Type*} (e : W ≃ DihedralGroup 6)
    (P : DihedralGroup 6 → Prop) [DecidablePred P] :
    ∃ T : Finset W, (∀ w, w ∈ T ↔ P (e w)) ∧ T.card = (Finset.univ.filter P).card :=
  ⟨(Finset.univ.filter P).map e.symm.toEmbedding, by intro w; simp, by simp⟩

theorem exists_regular_character
    {Q W : Type} [Group Q] [Finite Q] [Group W]
    (hcomm : ∀ x y : Q, x * y = y * x)
    (ρ : W →* MulAut Q) (e : W ≃* DihedralGroup 6) (w₀ : W) (hw₀ : e w₀ = DihedralGroup.r 3)
    (k : ℕ) (hk : 7 ≤ k) (hQ : Nat.card Q = k ^ 2)
    (hw₀fix : ∀ q : Q, ρ w₀ q = q → q = 1)
    (hord3 : ∀ w : W, orderOf w = 3 → ∀ q : Q, ρ w q = q → q = 1)
    (hinv : ∀ y : W, orderOf y = 2 → y ≠ w₀ → Nat.card {q : Q // ρ y q = q} ≤ k) :
    ∃ χ : Q →* ℂˣ, ∀ w : W, (∀ q : Q, χ (ρ w q) = χ q) → w = 1 := by
  classical
  let _ : CommGroup Q := { ‹Group Q› with mul_comm := hcomm }
  have hΛcard : Nat.card (Q →* ℂˣ) = k ^ 2 :=
    (card_monoidHom_of_hasEnoughRootsOfUnity Q ℂ).trans hQ
  have : Finite (Q →* ℂˣ) := Nat.finite_of_card_ne_zero (by rw [hΛcard]; positivity)
  let _ : Fintype (Q →* ℂˣ) := Fintype.ofFinite _
  let Fix : W → Finset (Q →* ℂˣ) := fun w =>
    Finset.univ.filter (fun χ => ∀ q, χ (ρ w q) = χ q)
  have hFix : ∀ w, (Fix w).card = Nat.card {q : Q // ρ w q = q} := by
    intro w
    have h := card_fixedCharacters (ρ w).toMonoidHom
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
    exact h
  have hmemFix : ∀ w χ, χ ∈ Fix w ↔ ∀ q, χ (ρ w q) = χ q := by
    intro w χ
    simp [Fix]
  have hFix1 : ∀ w, (w = w₀ ∨ (w ^ 3 = 1 ∧ w ≠ 1)) → (Fix w).card ≤ 1 := by
    intro w hw
    rw [hFix]
    have key : ∀ q, ρ w q = q → q = 1 := by
      rcases hw with rfl | ⟨h3, h1⟩
      · exact hw₀fix
      · exact hord3 w (orderOf_eq_prime h3 h1)
    have : Subsingleton {q : Q // ρ w q = q} :=
      ⟨fun a b => Subtype.ext (by rw [key a a.2, key b b.2])⟩
    exact Finite.card_le_one_iff_subsingleton.mpr this
  have hFixk : ∀ w, (w ^ 2 = 1 ∧ w ≠ 1 ∧ w ≠ w₀) → (Fix w).card ≤ k := by
    rintro w ⟨h2, h1, h0⟩
    rw [hFix]
    exact hinv w (orderOf_eq_prime h2 h1) h0
  obtain ⟨T₁, hT₁, hT₁c⟩ := exists_finset_card_of_equiv e.toEquiv
    (fun x => x = DihedralGroup.r 3 ∨ (x ^ 3 = 1 ∧ x ≠ 1))
  obtain ⟨T₂, hT₂, hT₂c⟩ := exists_finset_card_of_equiv e.toEquiv
    (fun x => x ^ 2 = 1 ∧ x ≠ 1 ∧ x ≠ DihedralGroup.r 3)
  rw [d12_card_central_or_order_three] at hT₁c
  rw [d12_card_noncentral_involutions] at hT₂c
  have hT₁' : ∀ w, w ∈ T₁ ↔ (w = w₀ ∨ (w ^ 3 = 1 ∧ w ≠ 1)) := by
    intro w
    rw [hT₁]
    simp [← hw₀, ← map_pow]
  have hT₂' : ∀ w, w ∈ T₂ ↔ (w ^ 2 = 1 ∧ w ≠ 1 ∧ w ≠ w₀) := by
    intro w
    rw [hT₂]
    simp [← hw₀, ← map_pow]
  have hBAD : (T₁.biUnion Fix ∪ T₂.biUnion Fix).card ≤ 3 + 6 * k := by
    calc (T₁.biUnion Fix ∪ T₂.biUnion Fix).card
        ≤ (T₁.biUnion Fix).card + (T₂.biUnion Fix).card := Finset.card_union_le _ _
      _ ≤ T₁.card * 1 + T₂.card * k :=
          Nat.add_le_add
            (Finset.card_biUnion_le_card_mul _ _ _ fun a ha => hFix1 a ((hT₁' a).1 ha))
            (Finset.card_biUnion_le_card_mul _ _ _ fun a ha => hFixk a ((hT₂' a).1 ha))
      _ = 3 + 6 * k := by simp [hT₁c, hT₂c]
  have hlt : (T₁.biUnion Fix ∪ T₂.biUnion Fix).card <
      (Finset.univ : Finset (Q →* ℂˣ)).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hΛcard]
    calc (T₁.biUnion Fix ∪ T₂.biUnion Fix).card ≤ 3 + 6 * k := hBAD
      _ < k ^ 2 := by nlinarith
  obtain ⟨χ, -, hχ⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨χ, fun w hw => ?_⟩
  by_contra hw1
  have hcardW : Nat.card W = 12 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have : Finite W := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨n, hn⟩ := exists_pow_orderOf_prime (orderOf_pos w).ne' hw1
  have hpow : ∀ n : ℕ, ∀ q, χ (ρ (w ^ n) q) = χ q := by
    intro n
    induction n with
    | zero => intro q; simp
    | succ n ih => intro q; rw [pow_succ, map_mul, MulAut.mul_apply, ih, hw]
  have h23 : orderOf (w ^ n) = 2 ∨ orderOf (w ^ n) = 3 :=
    prime_dvd_twelve hn (hcardW ▸ orderOf_dvd_natCard _)
  apply hχ
  rw [Finset.mem_union, Finset.mem_biUnion, Finset.mem_biUnion]
  rcases h23 with h2 | h3
  · have hv2 : (w ^ n) ^ 2 = 1 := h2 ▸ pow_orderOf_eq_one _
    have hv1 : w ^ n ≠ 1 := by
      intro h
      rw [h, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    by_cases h0 : w ^ n = w₀
    · exact Or.inl ⟨w ^ n, (hT₁' _).2 (Or.inl h0), (hmemFix _ _).2 (hpow n)⟩
    · exact Or.inr ⟨w ^ n, (hT₂' _).2 ⟨hv2, hv1, h0⟩, (hmemFix _ _).2 (hpow n)⟩
  · have hv3 : (w ^ n) ^ 3 = 1 := h3 ▸ pow_orderOf_eq_one _
    have hv1 : w ^ n ≠ 1 := by
      intro h
      rw [h, orderOf_one] at h3
      exact absurd h3 (by norm_num)
    exact Or.inl ⟨w ^ n, (hT₁' _).2 (Or.inr ⟨hv3, hv1⟩), (hmemFix _ _).2 (hpow n)⟩

end CFSG.GH74.GLS.Stage4.Q3n
