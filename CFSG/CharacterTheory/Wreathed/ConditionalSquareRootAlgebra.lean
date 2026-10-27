module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.CStarAlgebra.Classes
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

open scoped BigOperators ComplexConjugate

namespace CFSG.Wreathed.ConditionalSquareRoot

theorem odd_phase_sum {ζ : ℂ} {M₀ : ℕ} (hζ : IsPrimitiveRoot ζ (2 * M₀)) {r t : ℕ}
    (hr : r < M₀) (ht : t < M₀) :
    ∑ i ∈ Finset.range M₀, ζ⁻¹ ^ (r * (2 * i + 1)) * ζ ^ (t * (2 * i + 1)) =
      if r = t then (M₀ : ℂ) else 0 := by
  have hM : 0 < 2 * M₀ := by omega
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  set u := ζ⁻¹ ^ r * ζ ^ t with hu
  have hterm : ∀ i : ℕ, ζ⁻¹ ^ (r * (2 * i + 1)) * ζ ^ (t * (2 * i + 1)) = u * (u ^ 2) ^ i := by
    intro i
    rw [← pow_mul, ← pow_succ', hu, mul_pow, ← pow_mul, ← pow_mul]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum]
  split_ifs with hrt
  · subst hrt
    have hu1 : u = 1 := by rw [hu, ← mul_pow, inv_mul_cancel₀ hζ0, one_pow]
    simp [hu1]
  · have hz : ζ ^ (2 * M₀) = 1 := hζ.pow_eq_one
    have hu2m : (u ^ 2) ^ M₀ = 1 := by
      have h1 : (ζ⁻¹ ^ r) ^ (2 * M₀) = 1 := by
        rw [← pow_mul, mul_comm, pow_mul ζ⁻¹ (2 * M₀) r, inv_pow, hz, inv_one, one_pow]
      have h2 : (ζ ^ t) ^ (2 * M₀) = 1 := by
        rw [← pow_mul, mul_comm, pow_mul ζ (2 * M₀) t, hz, one_pow]
      rw [← pow_mul, hu, mul_pow, h1, h2, one_mul]
    have hu21 : u ^ 2 ≠ 1 := by
      intro h
      have hsq : IsPrimitiveRoot (ζ ^ 2) M₀ := hζ.pow hM rfl
      have h' : (ζ ^ 2) ^ t = (ζ ^ 2) ^ r := by
        rw [hu, mul_pow, ← pow_mul, ← pow_mul, inv_pow] at h
        rw [← pow_mul, ← pow_mul, mul_comm 2 t, mul_comm 2 r]
        have h2 := congrArg (· * ζ ^ (r * 2)) h
        simp only [one_mul] at h2
        rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hζ0), one_mul] at h2
        exact h2
      exact hrt (hsq.pow_inj ht hr h').symm
    have hgeom : ∑ i ∈ Finset.range M₀, (u ^ 2) ^ i = 0 := by
      have h := geom_sum_mul (u ^ 2) M₀
      rw [hu2m, sub_self] at h
      exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hu21)
    rw [hgeom, mul_zero]

theorem coefficient_gram_of_odd_columns {ι : Type*} (B : Finset ι) {ζ : ℂ} {M₀ : ℕ}
    (hζ : IsPrimitiveRoot ζ (2 * M₀)) (w : ι → ℕ → ℂ) (c : ι → ℕ → ℤ)
    (hinv : ∀ χ ∈ B, ∀ r < M₀, (c χ r : ℂ) =
      (M₀ : ℂ)⁻¹ * ∑ i ∈ Finset.range M₀, ζ⁻¹ ^ (r * (2 * i + 1)) * w χ i)
    (hgram : ∀ i < M₀, ∀ i' < M₀,
      ∑ χ ∈ B, w χ i * conj (w χ i') = if i = i' then (4 * M₀ : ℂ) else 0)
    {r t : ℕ} (hr : r < M₀) (ht : t < M₀) :
    ∑ χ ∈ B, c χ r * c χ t = if r = t then 4 else 0 := by
  have hM₀ : (M₀ : ℂ) ≠ 0 := by exact_mod_cast (show M₀ ≠ 0 by omega)
  have hnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one (by omega)
  have hconjinv : conj ζ⁻¹ = ζ := by rw [Complex.inv_eq_conj hnorm, Complex.conj_conj]
  apply Int.cast_injective (α := ℂ)
  push_cast
  have hct : ∀ χ ∈ B, (c χ t : ℂ) = conj (c χ t : ℂ) := fun χ _ => (map_intCast _ _).symm
  calc ∑ χ ∈ B, (c χ r : ℂ) * (c χ t : ℂ)
      = ∑ χ ∈ B, ((M₀ : ℂ)⁻¹ * ∑ i ∈ Finset.range M₀, ζ⁻¹ ^ (r * (2 * i + 1)) * w χ i) *
          conj ((M₀ : ℂ)⁻¹ * ∑ i ∈ Finset.range M₀, ζ⁻¹ ^ (t * (2 * i + 1)) * w χ i) := by
        refine Finset.sum_congr rfl fun χ hχ => ?_
        rw [hct χ hχ, hinv χ hχ r hr, hinv χ hχ t ht]
    _ = ∑ χ ∈ B, ∑ i ∈ Finset.range M₀, ∑ i' ∈ Finset.range M₀, (M₀ : ℂ)⁻¹ * (M₀ : ℂ)⁻¹ *
          (ζ⁻¹ ^ (r * (2 * i + 1)) * ζ ^ (t * (2 * i' + 1)) * (w χ i * conj (w χ i'))) := by
        refine Finset.sum_congr rfl fun χ _ => ?_
        simp only [map_mul, map_sum, map_inv₀, map_natCast, map_pow, hconjinv]
        rw [mul_mul_mul_comm, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i' _ => ?_
        ring
    _ = (M₀ : ℂ)⁻¹ * (M₀ : ℂ)⁻¹ * ∑ i ∈ Finset.range M₀, ∑ i' ∈ Finset.range M₀,
          ζ⁻¹ ^ (r * (2 * i + 1)) * ζ ^ (t * (2 * i' + 1)) *
            ∑ χ ∈ B, w χ i * conj (w χ i') := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i' _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
    _ = (M₀ : ℂ)⁻¹ * (M₀ : ℂ)⁻¹ * ((4 * M₀ : ℂ) *
          ∑ i ∈ Finset.range M₀, ζ⁻¹ ^ (r * (2 * i + 1)) * ζ ^ (t * (2 * i + 1))) := by
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.sum_eq_single i]
        · rw [hgram i (Finset.mem_range.mp hi) i (Finset.mem_range.mp hi), ite_eq_left rfl]
          ring
        · intro i' hi' hne
          rw [hgram i (Finset.mem_range.mp hi) i' (Finset.mem_range.mp hi'),
            ite_eq_right (Ne.symm hne), mul_zero]
        · intro h
          exact absurd hi h
    _ = if r = t then 4 else 0 := by
        rw [odd_phase_sum hζ hr ht]
        split_ifs
        · field_simp
        · simp

theorem four_units_of_sq_sum_four {ι : Type*} [DecidableEq ι] (B : Finset ι) (c d : ι → ℤ)
    (hd : ∀ χ ∈ B, 0 < d χ) (hsq : ∑ χ ∈ B, c χ * c χ = 4) (hdeg : ∑ χ ∈ B, c χ * d χ = 0) :
    (B.filter (fun χ => c χ ≠ 0)).card = 4 ∧ ∀ χ ∈ B, c χ = 0 ∨ c χ = 1 ∨ c χ = -1 := by
  have hle : ∀ χ ∈ B, c χ * c χ ≤ 4 := by
    intro χ hχ
    rw [← hsq]
    exact Finset.single_le_sum (f := fun χ => c χ * c χ) (fun χ _ => mul_self_nonneg _) hχ
  have hunit : ∀ χ ∈ B, c χ = 0 ∨ c χ = 1 ∨ c χ = -1 := by
    intro χ hχ
    have h4 := hle χ hχ
    have h1 : -2 ≤ c χ := by nlinarith
    have h2 : c χ ≤ 2 := by nlinarith
    by_contra hne
    push Not at hne
    have htwo : c χ = 2 ∨ c χ = -2 := by omega
    have hrest : ∀ ψ ∈ B, ψ ≠ χ → c ψ = 0 := by
      intro ψ hψ hψχ
      have hsplit := Finset.add_sum_erase B (fun χ => c χ * c χ) hχ
      rw [hsq] at hsplit
      have hχsq : c χ * c χ = 4 := by rcases htwo with h | h <;> rw [h] <;> norm_num
      have hzero : ∑ x ∈ B.erase χ, c x * c x = 0 := by linarith
      have hψ' : ψ ∈ B.erase χ := Finset.mem_erase.mpr ⟨hψχ, hψ⟩
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => mul_self_nonneg (c x))).mp hzero ψ hψ'
      exact mul_self_eq_zero.mp this
    have hdeg' : c χ * d χ = 0 := by
      rw [← hdeg, Finset.sum_eq_single χ]
      · intro ψ hψ hψχ
        rw [hrest ψ hψ hψχ, zero_mul]
      · intro h
        exact absurd hχ h
    have hdχ := hd χ hχ
    rcases htwo with h | h <;> rw [h] at hdeg' <;> omega
  refine ⟨?_, hunit⟩
  have hcount : ∑ χ ∈ B, c χ * c χ = ((B.filter (fun χ => c χ ≠ 0)).card : ℤ) := by
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rcases hunit χ hχ with h | h | h <;> simp [h]
  rw [hsq] at hcount
  exact_mod_cast hcount.symm

theorem card_orthogonal_le_three {ι κ : Type*} [DecidableEq ι] (T : Finset ι) (hT : T.card = 4)
    (d : ι → ℤ) (hd : ∀ χ ∈ T, 0 < d χ) (R : Finset κ) (v : κ → ι → ℤ)
    (hnz : ∀ r ∈ R, ∃ χ ∈ T, v r χ ≠ 0)
    (horth : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → ∑ χ ∈ T, v r χ * v r' χ = 0)
    (hdeg : ∀ r ∈ R, ∑ χ ∈ T, v r χ * d χ = 0) :
    R.card ≤ 3 := by
  classical
  let E := EuclideanSpace ℝ T
  let toE : (ι → ℤ) → E := fun f => WithLp.toLp 2 (fun χ : T => (f χ : ℝ))
  have hinner : ∀ f g : ι → ℤ, inner ℝ (toE f) (toE g) = ((∑ χ ∈ T, f χ * g χ : ℤ) : ℝ) := by
    intro f g
    simp only [toE, Int.cast_sum, Int.cast_mul]
    rw [← Finset.sum_coe_sort T]
    refine Finset.sum_congr rfl fun χ _ => ?_
    change (g χ : ℝ) * (f χ : ℝ) = (f χ : ℝ) * (g χ : ℝ)
    ring
  let fam : Option R → E := fun o => match o with
    | none => toE d
    | some r => toE (v r)
  have hne0 : ∀ o, fam o ≠ 0 := by
    intro o h
    have hself : inner ℝ (fam o) (fam o) = 0 := by rw [h, inner_zero_left]
    match o with
    | none =>
      change inner ℝ (toE d) (toE d) = 0 at hself
      rw [hinner] at hself
      have hpos : 0 < ∑ χ ∈ T, d χ * d χ := by
        have hne : T.Nonempty := Finset.card_pos.mp (by omega)
        exact Finset.sum_pos (fun χ hχ => mul_pos (hd χ hχ) (hd χ hχ)) hne
      have : ((∑ χ ∈ T, d χ * d χ : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
      exact this hself
    | some r =>
      change inner ℝ (toE (v r)) (toE (v r)) = 0 at hself
      rw [hinner] at hself
      have hzero : ∑ χ ∈ T, v r χ * v r χ = 0 := by exact_mod_cast hself
      obtain ⟨χ, hχ, hv⟩ := hnz r r.2
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => mul_self_nonneg (v r x))).mp
        hzero χ hχ
      exact hv (mul_self_eq_zero.mp this)
  have hpair : Pairwise fun o o' => inner ℝ (fam o) (fam o') = 0 := by
    intro o o' hoo'
    match o, o' with
    | none, none => exact absurd rfl hoo'
    | none, some r =>
      change inner ℝ (toE d) (toE (v r)) = 0
      rw [hinner]
      have h := hdeg r r.2
      rw [Finset.sum_congr rfl fun χ _ => mul_comm (d χ) (v r χ), h]
      simp
    | some r, none =>
      change inner ℝ (toE (v r)) (toE d) = 0
      rw [hinner, hdeg r r.2]
      simp
    | some r, some r' =>
      change inner ℝ (toE (v r)) (toE (v r')) = 0
      rw [hinner, horth r r.2 r' r'.2 (fun h => hoo' (congrArg some (Subtype.ext h)))]
      simp
  have hli : LinearIndependent ℝ fam := linearIndependent_of_ne_zero_of_inner_eq_zero hne0 hpair
  have hcard := hli.fintype_card_le_finrank
  rw [finrank_euclideanSpace, Fintype.card_option, Fintype.card_coe, Fintype.card_coe, hT] at hcard
  omega

end CFSG.Wreathed.ConditionalSquareRoot

namespace CFSG.Wreathed.ConditionalSquareRoot

theorem modEq_two_iff_of_units {u v : ℤ} (hu : u = 0 ∨ u = 1 ∨ u = -1)
    (hv : v = 0 ∨ v = 1 ∨ v = -1) : u ≡ v [ZMOD 2] ↔ (u ≠ 0 ↔ v ≠ 0) := by
  unfold Int.ModEq
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;> decide

theorem card_filter_odd_Ico (M₀ : ℕ) : ((Finset.Ico 1 (2 * M₀)).filter Odd).card = M₀ := by
  have h : (Finset.Ico 1 (2 * M₀)).filter Odd =
      (Finset.range M₀).image (fun i => 2 * i + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨i, rfl⟩⟩
      exact ⟨i, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨by omega, by omega⟩, ⟨i, rfl⟩⟩
  rw [h, Finset.card_image_of_injective _ (fun a b hab => by omega), Finset.card_range]

theorem parity_classes {ι : Type*} [DecidableEq ι] (B : Finset ι) {M₀ : ℕ}
    (c : ι → ℕ → ℤ) (d : ι → ℤ) (hd : ∀ χ ∈ B, 0 < d χ)
    (hgram : ∀ r < M₀, ∀ t < M₀, ∑ χ ∈ B, c χ r * c χ t = if r = t then 4 else 0)
    (hdeg : ∀ r < M₀, ∑ χ ∈ B, c χ r * d χ = 0)
    (hunit : ∀ r < M₀, (B.filter (fun χ => c χ r ≠ 0)).card = 4 ∧
      ∀ χ ∈ B, c χ r = 0 ∨ c χ r = 1 ∨ c χ r = -1)
    (X : ι → ℕ → ℤ)
    (hodd : ∀ j ∈ Finset.Ico 1 (2 * M₀), Odd j → ∀ χ ∈ B, X χ j ≡ c χ 0 [ZMOD 2])
    (heven : ∀ j ∈ Finset.Ico 1 (2 * M₀), Even j →
      ∀ χ ∈ B, X χ j ≡ c χ 0 + c χ (M₀ - j / 2) [ZMOD 2]) :
    (∀ j ∈ Finset.Ico 1 (2 * M₀), Odd j →
      (Finset.Ico 1 (2 * M₀)).filter (fun j' => ∀ χ ∈ B, X χ j' ≡ X χ j [ZMOD 2]) =
        (Finset.Ico 1 (2 * M₀)).filter Odd) ∧
    ((Finset.Ico 1 (2 * M₀)).filter Odd).card = M₀ ∧
    (∀ j ∈ Finset.Ico 1 (2 * M₀), Even j → ∀ j' ∈ Finset.Ico 1 (2 * M₀), Even j' →
      ((∀ χ ∈ B, X χ j ≡ X χ j' [ZMOD 2]) ↔
        B.filter (fun χ => c χ (M₀ - j / 2) ≠ 0) = B.filter (fun χ => c χ (M₀ - j' / 2) ≠ 0))) ∧
    ∀ j ∈ Finset.Ico 1 (2 * M₀), Even j →
      ((Finset.Ico 1 (2 * M₀)).filter (fun j' => ∀ χ ∈ B, X χ j' ≡ X χ j [ZMOD 2])).card ≤ 3 := by
  have hr : ∀ j ∈ Finset.Ico 1 (2 * M₀), Even j → 1 ≤ M₀ - j / 2 ∧ M₀ - j / 2 < M₀ := by
    intro j hj hje
    rw [Finset.mem_Ico] at hj
    obtain ⟨k, rfl⟩ := hje
    omega
  have hnz : ∀ r < M₀, ¬ ∀ χ ∈ B, c χ r ≡ 0 [ZMOD 2] := by
    intro r hrM h
    have hne : (B.filter (fun χ => c χ r ≠ 0)).Nonempty := by
      rw [← Finset.card_pos, (hunit r hrM).1]
      norm_num
    obtain ⟨χ, hχ⟩ := hne
    rw [Finset.mem_filter] at hχ
    have h1 := h χ hχ.1
    have h2 := (hunit r hrM).2 χ hχ.1
    rw [modEq_two_iff_of_units h2 (Or.inl rfl)] at h1
    exact h1.mp hχ.2 rfl
  have hsupp : ∀ r < M₀, ∀ t < M₀, (∀ χ ∈ B, c χ r ≡ c χ t [ZMOD 2]) ↔
      B.filter (fun χ => c χ r ≠ 0) = B.filter (fun χ => c χ t ≠ 0) := by
    intro r hrM t htM
    constructor
    · intro h
      ext χ
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hχ, hc⟩
        exact ⟨hχ, ((modEq_two_iff_of_units ((hunit r hrM).2 χ hχ)
          ((hunit t htM).2 χ hχ)).mp (h χ hχ)).mp hc⟩
      · rintro ⟨hχ, hc⟩
        exact ⟨hχ, ((modEq_two_iff_of_units ((hunit r hrM).2 χ hχ)
          ((hunit t htM).2 χ hχ)).mp (h χ hχ)).mpr hc⟩
    · intro h χ hχ
      rw [modEq_two_iff_of_units ((hunit r hrM).2 χ hχ) ((hunit t htM).2 χ hχ)]
      have h1 := congrArg (χ ∈ ·) h
      simp only [Finset.mem_filter, eq_iff_iff] at h1
      constructor
      · intro hc
        exact (h1.mp ⟨hχ, hc⟩).2
      · intro hc
        exact (h1.mpr ⟨hχ, hc⟩).2
  have hoddeven : ∀ j ∈ Finset.Ico 1 (2 * M₀), Odd j → ∀ j' ∈ Finset.Ico 1 (2 * M₀), Even j' →
      ¬ ∀ χ ∈ B, X χ j' ≡ X χ j [ZMOD 2] := by
    intro j hj hjo j' hj' hje h
    apply hnz _ (hr j' hj' hje).2
    intro χ hχ
    have h1 := heven j' hj' hje χ hχ
    have h2 := hodd j hj hjo χ hχ
    have h3 := h χ hχ
    unfold Int.ModEq at h1 h2 h3 ⊢
    omega
  have heveniff : ∀ j ∈ Finset.Ico 1 (2 * M₀), Even j → ∀ j' ∈ Finset.Ico 1 (2 * M₀),
      Even j' → ((∀ χ ∈ B, X χ j ≡ X χ j' [ZMOD 2]) ↔
        B.filter (fun χ => c χ (M₀ - j / 2) ≠ 0) = B.filter (fun χ => c χ (M₀ - j' / 2) ≠ 0)) := by
    intro j hj hje j' hj' hje'
    rw [← hsupp _ (hr j hj hje).2 _ (hr j' hj' hje').2]
    constructor
    · intro h χ hχ
      have h1 := heven j hj hje χ hχ
      have h2 := heven j' hj' hje' χ hχ
      have h3 := h χ hχ
      unfold Int.ModEq at h1 h2 h3 ⊢
      omega
    · intro h χ hχ
      have h1 := heven j hj hje χ hχ
      have h2 := heven j' hj' hje' χ hχ
      have h3 := h χ hχ
      unfold Int.ModEq at h1 h2 h3 ⊢
      omega
  refine ⟨?_, card_filter_odd_Ico M₀, heveniff, ?_⟩
  · intro j hj hjo
    ext j'
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hj', h⟩
      refine ⟨hj', ?_⟩
      rcases Nat.even_or_odd j' with hje | hjo'
      · exact absurd h (hoddeven j hj hjo j' hj' hje)
      · exact hjo'
    · rintro ⟨hj', hjo'⟩
      refine ⟨hj', fun χ hχ => ?_⟩
      exact (hodd j' hj' hjo' χ hχ).trans (hodd j hj hjo χ hχ).symm
  · intro j hj hje
    set T := B.filter (fun χ => c χ (M₀ - j / 2) ≠ 0) with hT
    set R := (Finset.range M₀).filter (fun r => B.filter (fun χ => c χ r ≠ 0) = T) with hR
    have hRcard : R.card ≤ 3 := by
      have hTB : T ⊆ B := Finset.filter_subset _ _
      have hzero : ∀ r ∈ R, ∀ χ ∈ B, χ ∉ T → c χ r = 0 := by
        intro r hrR χ hχ hχT
        rw [hR, Finset.mem_filter] at hrR
        by_contra hc
        apply hχT
        rw [← hrR.2, Finset.mem_filter]
        exact ⟨hχ, hc⟩
      have hsumT : ∀ r ∈ R, ∀ f : ι → ℤ, ∑ χ ∈ T, c χ r * f χ = ∑ χ ∈ B, c χ r * f χ := by
        intro r hrR f
        refine Finset.sum_subset hTB fun χ hχ hχT => ?_
        rw [hzero r hrR χ hχ hχT, zero_mul]
      refine card_orthogonal_le_three T (hunit _ (hr j hj hje).2).1 d
        (fun χ hχ => hd χ (hTB hχ)) R (fun r χ => c χ r) ?_ ?_ ?_
      · intro r hrR
        have hrR' := hrR
        rw [hR, Finset.mem_filter, Finset.mem_range] at hrR'
        have hne : (B.filter (fun χ => c χ r ≠ 0)).Nonempty := by
          rw [← Finset.card_pos, (hunit r hrR'.1).1]
          norm_num
        obtain ⟨χ, hχ⟩ := hne
        refine ⟨χ, ?_, (Finset.mem_filter.mp hχ).2⟩
        rw [← hrR'.2]
        exact hχ
      · intro r hrR r' hr'R hne
        have hrM := (Finset.mem_range.mp (Finset.mem_filter.mp hrR).1)
        have hr'M := (Finset.mem_range.mp (Finset.mem_filter.mp hr'R).1)
        rw [hsumT r hrR (fun χ => c χ r'), hgram r hrM r' hr'M, ite_eq_right hne]
      · intro r hrR
        have hrM := (Finset.mem_range.mp (Finset.mem_filter.mp hrR).1)
        rw [hsumT r hrR d, hdeg r hrM]
    refine le_trans (Finset.card_le_card_of_injOn (fun j' => M₀ - j' / 2) ?_ ?_) hRcard
    · intro j' hj'
      rw [Finset.mem_coe, Finset.mem_filter] at hj'
      have hje' : Even j' := by
        rcases Nat.even_or_odd j' with h | h
        · exact h
        · exact absurd (fun χ hχ => (hj'.2 χ hχ).symm) (hoddeven j' hj'.1 h j hj hje)
      rw [Finset.mem_coe, hR, Finset.mem_filter, Finset.mem_range]
      refine ⟨(hr j' hj'.1 hje').2, ?_⟩
      rw [hT]
      exact (heveniff j' hj'.1 hje' j hj hje).mp hj'.2
    · intro j₁ hj₁ j₂ hj₂ heq
      rw [Finset.mem_coe, Finset.mem_filter] at hj₁ hj₂
      have he₁ : Even j₁ := by
        rcases Nat.even_or_odd j₁ with h | h
        · exact h
        · exact absurd (fun χ hχ => (hj₁.2 χ hχ).symm) (hoddeven j₁ hj₁.1 h j hj hje)
      have he₂ : Even j₂ := by
        rcases Nat.even_or_odd j₂ with h | h
        · exact h
        · exact absurd (fun χ hχ => (hj₂.2 χ hχ).symm) (hoddeven j₂ hj₂.1 h j hj hje)
      have h1 := hr j₁ hj₁.1 he₁
      have h2 := hr j₂ hj₂.1 he₂
      obtain ⟨k₁, rfl⟩ := he₁
      obtain ⟨k₂, rfl⟩ := he₂
      simp only at heq
      omega

end CFSG.Wreathed.ConditionalSquareRoot
