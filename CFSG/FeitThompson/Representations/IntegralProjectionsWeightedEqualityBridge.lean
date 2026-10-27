module

public import CFSG.FeitThompson.Definitions.WeightedSubcoherenceBlockData
import CFSG.FeitThompson.Representations.DisjointCoherentWeightedFamiliesOrthogonal
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality
import CFSG.FeitThompson.Representations.EqualDegreeDifferenceSaturatesAntirealBlocks
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
import CFSG.FeitThompson.Representations.DisjointAntirealBlocksOrthogonal
public import CFSG.FeitThompson.Representations.ConjugatePairsDisjointBlocksCoherence
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.ExteriorImageProportionalCentralCoefficients

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace WeightedEqualityBridge

open ComplexConjugate

section Projection

variable {G : Type*} [Fintype G] {ι : Type*} [DecidableEq ι] {A B : Finset ι}
  {η θ : ι → G → ℂ} {f : G → ℂ} {c g : ι → ℂ} {P : G → ℂ}

omit [DecidableEq ι] in
theorem cfInner_self_eq_add_of_cfInner_sub_eq_zero (h1 : cfInner (f - P) P = 0) :
    cfInner f f = cfInner P P + cfInner (f - P) (f - P) := by
  have h2 : cfInner P (f - P) = 0 := by rw [← conj_cfInner, h1, map_zero]
  have hs : P + (f - P) = f := add_sub_cancel _ _
  calc cfInner f f = cfInner (P + (f - P)) (P + (f - P)) := by rw [hs]
    _ = _ := by rw [cfInner_add_left, cfInner_add_right, cfInner_add_right, h1, h2]; ring

omit [DecidableEq ι] in
theorem cfInner_combination_eq_zero {u : G → ℂ}
    (h1 : ∀ i ∈ A, cfInner u (η i) = 0) (h2 : ∀ j ∈ B, cfInner u (θ j) = 0) :
    cfInner u ((∑ i ∈ A, c i • η i) + ∑ j ∈ B, g j • θ j) = 0 := by
  rw [cfInner_add_right, cfInner_sum_right, cfInner_sum_right,
    Finset.sum_eq_zero fun i hi => by rw [cfInner_smul_right, h1 i hi, mul_zero],
    Finset.sum_eq_zero fun j hj => by rw [cfInner_smul_right, h2 j hj, mul_zero], add_zero]

variable (hηη : ∀ i ∈ A, ∀ j ∈ A, cfInner (η i) (η j) = if i = j then 1 else 0)
  (hθθ : ∀ i ∈ B, ∀ j ∈ B, cfInner (θ i) (θ j) = if i = j then 1 else 0)
  (hηθ : ∀ i ∈ A, ∀ j ∈ B, cfInner (η i) (θ j) = 0)

include hηη hηθ

omit hθθ in
theorem cfInner_dblProj_eta (i : ι) (hi : i ∈ A) :
    cfInner ((∑ i ∈ A, c i • η i) + ∑ j ∈ B, g j • θ j) (η i) = c i := by
  rw [cfInner_add_left, cfInner_sum_left, cfInner_sum_left]
  have h1 : ∑ j ∈ A, cfInner (c j • η j) (η i) = c i := by
    rw [Finset.sum_eq_single_of_mem i hi]
    · rw [cfInner_smul_left, hηη i hi i hi, if_pos rfl, mul_one]
    · intro j hj hji
      rw [cfInner_smul_left, hηη j hj i hi, if_neg hji, mul_zero]
  have h2 : ∑ j ∈ B, cfInner (g j • θ j) (η i) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [cfInner_smul_left, ← conj_cfInner, hηθ i hi j hj, map_zero, mul_zero]
  rw [h1, h2, add_zero]

include hθθ

omit hηη in
theorem cfInner_dblProj_theta (j : ι) (hj : j ∈ B) :
    cfInner ((∑ i ∈ A, c i • η i) + ∑ j ∈ B, g j • θ j) (θ j) = g j := by
  rw [cfInner_add_left, cfInner_sum_left, cfInner_sum_left]
  have h1 : ∑ i ∈ A, cfInner (c i • η i) (θ j) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [cfInner_smul_left, hηθ i hi j hj, mul_zero]
  have h2 : ∑ i ∈ B, cfInner (g i • θ i) (θ j) = g j := by
    rw [Finset.sum_eq_single_of_mem j hj]
    · rw [cfInner_smul_left, hθθ j hj j hj, if_pos rfl, mul_one]
    · intro i hi hij
      rw [cfInner_smul_left, hθθ i hi j hj, if_neg hij, mul_zero]
  rw [h1, h2, zero_add]

theorem cfInner_self_eq_sum_add_sum_add
    (hP : P = (∑ i ∈ A, c i • η i) + ∑ j ∈ B, g j • θ j)
    (hc : ∀ i ∈ A, cfInner f (η i) = c i) (hg : ∀ j ∈ B, cfInner f (θ j) = g j) :
    cfInner f f = (∑ i ∈ A, c i * conj (c i)) + (∑ j ∈ B, g j * conj (g j))
      + cfInner (f - P) (f - P) := by
  subst hP
  have hd1 : ∀ i ∈ A, cfInner (f - ((∑ i ∈ A, c i • η i) + ∑ j ∈ B, g j • θ j)) (η i) = 0 :=
    fun i hi => by
      rw [cfInner_sub_left, hc i hi, cfInner_dblProj_eta hηη hηθ i hi, sub_self]
  have hd2 : ∀ j ∈ B, cfInner (f - ((∑ i ∈ A, c i • η i) + ∑ j ∈ B, g j • θ j)) (θ j) = 0 :=
    fun j hj => by
      rw [cfInner_sub_left, hg j hj, cfInner_dblProj_theta hθθ hηθ j hj, sub_self]
  have hPP : cfInner ((∑ i ∈ A, c i • η i) + ∑ j ∈ B, g j • θ j)
      ((∑ i ∈ A, c i • η i) + ∑ j ∈ B, g j • θ j)
      = (∑ i ∈ A, c i * conj (c i)) + ∑ j ∈ B, g j * conj (g j) := by
    rw [cfInner_add_right, cfInner_sum_right, cfInner_sum_right]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [cfInner_smul_right, cfInner_dblProj_eta hηη hηθ i hi, mul_comm]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [cfInner_smul_right, cfInner_dblProj_theta hθθ hηθ j hj, mul_comm]
  rw [cfInner_self_eq_add_of_cfInner_sub_eq_zero
    (cfInner_combination_eq_zero hd1 hd2), hPP]

end Projection

theorem cfInner_self_nonneg_of_eq_intCast {X : Type*} [Fintype X] {f : X → ℂ} {n : ℤ}
    (h : cfInner f f = (n : ℂ)) : 0 ≤ n := by
  have hval : cfInner f f = (((Nat.card X : ℝ)⁻¹ * ∑ x, Complex.normSq (f x) : ℝ) : ℂ) := by
    rw [cfInner_self_eq_sum_normSq]
    push_cast
    ring
  rw [h] at hval
  have hre : (n : ℝ) = (Nat.card X : ℝ)⁻¹ * ∑ x, Complex.normSq (f x) := by exact_mod_cast hval
  have hnn : (0 : ℝ) ≤ (Nat.card X : ℝ)⁻¹ * ∑ x, Complex.normSq (f x) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => Complex.normSq_nonneg _)
  exact_mod_cast hre ▸ hnn

theorem exists_int_cfInner_family {G : Type*} [Group G] [Fintype G] {ι : Type*} {f : G → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr G)) {η : ι → G → ℂ}
    (hη : ∀ i, η i ∈ Submodule.span ℤ (Irr G)) :
    ∃ c : ι → ℤ, ∀ i, cfInner f (η i) = (c i : ℂ) :=
  Classical.axiomOfChoice fun i => exists_int_cfInner_of_mem_span_Irr hf (hη i)

section Orth

variable {G : Type*} [Fintype G] {ι : Type*} {A : Finset ι} {θ : ι → G → ℂ} {c : ι → ℂ}

theorem cfInner_sum_smul_right_of_orthonormalOn [DecidableEq ι]
    (hθθ : ∀ i ∈ A, ∀ j ∈ A, cfInner (θ i) (θ j) = if i = j then 1 else 0)
    {j : ι} (hj : j ∈ A) : cfInner (∑ i ∈ A, c i • θ i) (θ j) = c j := by
  rw [cfInner_sum_left, Finset.sum_eq_single_of_mem j hj (fun i hi hij => by
    rw [cfInner_smul_left, hθθ i hi j hj, if_neg hij, mul_zero]),
    cfInner_smul_left, hθθ j hj j hj, if_pos rfl, mul_one]

theorem cfInner_self_sum_zsmul_of_orthonormalOn [DecidableEq ι] {g : ι → ℤ}
    (hθθ : ∀ i ∈ A, ∀ j ∈ A, cfInner (θ i) (θ j) = if i = j then 1 else 0) :
    cfInner (∑ i ∈ A, (g i : ℂ) • θ i) (∑ i ∈ A, (g i : ℂ) • θ i)
      = ((∑ i ∈ A, g i ^ 2 : ℤ) : ℂ) := by
  rw [cfInner_sum_right]
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [cfInner_smul_right, cfInner_sum_smul_right_of_orthonormalOn hθθ hi]
  simp [sq]

theorem int_coeff_sub_eq {u v w : G → ℂ} {m m' c : ℤ}
    (hm : cfInner u v = (m : ℂ)) (hm' : cfInner u w = (m' : ℂ))
    (h : cfInner u (v - w) = (c : ℂ)) : m - m' = c := by
  rw [cfInner_sub_right, hm, hm'] at h
  have : ((m - m' : ℤ) : ℂ) = (c : ℂ) := by push_cast; linear_combination h
  exact_mod_cast this

theorem cfInner_sum_smul_right_eq_zero {u : G → ℂ} (hu : ∀ i ∈ A, cfInner u (θ i) = 0) :
    cfInner u (∑ i ∈ A, c i • θ i) = 0 := by
  rw [cfInner_sum_right]
  exact Finset.sum_eq_zero fun i hi => by rw [cfInner_smul_right, hu i hi, mul_zero]

end Orth

section Squeeze

variable {G : Type*} [Fintype G] [Nonempty G] {ι : Type*} [DecidableEq ι] {A B : Finset ι}
  {η θ : ι → G → ℂ} {f : G → ℂ} {a g : ι → ℤ} {b K : ℤ} {i₀ j₁ j₂ : ι}

theorem eq_add_sum_of_double_projection_squeeze
    (hηη : ∀ i ∈ A, ∀ j ∈ A, cfInner (η i) (η j) = if i = j then 1 else 0)
    (hθθ : ∀ i ∈ B, ∀ j ∈ B, cfInner (θ i) (θ j) = if i = j then 1 else 0)
    (hηθ : ∀ i ∈ A, ∀ j ∈ B, cfInner (η i) (θ j) = 0)
    (ha' : ∀ i ∈ A, cfInner f (η i) = (a i : ℂ))
    (hg' : ∀ j ∈ B, cfInner f (θ j) = (g j : ℂ))
    (hff : cfInner f f = ((1 + K ^ 2 : ℤ) : ℂ))
    (hi₀ : i₀ ∈ A) (hcard : (A.card : ℤ) = 2 * K) (hK : 0 < K)
    (ha₀ : a i₀ = b - K) (ha : ∀ i ∈ A, i ≠ i₀ → a i = b)
    (hj₁ : j₁ ∈ B) (hj₂ : j₂ ∈ B) (hjne : j₁ ≠ j₂) (hgdiff : g j₁ - g j₂ = 1) :
    b ^ 2 = b ∧ (∑ j ∈ B, g j ^ 2) = 1 ∧
      f = (∑ i ∈ A, (a i : ℂ) • η i) + ∑ j ∈ B, (g j : ℂ) • θ j := by
  classical
  set P : G → ℂ := (∑ i ∈ A, (a i : ℂ) • η i) + ∑ j ∈ B, (g j : ℂ) • θ j with hPdef
  have key := cfInner_self_eq_sum_add_sum_add (A := A) (B := B) (η := η) (θ := θ) (f := f)
    (c := fun i => (a i : ℂ)) (g := fun j => (g j : ℂ)) (P := P) hηη hθθ hηθ hPdef ha' hg'
  have hA : (∑ i ∈ A, ((a i : ℂ)) * conj ((a i : ℂ))) = ((∑ i ∈ A, a i ^ 2 : ℤ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun i _ => by simp [sq]
  have hB : (∑ j ∈ B, ((g j : ℂ)) * conj ((g j : ℂ))) = ((∑ j ∈ B, g j ^ 2 : ℤ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun j _ => by simp [sq]
  set t : ℤ := (1 + K ^ 2) - (∑ i ∈ A, a i ^ 2) - (∑ j ∈ B, g j ^ 2) with htdef
  have hrem : cfInner (f - P) (f - P) = (t : ℂ) := by
    rw [hff, hA, hB] at key
    rw [htdef]
    push_cast at key ⊢
    linear_combination -key
  have ht0 : 0 ≤ t := cfInner_self_nonneg_of_eq_intCast hrem
  have heq : (1 + K ^ 2) = (∑ i ∈ A, a i ^ 2) + (∑ j ∈ B, g j ^ 2) + t := by omega
  have hAsum : (∑ i ∈ A, a i ^ 2) = 2 * K * (b ^ 2 - b) + K ^ 2 := by
    have hrest : ∑ i ∈ A.erase i₀, a i ^ 2 = (A.card - 1) • b ^ 2 := by
      rw [Finset.sum_congr rfl (fun i hi => by
        rw [ha i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)]),
        Finset.sum_const, Finset.card_erase_of_mem hi₀]
    have h1 : ((A.card - 1 : ℕ) : ℤ) = 2 * K - 1 := by
      have hpos : 1 ≤ A.card := Finset.card_pos.2 ⟨i₀, hi₀⟩
      omega
    rw [← Finset.sum_erase_add A _ hi₀, hrest, ha₀, nsmul_eq_mul, h1]
    ring
  have hBge : 1 ≤ ∑ j ∈ B, g j ^ 2 := by
    have hsub : ({j₁, j₂} : Finset ι) ⊆ B := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hle : ∑ j ∈ ({j₁, j₂} : Finset ι), g j ^ 2 ≤ ∑ j ∈ B, g j ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => sq_nonneg _
    rw [Finset.sum_pair hjne] at hle
    have : 1 ≤ g j₁ ^ 2 + g j₂ ^ 2 := by nlinarith [sq_nonneg (g j₁ + g j₂)]
    omega
  have hbnn : 0 ≤ b ^ 2 - b := by
    rcases le_or_gt 1 b with hb | hb
    · nlinarith
    · have : b ≤ 0 := by omega
      nlinarith
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have htz : t = 0 := by nlinarith
  have hz : f - P = 0 := by
    rw [← cfInner_self_eq_zero (f := f - P), hrem, htz]
    simp
  rw [sub_eq_zero] at hz
  exact hz

theorem b_eq_zero_of_alpha_projection {Z : G → ℂ} {p : ι → ℤ} {x : ℤ}
    (hηη : ∀ i ∈ A, ∀ j ∈ A, cfInner (η i) (η j) = if i = j then 1 else 0)
    (hθθ : ∀ i ∈ B, ∀ j ∈ B, cfInner (θ i) (θ j) = if i = j then 1 else 0)
    (hηθ : ∀ i ∈ A, ∀ j ∈ B, cfInner (η i) (θ j) = 0)
    (ha' : ∀ i ∈ A, cfInner f (η i) = (a i : ℂ))
    (hg' : ∀ j ∈ B, cfInner f (θ j) = (g j : ℂ))
    (hff : cfInner f f = ((1 + K ^ 2 : ℤ) : ℂ))
    (hi₀ : i₀ ∈ A) (hcard : (A.card : ℤ) = 2 * K) (hK : 1 < K)
    (ha₀ : a i₀ = b - K) (ha : ∀ i ∈ A, i ≠ i₀ → a i = b)
    (hj₁ : j₁ ∈ B) (hj₂ : j₂ ∈ B) (hjne : j₁ ≠ j₂) (hgdiff : g j₁ - g j₂ = 1)
    (hZθ : ∀ j ∈ B, cfInner Z (θ j) = 0)
    (hZη : ∀ i ∈ A, cfInner Z (η i) = (p i : ℂ))
    (hp₀ : p i₀ = x - 1) (hp : ∀ i ∈ A, i ≠ i₀ → p i = x)
    (hZf : cfInner Z f = (K : ℂ)) :
    b = 0 ∧ (∑ j ∈ B, g j ^ 2) = 1 ∧
      f = (∑ i ∈ A, (a i : ℂ) • η i) + ∑ j ∈ B, (g j : ℂ) • θ j := by
  classical
  have hK0 : 0 < K := by omega
  obtain ⟨hb2, hBsum, hfP⟩ := eq_add_sum_of_double_projection_squeeze hηη hθθ hηθ ha' hg' hff
    hi₀ hcard hK0 ha₀ ha hj₁ hj₂ hjne hgdiff
  refine ⟨?_, hBsum, hfP⟩
  have hZfP : cfInner Z f = ((∑ i ∈ A, a i * p i : ℤ) : ℂ) := by
    rw [hfP, cfInner_add_right, cfInner_sum_smul_right_eq_zero hZθ, add_zero, cfInner_sum_right]
    push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [cfInner_smul_right, hZη i hi]
    simp
  have hsum : (∑ i ∈ A, a i * p i) = (b - K) * (x - 1) + (2 * K - 1) * (b * x) := by
    have hrest : ∑ i ∈ A.erase i₀, a i * p i = (A.card - 1) • (b * x) := by
      rw [Finset.sum_congr rfl (fun i hi => by
        rw [ha i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi),
          hp i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)]),
        Finset.sum_const, Finset.card_erase_of_mem hi₀]
    have h1 : ((A.card - 1 : ℕ) : ℤ) = 2 * K - 1 := by
      have hpos : 1 ≤ A.card := Finset.card_pos.2 ⟨i₀, hi₀⟩
      omega
    rw [← Finset.sum_erase_add A _ hi₀, hrest, ha₀, hp₀, nsmul_eq_mul, h1]
    ring
  have hKint : K = (b - K) * (x - 1) + (2 * K - 1) * (b * x) := by
    have : ((K : ℤ) : ℂ) = (((b - K) * (x - 1) + (2 * K - 1) * (b * x) : ℤ) : ℂ) := by
      rw [← hZf, hZfP, hsum]
    exact_mod_cast this
  have hb01 : b = 0 ∨ b = 1 := by
    have hz : b * (b - 1) = 0 := by nlinarith [hb2]
    rcases mul_eq_zero.1 hz with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  rcases hb01 with h | h
  · exact h
  · subst h
    exfalso
    have h1 : K * x = 1 := by nlinarith [hKint]
    have := Int.le_of_dvd one_pos ⟨x, h1.symm⟩
    omega

end Squeeze

section SpanImage

variable {L G : Type*} [Group G]

open scoped Classical in
noncomputable def spanEmb (T : Finset (L → ℂ)) (χ : L → ℂ) :
    Submodule.span ℤ (T : Set (L → ℂ)) :=
  if h : χ ∈ (T : Set (L → ℂ)) then ⟨χ, Submodule.subset_span h⟩ else 0

noncomputable def spanImage (T : Finset (L → ℂ))
    (ν : Submodule.span ℤ (T : Set (L → ℂ)) →+ virtualChars G) (χ : L → ℂ) : G → ℂ :=
  (ν (spanEmb T χ) : G → ℂ)

variable {T : Finset (L → ℂ)} {ν : Submodule.span ℤ (T : Set (L → ℂ)) →+ virtualChars G}

theorem spanEmb_of_mem {χ : L → ℂ} (h : χ ∈ T) :
    spanEmb T χ = ⟨χ, Submodule.subset_span (show χ ∈ (T : Set (L → ℂ)) from h)⟩ := by
  classical
  change (if h : χ ∈ (T : Set (L → ℂ)) then _ else 0) = _
  rw [dif_pos (show χ ∈ (T : Set (L → ℂ)) from h)]

theorem spanImage_eq (χ : L → ℂ) : spanImage T ν χ = (ν (spanEmb T χ) : G → ℂ) := (rfl)

theorem spanImage_of_mem {χ : L → ℂ} (h : χ ∈ T) :
    spanImage T ν χ
      = (ν ⟨χ, Submodule.subset_span (show χ ∈ (T : Set (L → ℂ)) from h)⟩ : G → ℂ) := by
  rw [spanImage_eq, spanEmb_of_mem h]

theorem spanImage_mem_span_Irr (χ : L → ℂ) :
    spanImage T ν χ ∈ Submodule.span ℤ (Irr G) :=
  mem_span_Irr_of_mem_virtualChars (ν (spanEmb T χ)).2

theorem spanImage_sub_eq {χ χ' : L → ℂ} (hχ : χ ∈ T) (hχ' : χ' ∈ T) :
    spanImage T ν χ - spanImage T ν χ'
      = ((ν (⟨χ, Submodule.subset_span (show χ ∈ (T : Set (L → ℂ)) from hχ)⟩
          - ⟨χ', Submodule.subset_span (show χ' ∈ (T : Set (L → ℂ)) from hχ')⟩)
          : virtualChars G) : G → ℂ) := by
  rw [map_sub, spanImage_of_mem hχ, spanImage_of_mem hχ']
  rfl

theorem sum_zsmul_spanImage_eq (A : Finset (L → ℂ)) (c : (L → ℂ) → ℤ) :
    ∑ χ ∈ A, (c χ : ℂ) • spanImage T ν χ
      = ((ν (∑ χ ∈ A, c χ • spanEmb T χ) : virtualChars G) : G → ℂ) := by
  rw [map_sum, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [map_zsmul, SetLike.val_smul, Int.cast_smul_eq_zsmul, spanImage_eq]

theorem sum_zsmul_spanImage_mem_span_Irr (A : Finset (L → ℂ)) (c : (L → ℂ) → ℤ) :
    (∑ χ ∈ A, (c χ : ℂ) • spanImage T ν χ) ∈ Submodule.span ℤ (Irr G) := by
  rw [sum_zsmul_spanImage_eq]
  exact mem_span_Irr_of_mem_virtualChars (ν _).2

end SpanImage

theorem exists_addMonoidHom_isometry_of_gram_eq
    {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Set (L → ℂ)} {u : ι → L → ℂ} (hS : S = Set.range u) {g : ι → ℂ}
    (hgramu : ∀ i j, cfInner (u i) (u j) = if i = j then g i else 0) (hgne : ∀ i, g i ≠ 0)
    {v : ι → G → ℂ} (hvmem : ∀ i, v i ∈ Submodule.span ℤ (Irr G))
    (hgramv : ∀ i j, cfInner (v i) (v j) = if i = j then g i else 0) :
    ∃ ν : Submodule.span ℤ S →+ virtualChars G,
      (∀ f h : Submodule.span ℤ S,
        cfInner (ν f : G → ℂ) (ν h : G → ℂ) = cfInner (f : L → ℂ) (h : L → ℂ)) ∧
      ∀ i, ∀ w : Submodule.span ℤ S, (w : L → ℂ) = u i →
        ((ν w : virtualChars G) : G → ℂ) = v i := by
  have hu : LinearIndependent ℤ u := linearIndependent_of_gram_diag hgramu hgne
  refine ⟨(spanIrrToVirtualChars G).comp (extendAlong hS hu hvmem).toAddMonoidHom, ?_, ?_⟩
  · intro w w'
    obtain ⟨c, hc1, hc2⟩ := exists_coe_extendAlong_eq hS hu hvmem w
    obtain ⟨c', hd1, hd2⟩ := exists_coe_extendAlong_eq hS hu hvmem w'
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      coe_spanIrrToVirtualChars]
    rw [hc1, hd1, hc2, hd2, cfInner_sum_smul_of_gram_diag hgramv,
      cfInner_sum_smul_of_gram_diag hgramu]
  · intro i w hw
    obtain ⟨c, hc1, hc2⟩ := exists_coe_extendAlong_eq hS hu hvmem w
    have hci := eq_single_of_gram_diag hgramu hgne (hw ▸ hc1 : u i = ∑ j, (c j : ℂ) • u j)
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      coe_spanIrrToVirtualChars]
    rw [hc2, Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => congrArg (· • v j) (hci j)]
    simp

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]
  {S : Finset (L → ℂ)} {tau : (L → ℂ) → G → ℂ} {R : (L → ℂ) → Finset (G → ℂ)}

omit [Fintype L] in
theorem mem_intSpanZeroAtOne_of_mem_charSpanZero {T : Set (L → ℂ)}
    (hTS : T ⊆ (S : Set (L → ℂ))) {f : L → ℂ} (hf : f ∈ charSpanZero T) :
    f ∈ intSpanZeroAtOne (S : Set (L → ℂ)) :=
  mem_intSpanZeroAtOne.2
    ⟨Submodule.span_mono hTS (mem_charSpanZero.1 hf).1, (mem_charSpanZero.1 hf).2⟩

theorem tau_mem_virtualChars (hc : IsSubcoherent S tau R) {f : L → ℂ}
    (hf : f ∈ intSpanZeroAtOne (S : Set (L → ℂ))) : tau f ∈ virtualChars G :=
  mem_virtualChars_of_mem_span_Irr
    (DisjointCoherentBlocks.mem_span_Irr_of_mem_virtualCharSpan (hc.tau_mem f hf))

noncomputable def baselineOn (hc : IsSubcoherent S tau R) {T : Set (L → ℂ)}
    (hTS : T ⊆ (S : Set (L → ℂ))) : charSpanZero T →+ virtualChars G where
  toFun f := ⟨tau (f : L → ℂ), tau_mem_virtualChars hc
    (mem_intSpanZeroAtOne_of_mem_charSpanZero hTS f.2)⟩
  map_zero' := Subtype.ext hc.tau_zero
  map_add' f g := Subtype.ext (hc.map_add _ (mem_intSpanZeroAtOne_of_mem_charSpanZero hTS f.2)
    _ (mem_intSpanZeroAtOne_of_mem_charSpanZero hTS g.2))

theorem coe_baselineOn (hc : IsSubcoherent S tau R) {T : Set (L → ℂ)}
    (hTS : T ⊆ (S : Set (L → ℂ))) (f : charSpanZero T) :
    (baselineOn hc hTS f : G → ℂ) = tau (f : L → ℂ) := (rfl)

theorem cfInner_tau_tau (hc : IsSubcoherent S tau R) {f g : L → ℂ}
    (hf : f ∈ intSpanZeroAtOne (S : Set (L → ℂ)))
    (hg : g ∈ intSpanZeroAtOne (S : Set (L → ℂ))) :
    cfInner (tau f) (tau g) = cfInner f g := by
  rw [← charInner_eq_cfInner, ← charInner_eq_cfInner]
  exact hc.charInner_tau_tau f hf g hg

omit [Group L] [Fintype L] [Fintype G] in
theorem addMonoidHom_eq_of_eq_on_generators {P : Submodule ℤ (L → ℂ)} {T : Set (L → ℂ)}
    {N : Type*} [AddCommGroup N] (hT : T ⊆ (P : Set (L → ℂ))) (hP : P ≤ Submodule.span ℤ T)
    (φ φ' : P →+ N) (h : ∀ t (ht : t ∈ T), φ ⟨t, hT ht⟩ = φ' ⟨t, hT ht⟩)
    (f : P) : φ f = φ' f := by
  suffices key : ∀ v ∈ Submodule.span ℤ T, ∀ hv : v ∈ P, φ ⟨v, hv⟩ = φ' ⟨v, hv⟩ by
    obtain ⟨v, hv⟩ := f
    exact key v (hP hv) hv
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => intro _; exact h x hx
  | zero =>
      intro hz
      have he : (⟨0, hz⟩ : P) = 0 := rfl
      rw [he, map_zero, map_zero]
  | add x y hx hy ihx ihy =>
      intro _
      have hxP : x ∈ P := Submodule.span_le.2 hT hx
      have hyP : y ∈ P := Submodule.span_le.2 hT hy
      have he : (⟨x + y, P.add_mem hxP hyP⟩ : P) = ⟨x, hxP⟩ + ⟨y, hyP⟩ := rfl
      rw [he, map_add, map_add, ihx hxP, ihy hyP]
  | smul c x hx ih =>
      intro _
      have hxP : x ∈ P := Submodule.span_le.2 hT hx
      have he : (⟨c • x, P.smul_mem c hxP⟩ : P) = c • ⟨x, hxP⟩ := rfl
      rw [he, map_zsmul, map_zsmul, ih hxP]

section Pair

variable {S1 : Finset (L → ℂ)} {a b ψ : L → ℂ} {k : ℤ} {e : ℂ} {W : Set (L → ℂ)}
  {ν₁ : Submodule.span ℤ (S1 : Set (L → ℂ)) →+ virtualChars G}

def pairGens (S1 : Finset (L → ℂ)) (a b ψ : L → ℂ) (k : ℤ) : Set (L → ℂ) :=
  (fun χ => χ - ψ) '' (S1 : Set (L → ℂ)) ∪ {a - k • ψ, b - k • ψ}

omit [Group L] [Fintype L] [Fintype G] in
theorem mem_pairGens_iff {x : L → ℂ} :
    x ∈ pairGens S1 a b ψ k ↔ (∃ χ ∈ S1, χ - ψ = x) ∨ x = a - k • ψ ∨ x = b - k • ψ := by
  simp only [pairGens, Set.mem_union, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
    Finset.mem_coe]

omit [Fintype L] [Fintype G] in
theorem span_pairGens_le (hψ : ψ ∈ S1) (hdeg : ∀ χ ∈ S1, χ 1 = e)
    (hdega : a 1 = (k : ℂ) * e) (hdegb : b 1 = (k : ℂ) * e) :
    Submodule.span ℤ (pairGens S1 a b ψ k)
      ≤ charSpanZero ((S1 : Set (L → ℂ)) ∪ {a, b}) := by
  rw [Submodule.span_le]
  intro v hv
  have hψW : ψ ∈ (S1 : Set (L → ℂ)) ∪ ({a, b} : Set (L → ℂ)) := Or.inl hψ
  have haW : a ∈ (S1 : Set (L → ℂ)) ∪ ({a, b} : Set (L → ℂ)) := Or.inr (Or.inl rfl)
  have hbW : b ∈ (S1 : Set (L → ℂ)) ∪ ({a, b} : Set (L → ℂ)) := Or.inr (Or.inr rfl)
  rcases hv with ⟨χ, hχ, rfl⟩ | hv
  · exact mem_charSpanZero.2 ⟨Submodule.sub_mem _ (Submodule.subset_span (Or.inl hχ))
      (Submodule.subset_span hψW), by simp [hdeg _ hχ, hdeg _ hψ]⟩
  · rcases hv with rfl | hv
    · exact mem_charSpanZero.2 ⟨Submodule.sub_mem _ (Submodule.subset_span haW)
        (Submodule.smul_mem _ _ (Submodule.subset_span hψW)), by simp [hdega, hdeg _ hψ]⟩
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      exact mem_charSpanZero.2 ⟨Submodule.sub_mem _ (Submodule.subset_span hbW)
        (Submodule.smul_mem _ _ (Submodule.subset_span hψW)), by simp [hdegb, hdeg _ hψ]⟩

omit [Fintype L] [Fintype G] in
theorem charSpanZero_le_span_pairGens (hdeg : ∀ χ ∈ S1, χ 1 = e)
    (hdega : a 1 = (k : ℂ) * e) (hdegb : b 1 = (k : ℂ) * e) (he : e ≠ 0)
    (haS1 : a ∉ S1) (hbS1 : b ∉ S1) (hab : a ≠ b) :
    charSpanZero ((S1 : Set (L → ℂ)) ∪ {a, b})
      ≤ Submodule.span ℤ (pairGens S1 a b ψ k) := by
  classical
  intro v hv
  obtain ⟨hvspan, hv1⟩ := mem_charSpanZero.1 hv
  set W' : Finset (L → ℂ) := S1 ∪ {a, b} with hWdef
  have hWcoe : (W' : Set (L → ℂ)) = (S1 : Set (L → ℂ)) ∪ {a, b} := by simp [hWdef]
  rw [← hWcoe] at hvspan
  obtain ⟨c, -, hcsum⟩ := Submodule.mem_span_finset.1 hvspan
  have hdisj : Disjoint S1 ({a, b} : Finset (L → ℂ)) := by
    simp [Finset.disjoint_right, haS1, hbS1]
  have hsplit : ∑ χ ∈ W', c χ • χ = (∑ χ ∈ S1, c χ • χ) + (c a • a + c b • b) := by
    rw [hWdef, Finset.sum_union hdisj, Finset.sum_pair hab]
  have hval : v 1 = (((∑ χ ∈ S1, c χ) + k * c a + k * c b : ℤ) : ℂ) * e := by
    rw [← hcsum, hsplit]
    have h1 : (∑ χ ∈ S1, c χ • χ) 1 = ((∑ χ ∈ S1, c χ : ℤ) : ℂ) * e := by
      rw [Finset.sum_apply, Int.cast_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun χ hχ => by
        rw [Pi.smul_apply, zsmul_eq_mul, hdeg χ hχ]
    rw [Pi.add_apply, Pi.add_apply, h1, Pi.smul_apply, Pi.smul_apply, zsmul_eq_mul,
      zsmul_eq_mul, hdega, hdegb]
    push_cast
    ring
  have hN0 : (∑ χ ∈ S1, c χ) + k * c a + k * c b = 0 := by
    rw [hv1] at hval
    rcases mul_eq_zero.1 hval.symm with h | h
    · exact_mod_cast h
    · exact absurd h he
  have hsum_sub : (∑ χ ∈ S1, c χ • (χ - ψ))
      = (∑ χ ∈ S1, c χ • χ) - (∑ χ ∈ S1, c χ) • ψ := by
    rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun χ _ => smul_sub _ _ _
  have hkey : v = (∑ χ ∈ S1, c χ • (χ - ψ)) + (c a • (a - k • ψ) + c b • (b - k • ψ)) := by
    rw [hsum_sub, smul_sub, smul_sub, ← hcsum, hsplit, smul_smul, smul_smul]
    have hz : ((∑ χ ∈ S1, c χ) + (c a * k + c b * k)) • ψ = (0 : L → ℂ) := by
      rw [show (∑ χ ∈ S1, c χ) + (c a * k + c b * k) = 0 by linarith [hN0], zero_smul]
    rw [add_smul, add_smul] at hz
    rw [← sub_eq_zero,
      show (∑ χ ∈ S1, c χ • χ) + (c a • a + c b • b)
        - ((∑ χ ∈ S1, c χ • χ) - (∑ χ ∈ S1, c χ) • ψ
          + (c a • a - (c a * k) • ψ + (c b • b - (c b * k) • ψ)))
        = (∑ χ ∈ S1, c χ) • ψ + (c a * k) • ψ + (c b * k) • ψ from by abel, ← hz]
    abel
  rw [hkey]
  exact Submodule.add_mem _ (Submodule.sum_mem _ fun χ hχ => Submodule.smul_mem _ _
    (Submodule.subset_span (Or.inl ⟨χ, hχ, rfl⟩))) (Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr (Or.inl rfl))))
    (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr (Or.inr rfl)))))

open scoped Classical in
noncomputable def pairImage (S1 : Finset (L → ℂ)) (a : L → ℂ) (W : Set (L → ℂ))
    (ν₁ : Submodule.span ℤ (S1 : Set (L → ℂ)) →+ virtualChars G) (Γ₁ Γ₂ : virtualChars G)
    (χ : W) : virtualChars G :=
  if h : (χ : L → ℂ) ∈ (S1 : Set (L → ℂ)) then ν₁ ⟨(χ : L → ℂ), Submodule.subset_span h⟩
  else if (χ : L → ℂ) = a then Γ₁ else Γ₂

omit [Group L] [Fintype G] in
theorem pairImage_of_mem (Γ₁ Γ₂ : virtualChars G) {x : L → ℂ}
    (h : x ∈ (S1 : Set (L → ℂ))) (h' : x ∈ W) :
    pairImage S1 a W ν₁ Γ₁ Γ₂ ⟨x, h'⟩ = ν₁ ⟨x, Submodule.subset_span h⟩ := by
  classical
  change (if hh : x ∈ (S1 : Set (L → ℂ)) then ν₁ ⟨x, Submodule.subset_span hh⟩
    else if x = a then Γ₁ else Γ₂) = _
  rw [dif_pos h]

omit [Group L] [Fintype G] in
theorem pairImage_left (Γ₁ Γ₂ : virtualChars G) (haS1 : a ∉ (S1 : Set (L → ℂ)))
    (haW : a ∈ W) : pairImage S1 a W ν₁ Γ₁ Γ₂ ⟨a, haW⟩ = Γ₁ := by
  classical
  change (if hh : a ∈ (S1 : Set (L → ℂ)) then ν₁ ⟨a, Submodule.subset_span hh⟩
    else if a = a then Γ₁ else Γ₂) = Γ₁
  rw [dif_neg haS1, if_pos rfl]

omit [Group L] [Fintype G] in
theorem pairImage_right (Γ₁ Γ₂ : virtualChars G) (hbS1 : b ∉ (S1 : Set (L → ℂ)))
    (hab : a ≠ b) (hbW : b ∈ W) : pairImage S1 a W ν₁ Γ₁ Γ₂ ⟨b, hbW⟩ = Γ₂ := by
  classical
  change (if hh : b ∈ (S1 : Set (L → ℂ)) then ν₁ ⟨b, Submodule.subset_span hh⟩
    else if b = a then Γ₁ else Γ₂) = Γ₂
  rw [dif_neg hbS1, if_neg (Ne.symm hab)]

theorem cfInner_pairImage_pairImage (hW : W = (S1 : Set (L → ℂ)) ∪ {a, b})
    (hS1Irr : (S1 : Set (L → ℂ)) ⊆ Irr L)
    (haS1 : a ∉ (S1 : Set (L → ℂ))) (hbS1 : b ∉ (S1 : Set (L → ℂ))) (hab : a ≠ b)
    (hν₁ : ∀ f g : Submodule.span ℤ (S1 : Set (L → ℂ)),
      cfInner (ν₁ f : G → ℂ) (ν₁ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (Γ₁ Γ₂ : virtualChars G)
    (h11 : cfInner (Γ₁ : G → ℂ) (Γ₁ : G → ℂ) = 1)
    (h22 : cfInner (Γ₂ : G → ℂ) (Γ₂ : G → ℂ) = 1)
    (h12 : cfInner (Γ₁ : G → ℂ) (Γ₂ : G → ℂ) = 0)
    (ho1 : ∀ f : Submodule.span ℤ (S1 : Set (L → ℂ)), cfInner (Γ₁ : G → ℂ) (ν₁ f : G → ℂ) = 0)
    (ho2 : ∀ f : Submodule.span ℤ (S1 : Set (L → ℂ)), cfInner (Γ₂ : G → ℂ) (ν₁ f : G → ℂ) = 0)
    (χ χ' : W) :
    cfInner ((pairImage S1 a W ν₁ Γ₁ Γ₂ χ : virtualChars G) : G → ℂ)
        ((pairImage S1 a W ν₁ Γ₁ Γ₂ χ' : virtualChars G) : G → ℂ)
      = if χ = χ' then 1 else 0 := by
  classical
  have haW : a ∈ W := by rw [hW]; exact Or.inr (Or.inl rfl)
  have hbWm : b ∈ W := by rw [hW]; exact Or.inr (Or.inr rfl)
  have hL : pairImage S1 a W ν₁ Γ₁ Γ₂ ⟨a, haW⟩ = Γ₁ := pairImage_left Γ₁ Γ₂ haS1 haW
  have hRr : pairImage S1 a W ν₁ Γ₁ Γ₂ ⟨b, hbWm⟩ = Γ₂ := pairImage_right Γ₁ Γ₂ hbS1 hab hbWm
  have hpair : ∀ x : W, (x : L → ℂ) ∉ (S1 : Set (L → ℂ)) →
      (pairImage S1 a W ν₁ Γ₁ Γ₂ x = Γ₁ ∧ (x : L → ℂ) = a)
        ∨ (pairImage S1 a W ν₁ Γ₁ Γ₂ x = Γ₂ ∧ (x : L → ℂ) = b) := by
    intro x hx
    have hmem : (x : L → ℂ) ∈ (S1 : Set (L → ℂ)) ∪ ({a, b} : Set (L → ℂ)) := hW ▸ x.2
    rcases hmem with h | h
    · exact absurd h hx
    · rcases h with h | h
      · exact Or.inl ⟨by rw [show x = ⟨a, haW⟩ from Subtype.ext h, hL], h⟩
      · have h' : (x : L → ℂ) = b := Set.mem_singleton_iff.1 h
        exact Or.inr ⟨by rw [show x = ⟨b, hbWm⟩ from Subtype.ext h', hRr], h'⟩
  by_cases hχ : (χ : L → ℂ) ∈ (S1 : Set (L → ℂ))
  · by_cases hχ' : (χ' : L → ℂ) ∈ (S1 : Set (L → ℂ))
    · rw [show χ = ⟨(χ : L → ℂ), χ.2⟩ from rfl, show χ' = ⟨(χ' : L → ℂ), χ'.2⟩ from rfl,
        pairImage_of_mem Γ₁ Γ₂ hχ χ.2, pairImage_of_mem Γ₁ Γ₂ hχ' χ'.2, hν₁,
        cfInner_eq_ite_of_mem_Irr (hS1Irr hχ) (hS1Irr hχ')]
      congr 1
      simp [Subtype.ext_iff]
    · have hne : χ ≠ χ' := fun h => hχ' (h ▸ hχ)
      rw [if_neg hne, show χ = ⟨(χ : L → ℂ), χ.2⟩ from rfl, pairImage_of_mem Γ₁ Γ₂ hχ χ.2]
      rcases hpair χ' hχ' with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h, ← conj_cfInner, ho1, map_zero]
      · rw [h, ← conj_cfInner, ho2, map_zero]
  · by_cases hχ' : (χ' : L → ℂ) ∈ (S1 : Set (L → ℂ))
    · have hne : χ ≠ χ' := fun h => hχ (h ▸ hχ')
      rw [if_neg hne, show χ' = ⟨(χ' : L → ℂ), χ'.2⟩ from rfl,
        pairImage_of_mem Γ₁ Γ₂ hχ' χ'.2]
      rcases hpair χ hχ with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h, ho1]
      · rw [h, ho2]
    · rcases hpair χ hχ with ⟨h, hxa⟩ | ⟨h, hxb⟩ <;>
        rcases hpair χ' hχ' with ⟨h', hya⟩ | ⟨h', hyb⟩
      · rw [h, h', h11, if_pos (Subtype.ext (hxa.trans hya.symm))]
      · rw [h, h', h12, if_neg (fun hcc => hab (by rw [← hxa, hcc, hyb]))]
      · rw [h, h', ← conj_cfInner, h12, map_zero,
          if_neg (fun hcc => hab (by rw [← hya, ← hcc, hxb]))]
      · rw [h, h', h22, if_pos (Subtype.ext (hxb.trans hyb.symm))]

theorem exists_isCoherentWith_insert_pair_of_orthonormal
    {S : Finset (L → ℂ)} {tau : (L → ℂ) → G → ℂ} {R : (L → ℂ) → Finset (G → ℂ)}
    (hc : IsSubcoherent S tau R)
    {S1 : Finset (L → ℂ)} {ν₁ : Submodule.span ℤ (S1 : Set (L → ℂ)) →+ virtualChars G}
    {a b ψ : L → ℂ} {k : ℤ} {e : ℂ}
    (hWS : (S1 : Set (L → ℂ)) ∪ {a, b} ⊆ (S : Set (L → ℂ)))
    (hS1Irr : (S1 : Set (L → ℂ)) ⊆ Irr L) (haIrr : a ∈ Irr L) (hbIrr : b ∈ Irr L)
    (haS1 : a ∉ (S1 : Set (L → ℂ))) (hbS1 : b ∉ (S1 : Set (L → ℂ))) (hab : a ≠ b)
    (hψ : ψ ∈ S1) (hdeg : ∀ χ ∈ S1, χ 1 = e) (he : e ≠ 0)
    (hdega : a 1 = (k : ℂ) * e) (hdegb : b 1 = (k : ℂ) * e)
    (hν₁ : ∀ f g : Submodule.span ℤ (S1 : Set (L → ℂ)),
      cfInner (ν₁ f : G → ℂ) (ν₁ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (Γ₁ Γ₂ : virtualChars G)
    (h11 : cfInner (Γ₁ : G → ℂ) (Γ₁ : G → ℂ) = 1)
    (h22 : cfInner (Γ₂ : G → ℂ) (Γ₂ : G → ℂ) = 1)
    (h12 : cfInner (Γ₁ : G → ℂ) (Γ₂ : G → ℂ) = 0)
    (ho1 : ∀ f : Submodule.span ℤ (S1 : Set (L → ℂ)), cfInner (Γ₁ : G → ℂ) (ν₁ f : G → ℂ) = 0)
    (ho2 : ∀ f : Submodule.span ℤ (S1 : Set (L → ℂ)), cfInner (Γ₂ : G → ℂ) (ν₁ f : G → ℂ) = 0)
    (htau1 : ∀ χ ∈ S1, tau (χ - ψ) = spanImage S1 ν₁ χ - spanImage S1 ν₁ ψ)
    (htaua : tau (a - k • ψ) = (Γ₁ : G → ℂ) - k • spanImage S1 ν₁ ψ)
    (htaub : tau (b - k • ψ) = (Γ₂ : G → ℂ) - k • spanImage S1 ν₁ ψ) :
    ∃ ν : Submodule.span ℤ ((S1 : Set (L → ℂ)) ∪ {a, b}) →+ virtualChars G,
      IsCoherentWith ((S1 : Set (L → ℂ)) ∪ {a, b}) (baselineOn hc hWS) ν ∧
      ∀ f : Submodule.span ℤ (S1 : Set (L → ℂ)),
        ν (Submodule.inclusion (Submodule.span_mono Set.subset_union_left) f) = ν₁ f := by
  classical
  set W : Set (L → ℂ) := (S1 : Set (L → ℂ)) ∪ {a, b} with hWdef
  have hWfin : W.Finite := (S1.finite_toSet).union (Set.toFinite _)
  have : Fintype W := hWfin.fintype
  have haW : a ∈ W := Or.inr (Or.inl rfl)
  have hbW : b ∈ W := Or.inr (Or.inr rfl)
  have hS1W : (S1 : Set (L → ℂ)) ⊆ W := Set.subset_union_left
  have hWIrr : W ⊆ Irr L := by
    intro x hx
    rcases hx with hx | hx
    · exact hS1Irr hx
    · rcases hx with rfl | hx
      · exact haIrr
      · rw [Set.mem_singleton_iff] at hx; subst hx; exact hbIrr
  set u : W → L → ℂ := fun x => (x : L → ℂ) with hudef
  set v : W → G → ℂ := fun x => ((pairImage S1 a W ν₁ Γ₁ Γ₂ x : virtualChars G) : G → ℂ)
    with hvdef
  have hSrange : W = Set.range u := (Subtype.range_coe (s := W)).symm
  have hgramu : ∀ i j : W, cfInner (u i) (u j) = if i = j then (1 : ℂ) else 0 := by
    intro i j
    rw [hudef, cfInner_eq_ite_of_mem_Irr (hWIrr i.2) (hWIrr j.2)]
    congr 1
    simp [Subtype.ext_iff]
  have hgramv : ∀ i j : W, cfInner (v i) (v j) = if i = j then (1 : ℂ) else 0 :=
    fun i j => cfInner_pairImage_pairImage rfl hS1Irr haS1 hbS1 hab hν₁ Γ₁ Γ₂
      h11 h22 h12 ho1 ho2 i j
  have hvmem : ∀ i : W, v i ∈ Submodule.span ℤ (Irr G) :=
    fun i => mem_span_Irr_of_mem_virtualChars (pairImage S1 a W ν₁ Γ₁ Γ₂ i).2
  obtain ⟨ν, hνiso, hνval⟩ := exists_addMonoidHom_isometry_of_gram_eq (g := fun _ : W => (1 : ℂ))
    hSrange hgramu (fun _ => one_ne_zero) hvmem hgramv
  have hνS1 : ∀ t ∈ S1, ∀ h : t ∈ Submodule.span ℤ W,
      ((ν ⟨t, h⟩ : virtualChars G) : G → ℂ) = spanImage S1 ν₁ t := by
    intro t ht h
    rw [hνval ⟨t, hS1W ht⟩ ⟨t, h⟩ rfl, hvdef]
    change ((pairImage S1 a W ν₁ Γ₁ Γ₂ ⟨t, hS1W ht⟩ : virtualChars G) : G → ℂ) = _
    rw [pairImage_of_mem Γ₁ Γ₂ ht (hS1W ht), spanImage_of_mem ht]
  have hνa : ∀ h : a ∈ Submodule.span ℤ W,
      ((ν ⟨a, h⟩ : virtualChars G) : G → ℂ) = (Γ₁ : G → ℂ) := by
    intro h
    rw [hνval ⟨a, haW⟩ ⟨a, h⟩ rfl, hvdef]
    change ((pairImage S1 a W ν₁ Γ₁ Γ₂ ⟨a, haW⟩ : virtualChars G) : G → ℂ) = _
    rw [pairImage_left Γ₁ Γ₂ haS1 haW]
  have hνb : ∀ h : b ∈ Submodule.span ℤ W,
      ((ν ⟨b, h⟩ : virtualChars G) : G → ℂ) = (Γ₂ : G → ℂ) := by
    intro h
    rw [hνval ⟨b, hbW⟩ ⟨b, h⟩ rfl, hvdef]
    change ((pairImage S1 a W ν₁ Γ₁ Γ₂ ⟨b, hbW⟩ : virtualChars G) : G → ℂ) = _
    rw [pairImage_right Γ₁ Γ₂ hbS1 hab hbW]
  have hνgen : ∀ x ∈ pairGens S1 a b ψ k, ∀ hx : x ∈ Submodule.span ℤ W,
      ((ν ⟨x, hx⟩ : virtualChars G) : G → ℂ) = tau x := by
    intro x hxg hx
    rcases mem_pairGens_iff.1 hxg with ⟨χ, hχ, rfl⟩ | rfl | rfl
    · rw [show (⟨χ - ψ, hx⟩ : Submodule.span ℤ W)
          = ⟨χ, Submodule.subset_span (hS1W hχ)⟩
            - ⟨ψ, Submodule.subset_span (hS1W hψ)⟩ from rfl, map_sub]
      show ((ν _ : virtualChars G) : G → ℂ) - ((ν _ : virtualChars G) : G → ℂ) = _
      rw [hνS1 χ hχ _, hνS1 ψ hψ _, htau1 χ hχ]
    · rw [show (⟨a - k • ψ, hx⟩ : Submodule.span ℤ W)
          = ⟨a, Submodule.subset_span haW⟩
            - k • ⟨ψ, Submodule.subset_span (hS1W hψ)⟩ from rfl, map_sub, map_zsmul]
      show ((ν _ : virtualChars G) : G → ℂ) - ((k • (ν _) : virtualChars G) : G → ℂ) = _
      rw [SetLike.val_smul, hνa _, hνS1 ψ hψ _, htaua]
    · rw [show (⟨b - k • ψ, hx⟩ : Submodule.span ℤ W)
          = ⟨b, Submodule.subset_span hbW⟩
            - k • ⟨ψ, Submodule.subset_span (hS1W hψ)⟩ from rfl, map_sub, map_zsmul]
      show ((ν _ : virtualChars G) : G → ℂ) - ((k • (ν _) : virtualChars G) : G → ℂ) = _
      rw [SetLike.val_smul, hνb _, hνS1 ψ hψ _, htaub]
  refine ⟨ν, ⟨hνiso, ?_⟩, ?_⟩
  · refine addMonoidHom_eq_of_eq_on_generators (T := pairGens S1 a b ψ k)
      (fun t ht => span_pairGens_le hψ hdeg hdega hdegb (Submodule.subset_span ht))
      (charSpanZero_le_span_pairGens hdeg hdega hdegb he haS1 hbS1 hab)
      (ν.comp (Submodule.inclusion (charSpanZero_le W)).toAddMonoidHom) (baselineOn hc hWS) ?_
    intro t ht
    refine Subtype.ext ?_
    rw [coe_baselineOn]
    exact hνgen t ht _
  · intro f
    refine addMonoidHom_eq_of_eq_on_generators (T := (S1 : Set (L → ℂ)))
      (fun t ht => Submodule.subset_span ht) le_rfl
      (ν.comp (Submodule.inclusion (Submodule.span_mono hS1W)).toAddMonoidHom) ν₁ ?_ f
    intro t ht
    refine Subtype.ext ?_
    change ((ν ⟨t, Submodule.span_mono hS1W (Submodule.subset_span ht)⟩ : virtualChars G) : G → ℂ)
      = ((ν₁ ⟨t, Submodule.subset_span ht⟩ : virtualChars G) : G → ℂ)
    rw [hνS1 t ht _, spanImage_of_mem ht]

end Pair

structure IsWeightedEqualityConfig (S S1 S3 Q : Finset (L → ℂ)) (tau : (L → ℂ) → G → ℂ)
    (R : (L → ℂ) → Finset (G → ℂ))
    (ν₁ : Submodule.span ℤ (S1 : Set (L → ℂ)) →+ virtualChars G)
    (ν₃ : Submodule.span ℤ (S3 : Set (L → ℂ)) →+ virtualChars G)
    (k d : ℤ) (D : Submodule ℤ (L → ℂ)) (tauhat : D →+ virtualChars G) (α ψ : L → ℂ) : Prop where
  subcoherent : IsSubcoherent S tau R
  union : (S : Set (L → ℂ)) = (S1 : Set (L → ℂ)) ∪ (S3 : Set (L → ℂ))
  disjoint : Disjoint S1 S3
  S1_nonempty : S1.Nonempty
  S3_nonempty : S3.Nonempty
  S1_star : ∀ χ ∈ S1, star χ ∈ S1
  S3_star : ∀ χ ∈ S3, star χ ∈ S3
  nu1_isometry : ∀ f g : Submodule.span ℤ (S1 : Set (L → ℂ)),
    cfInner (ν₁ f : G → ℂ) (ν₁ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ)
  nu1_eq_tau : ∀ f : charSpanZero (S1 : Set (L → ℂ)),
    (ν₁ (Submodule.inclusion (charSpanZero_le _) f) : G → ℂ) = tau (f : L → ℂ)
  nu3_isometry : ∀ f g : Submodule.span ℤ (S3 : Set (L → ℂ)),
    cfInner (ν₃ f : G → ℂ) (ν₃ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ)
  nu3_eq_tau : ∀ f : charSpanZero (S3 : Set (L → ℂ)),
    (ν₃ (Submodule.inclusion (charSpanZero_le _) f) : G → ℂ) = tau (f : L → ℂ)
  one_lt_k : 1 < k
  d_pos : 0 < d
  S1_subset_Irr : (S1 : Set (L → ℂ)) ⊆ Irr L
  card_S1 : (S1.card : ℤ) = 2 * k
  S1_degree : ∀ χ ∈ S1, χ 1 = (d : ℂ)
  S3_degree : ∀ χ ∈ S3, χ 1 = ((k * d : ℤ) : ℂ)
  Q_subset : Q ⊆ S3
  Q_subset_Irr : (Q : Set (L → ℂ)) ⊆ Irr L
  Q_nonempty : Q.Nonempty
  Q_star : ∀ χ ∈ Q, star χ ∈ Q
  charSpanZero_le_D : charSpanZero (S : Set (L → ℂ)) ≤ D
  alpha_mem : α ∈ D
  tauhat_isometry : ∀ f g : D, cfInner (tauhat f : G → ℂ) (tauhat g : G → ℂ)
    = cfInner (f : L → ℂ) (g : L → ℂ)
  tauhat_eq_tau : ∀ f : charSpanZero (S : Set (L → ℂ)),
    (tauhat (Submodule.inclusion charSpanZero_le_D f) : G → ℂ) = tau (f : L → ℂ)
  psi_mem : ψ ∈ S1
  alpha_inner_psi : cfInner α ψ = -1
  alpha_inner_ne : ∀ χ ∈ S, χ ≠ ψ → cfInner α χ = 0
  tauhat_alpha_orthogonal : ∀ f : Submodule.span ℤ (S3 : Set (L → ℂ)),
    cfInner (tauhat ⟨α, alpha_mem⟩ : G → ℂ) (ν₃ f : G → ℂ) = 0

namespace IsWeightedEqualityConfig

variable {S1 S3 Q : Finset (L → ℂ)}
  {ν₁ : Submodule.span ℤ (S1 : Set (L → ℂ)) →+ virtualChars G}
  {ν₃ : Submodule.span ℤ (S3 : Set (L → ℂ)) →+ virtualChars G}
  {k d : ℤ} {D : Submodule ℤ (L → ℂ)} {tauhat : D →+ virtualChars G} {α ψ : L → ℂ}
  (hcfg : IsWeightedEqualityConfig S S1 S3 Q tau R ν₁ ν₃ k d D tauhat α ψ)

include hcfg

theorem S1_subset : S1 ⊆ S := fun x hx => by
  have h : (x : L → ℂ) ∈ (S : Set (L → ℂ)) := by rw [hcfg.union]; exact Or.inl hx
  exact h

theorem S3_subset : S3 ⊆ S := fun x hx => by
  have h : (x : L → ℂ) ∈ (S : Set (L → ℂ)) := by rw [hcfg.union]; exact Or.inr hx
  exact h

theorem Q_subset_S : Q ⊆ S := hcfg.Q_subset.trans hcfg.S3_subset

theorem isCoherentWith_nu1 :
    IsCoherentWith (S1 : Set (L → ℂ)) (baselineOn hcfg.subcoherent
      (by exact_mod_cast hcfg.S1_subset)) ν₁ where
  inner_eq := hcfg.nu1_isometry
  eq_on_zero f := Subtype.ext (by rw [hcfg.nu1_eq_tau f, coe_baselineOn])

theorem isCoherentWith_nu3 :
    IsCoherentWith (S3 : Set (L → ℂ)) (baselineOn hcfg.subcoherent
      (by exact_mod_cast hcfg.S3_subset)) ν₃ where
  inner_eq := hcfg.nu3_isometry
  eq_on_zero f := Subtype.ext (by rw [hcfg.nu3_eq_tau f, coe_baselineOn])

theorem cfInner_nu1_nu3_eq_zero (f : Submodule.span ℤ (S1 : Set (L → ℂ)))
    (g : Submodule.span ℤ (S3 : Set (L → ℂ))) :
    cfInner (ν₁ f : G → ℂ) (ν₃ g : G → ℂ) = 0 :=
  DisjointCoherentBlocks.cfInner_eq_zero_of_disjoint hcfg.subcoherent hcfg.S1_subset
    (fun _ h => hcfg.S1_star _ h) hcfg.isCoherentWith_nu1 (fun f => coe_baselineOn _ _ f)
    hcfg.S3_subset (fun _ h => hcfg.S3_star _ h) hcfg.isCoherentWith_nu3
    (fun f => coe_baselineOn _ _ f) hcfg.disjoint f g

set_option maxHeartbeats 2000000 in
theorem exists_projection_of_mem_Q {lam : L → ℂ} (hlam : lam ∈ Q) :
    ∃ Γ : G → ℂ, Γ ∈ Submodule.span ℤ (Irr G) ∧ cfInner Γ Γ = 1 ∧
      (∀ f : Submodule.span ℤ (S1 : Set (L → ℂ)), cfInner Γ (ν₁ f : G → ℂ) = 0) ∧
      cfInner Γ (tau (lam - star lam)) = 1 ∧
      tau (lam - k • ψ) = Γ - k • spanImage S1 ν₁ ψ := by
  classical
  have hnG : Nonempty G := ⟨1⟩
  have hlam3 : lam ∈ S3 := hcfg.Q_subset hlam
  have hslam : star lam ∈ Q := hcfg.Q_star _ hlam
  have hslam3 : star lam ∈ S3 := hcfg.Q_subset hslam
  have hslamne : star lam ≠ lam := hcfg.subcoherent.star_ne lam (hcfg.Q_subset_S hlam)
  have hmemS : ∀ {χ χ' : L → ℂ}, χ ∈ S → χ' ∈ S → χ 1 = χ' 1 →
      χ - χ' ∈ charSpanZero (S : Set (L → ℂ)) := fun hχ hχ' hd =>
    mem_charSpanZero.2 ⟨Submodule.sub_mem _ (Submodule.subset_span hχ)
      (Submodule.subset_span hχ'), by rw [Pi.sub_apply, hd, sub_self]⟩
  have hisoT : ∀ {u v : L → ℂ}, u ∈ charSpanZero (S : Set (L → ℂ)) →
      v ∈ charSpanZero (S : Set (L → ℂ)) → cfInner (tau u) (tau v) = cfInner u v := fun hu hv =>
    cfInner_tau_tau hcfg.subcoherent (mem_intSpanZeroAtOne.2 (mem_charSpanZero.1 hu))
      (mem_intSpanZeroAtOne.2 (mem_charSpanZero.1 hv))
  have hcfS : ∀ {χ χ' : L → ℂ}, χ ∈ S → χ' ∈ S → χ ≠ χ' → cfInner χ χ' = 0 := by
    intro χ χ' hχ hχ' hne
    rw [← charInner_eq_cfInner]
    exact hcfg.subcoherent.charInner_eq_zero χ hχ χ' hχ' hne
  have hneS13 : ∀ {χ χ' : L → ℂ}, χ ∈ S1 → χ' ∈ S3 → χ ≠ χ' := fun hχ hχ' h =>
    (Finset.disjoint_left.1 hcfg.disjoint hχ) (h ▸ hχ')
  have hβmem : lam - k • ψ ∈ charSpanZero (S : Set (L → ℂ)) := by
    refine mem_charSpanZero.2 ⟨Submodule.sub_mem _
      (Submodule.subset_span (hcfg.S3_subset hlam3))
      (Submodule.smul_mem _ _ (Submodule.subset_span (hcfg.S1_subset hcfg.psi_mem))), ?_⟩
    rw [Pi.sub_apply, Pi.smul_apply, zsmul_eq_mul, hcfg.S3_degree _ hlam3,
      hcfg.S1_degree _ hcfg.psi_mem]
    push_cast
    ring
  have hmemS1 : ∀ {χ χ' : L → ℂ}, χ ∈ S1 → χ' ∈ S1 →
      χ - χ' ∈ charSpanZero (S : Set (L → ℂ)) := fun hχ hχ' =>
    hmemS (hcfg.S1_subset hχ) (hcfg.S1_subset hχ')
      (by rw [hcfg.S1_degree _ hχ, hcfg.S1_degree _ hχ'])
  have hmemS3 : ∀ {χ χ' : L → ℂ}, χ ∈ S3 → χ' ∈ S3 →
      χ - χ' ∈ charSpanZero (S : Set (L → ℂ)) := fun hχ hχ' =>
    hmemS (hcfg.S3_subset hχ) (hcfg.S3_subset hχ')
      (by rw [hcfg.S3_degree _ hχ, hcfg.S3_degree _ hχ'])
  have htauS1 : ∀ {χ χ' : L → ℂ}, χ ∈ S1 → χ' ∈ S1 →
      tau (χ - χ') = spanImage S1 ν₁ χ - spanImage S1 ν₁ χ' := by
    intro χ χ' hχ hχ'
    have hmem : χ - χ' ∈ charSpanZero (S1 : Set (L → ℂ)) :=
      mem_charSpanZero.2 ⟨Submodule.sub_mem _ (Submodule.subset_span hχ)
        (Submodule.subset_span hχ'), by simp [hcfg.S1_degree _ hχ, hcfg.S1_degree _ hχ']⟩
    rw [spanImage_sub_eq hχ hχ', ← hcfg.nu1_eq_tau ⟨χ - χ', hmem⟩]
    rfl
  have htauS3 : ∀ {χ χ' : L → ℂ}, χ ∈ S3 → χ' ∈ S3 →
      tau (χ - χ') = spanImage S3 ν₃ χ - spanImage S3 ν₃ χ' := by
    intro χ χ' hχ hχ'
    have hmem : χ - χ' ∈ charSpanZero (S3 : Set (L → ℂ)) :=
      mem_charSpanZero.2 ⟨Submodule.sub_mem _ (Submodule.subset_span hχ)
        (Submodule.subset_span hχ'), by simp [hcfg.S3_degree _ hχ, hcfg.S3_degree _ hχ']⟩
    rw [spanImage_sub_eq hχ hχ', ← hcfg.nu3_eq_tau ⟨χ - χ', hmem⟩]
    rfl
  have hηη : ∀ χ ∈ S1, ∀ χ' ∈ S1,
      cfInner (spanImage S1 ν₁ χ) (spanImage S1 ν₁ χ') = if χ = χ' then 1 else 0 := by
    intro χ hχ χ' hχ'
    rw [spanImage_of_mem hχ, spanImage_of_mem hχ', hcfg.nu1_isometry]
    exact cfInner_eq_ite_of_mem_Irr (hcfg.S1_subset_Irr hχ) (hcfg.S1_subset_Irr hχ')
  have hθθ : ∀ χ ∈ Q, ∀ χ' ∈ Q,
      cfInner (spanImage S3 ν₃ χ) (spanImage S3 ν₃ χ') = if χ = χ' then 1 else 0 := by
    intro χ hχ χ' hχ'
    rw [spanImage_of_mem (hcfg.Q_subset hχ), spanImage_of_mem (hcfg.Q_subset hχ'),
      hcfg.nu3_isometry]
    exact cfInner_eq_ite_of_mem_Irr (hcfg.Q_subset_Irr hχ) (hcfg.Q_subset_Irr hχ')
  have hηθ : ∀ χ ∈ S1, ∀ χ' ∈ Q,
      cfInner (spanImage S1 ν₁ χ) (spanImage S3 ν₃ χ') = 0 := by
    intro χ hχ χ' hχ'
    rw [spanImage_of_mem hχ, spanImage_of_mem (hcfg.Q_subset hχ')]
    exact hcfg.cfInner_nu1_nu3_eq_zero _ _
  set f : G → ℂ := tau (lam - k • ψ) with hfdef
  set Z : G → ℂ := (tauhat ⟨α, hcfg.alpha_mem⟩ : G → ℂ) with hZdef
  have hfIrr : f ∈ Submodule.span ℤ (Irr G) :=
    mem_span_Irr_of_mem_virtualChars
      (tau_mem_virtualChars hcfg.subcoherent (mem_intSpanZeroAtOne.2 (mem_charSpanZero.1 hβmem)))
  have hZIrr : Z ∈ Submodule.span ℤ (Irr G) :=
    mem_span_Irr_of_mem_virtualChars (tauhat ⟨α, hcfg.alpha_mem⟩).2
  obtain ⟨a, ha⟩ := exists_int_cfInner_family hfIrr
    (fun χ : L → ℂ => spanImage_mem_span_Irr (T := S1) (ν := ν₁) χ)
  obtain ⟨g, hg⟩ := exists_int_cfInner_family hfIrr
    (fun χ : L → ℂ => spanImage_mem_span_Irr (T := S3) (ν := ν₃) χ)
  obtain ⟨p, hp⟩ := exists_int_cfInner_family hZIrr
    (fun χ : L → ℂ => spanImage_mem_span_Irr (T := S1) (ν := ν₁) χ)
  have hff : cfInner f f = ((1 + k ^ 2 : ℤ) : ℂ) := by
    rw [hfdef, hisoT hβmem hβmem]
    have h1 : cfInner lam lam = 1 := by
      rw [cfInner_eq_ite_of_mem_Irr (hcfg.Q_subset_Irr hlam) (hcfg.Q_subset_Irr hlam), if_pos rfl]
    have h2 : cfInner lam ψ = 0 :=
      hcfS (hcfg.S3_subset hlam3) (hcfg.S1_subset hcfg.psi_mem)
        (Ne.symm (hneS13 hcfg.psi_mem hlam3))
    have h3 : cfInner ψ lam = 0 :=
      hcfS (hcfg.S1_subset hcfg.psi_mem) (hcfg.S3_subset hlam3) (hneS13 hcfg.psi_mem hlam3)
    have h4 : cfInner ψ ψ = 1 := by
      rw [cfInner_eq_ite_of_mem_Irr (hcfg.S1_subset_Irr hcfg.psi_mem)
        (hcfg.S1_subset_Irr hcfg.psi_mem), if_pos rfl]
    rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, h1, cfInner_zsmul_left,
      cfInner_zsmul_right, cfInner_zsmul_right, cfInner_zsmul_left, h2, h3, h4]
    push_cast
    ring
  set b : ℤ := a ψ + k with hbdef
  have haψ : a ψ = b - k := by omega
  have ha1 : ∀ χ ∈ S1, χ ≠ ψ → a χ = b := by
    intro χ hχ hne
    have hkey : cfInner f (spanImage S1 ν₁ χ - spanImage S1 ν₁ ψ) = ((k : ℤ) : ℂ) := by
      rw [← htauS1 hχ hcfg.psi_mem, hfdef, hisoT hβmem (hmemS1 hχ hcfg.psi_mem)]
      have h1 : cfInner lam χ = 0 :=
        hcfS (hcfg.S3_subset hlam3) (hcfg.S1_subset hχ) (Ne.symm (hneS13 hχ hlam3))
      have h2 : cfInner lam ψ = 0 :=
        hcfS (hcfg.S3_subset hlam3) (hcfg.S1_subset hcfg.psi_mem)
          (Ne.symm (hneS13 hcfg.psi_mem hlam3))
      have h3 : cfInner ψ χ = 0 := by
        rw [cfInner_eq_ite_of_mem_Irr (hcfg.S1_subset_Irr hcfg.psi_mem)
          (hcfg.S1_subset_Irr hχ), if_neg (Ne.symm hne)]
      have h4 : cfInner ψ ψ = 1 := by
        rw [cfInner_eq_ite_of_mem_Irr (hcfg.S1_subset_Irr hcfg.psi_mem)
          (hcfg.S1_subset_Irr hcfg.psi_mem), if_pos rfl]
      rw [cfInner_sub_right, cfInner_sub_left, cfInner_sub_left, h1, h2,
        cfInner_zsmul_left, cfInner_zsmul_left, h3, h4]
      ring
    have := int_coeff_sub_eq (ha χ) (ha ψ) hkey
    omega
  have hgdiff : g lam - g (star lam) = 1 := by
    have hkey : cfInner f (spanImage S3 ν₃ lam - spanImage S3 ν₃ (star lam)) = ((1 : ℤ) : ℂ) := by
      rw [← htauS3 hlam3 hslam3, hfdef, hisoT hβmem (hmemS3 hlam3 hslam3)]
      have h1 : cfInner lam lam = 1 := by
        rw [cfInner_eq_ite_of_mem_Irr (hcfg.Q_subset_Irr hlam) (hcfg.Q_subset_Irr hlam),
          if_pos rfl]
      have h2 : cfInner lam (star lam) = 0 :=
        hcfS (hcfg.S3_subset hlam3) (hcfg.S3_subset hslam3) (Ne.symm hslamne)
      have h3 : cfInner ψ lam = 0 :=
        hcfS (hcfg.S1_subset hcfg.psi_mem) (hcfg.S3_subset hlam3) (hneS13 hcfg.psi_mem hlam3)
      have h4 : cfInner ψ (star lam) = 0 :=
        hcfS (hcfg.S1_subset hcfg.psi_mem) (hcfg.S3_subset hslam3) (hneS13 hcfg.psi_mem hslam3)
      rw [cfInner_sub_right, cfInner_sub_left, cfInner_sub_left, h1, h2,
        cfInner_zsmul_left, cfInner_zsmul_left, h3, h4]
      push_cast
      ring
    exact int_coeff_sub_eq (hg lam) (hg (star lam)) hkey
  have hZθ : ∀ χ ∈ Q, cfInner Z (spanImage S3 ν₃ χ) = 0 := by
    intro χ hχ
    rw [hZdef, spanImage_of_mem (hcfg.Q_subset hχ)]
    exact hcfg.tauhat_alpha_orthogonal _
  set x : ℤ := p ψ + 1 with hxdef
  have hpψ : p ψ = x - 1 := by omega
  have hp1 : ∀ χ ∈ S1, χ ≠ ψ → p χ = x := by
    intro χ hχ hne
    have hkey : cfInner Z (spanImage S1 ν₁ χ - spanImage S1 ν₁ ψ) = ((1 : ℤ) : ℂ) := by
      rw [← htauS1 hχ hcfg.psi_mem, hZdef,
        ← hcfg.tauhat_eq_tau ⟨χ - ψ, hmemS1 hχ hcfg.psi_mem⟩, hcfg.tauhat_isometry]
      show cfInner α (χ - ψ) = _
      rw [cfInner_sub_right, hcfg.alpha_inner_psi,
        hcfg.alpha_inner_ne χ (hcfg.S1_subset hχ) hne]
      push_cast
      ring
    have := int_coeff_sub_eq (hp χ) (hp ψ) hkey
    omega
  have hZf : cfInner Z f = (k : ℂ) := by
    rw [hfdef, hZdef, ← hcfg.tauhat_eq_tau ⟨lam - k • ψ, hβmem⟩, hcfg.tauhat_isometry]
    show cfInner α (lam - k • ψ) = _
    have h1 : cfInner α lam = 0 :=
      hcfg.alpha_inner_ne lam (hcfg.Q_subset_S hlam)
        (Ne.symm (hneS13 hcfg.psi_mem hlam3))
    rw [cfInner_sub_right, h1, cfInner_zsmul_right, hcfg.alpha_inner_psi]
    ring
  obtain ⟨hb0, hBsum, hfP⟩ := b_eq_zero_of_alpha_projection (A := S1) (B := Q)
    (η := spanImage S1 ν₁) (θ := spanImage S3 ν₃) (i₀ := ψ) (j₁ := lam) (j₂ := star lam)
    (K := k) (a := a) (g := g) (p := p) (b := b) (x := x)
    hηη hθθ hηθ (fun χ _ => ha χ) (fun χ _ => hg χ) hff hcfg.psi_mem hcfg.card_S1 hcfg.one_lt_k
    haψ ha1 hlam hslam (Ne.symm hslamne) hgdiff hZθ (fun χ _ => hp χ) hpψ hp1 hZf
  refine ⟨∑ χ ∈ Q, (g χ : ℂ) • spanImage S3 ν₃ χ,
    sum_zsmul_spanImage_mem_span_Irr (T := S3) (ν := ν₃) Q g, ?_, ?_, ?_, ?_⟩
  · rw [cfInner_self_sum_zsmul_of_orthonormalOn hθθ, hBsum]
    norm_num
  · intro w
    rw [cfInner_sum_left]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [cfInner_smul_left, ← conj_cfInner, spanImage_of_mem (hcfg.Q_subset hj),
      hcfg.cfInner_nu1_nu3_eq_zero, map_zero, mul_zero]
  · rw [htauS3 hlam3 hslam3, cfInner_sub_right,
      cfInner_sum_smul_right_of_orthonormalOn hθθ hlam,
      cfInner_sum_smul_right_of_orthonormalOn hθθ hslam]
    have hd : ((g lam - g (star lam) : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by rw [hgdiff]
    push_cast at hd
    linear_combination hd
  ·
    rw [hfP]
    have hS1part : (∑ χ ∈ S1, (a χ : ℂ) • spanImage S1 ν₁ χ)
        = -(k : ℂ) • spanImage S1 ν₁ ψ := by
      rw [← Finset.sum_erase_add S1 _ hcfg.psi_mem,
        Finset.sum_eq_zero (fun χ hχ => by
          rw [ha1 χ (Finset.mem_of_mem_erase hχ) (Finset.ne_of_mem_erase hχ), hb0]
          simp), zero_add, haψ, hb0]
      push_cast
      ring_nf
    rw [hS1part, ← Int.cast_smul_eq_zsmul ℂ k (spanImage S1 ν₁ ψ)]
    push_cast
    module

set_option maxHeartbeats 1000000 in
theorem exists_isCoherentWith_insert_pair {lam : L → ℂ} (hlam : lam ∈ Q) :
    ∃ ν : Submodule.span ℤ ((S1 : Set (L → ℂ)) ∪ {lam, star lam}) →+ virtualChars G,
      IsCoherentWith ((S1 : Set (L → ℂ)) ∪ {lam, star lam})
        (baselineOn hcfg.subcoherent (by
          refine Set.union_subset (by exact_mod_cast hcfg.S1_subset) ?_
          intro x hx
          rcases hx with rfl | hx
          · exact_mod_cast hcfg.Q_subset_S hlam
          · rw [Set.mem_singleton_iff] at hx
            subst hx
            exact_mod_cast hcfg.Q_subset_S (hcfg.Q_star _ hlam))) ν ∧
      ∀ f : Submodule.span ℤ (S1 : Set (L → ℂ)),
        ν (Submodule.inclusion (Submodule.span_mono Set.subset_union_left) f) = ν₁ f := by
  classical
  obtain ⟨Γ, hΓIrr, hΓΓ, hΓν, hΓz, hbeta⟩ := hcfg.exists_projection_of_mem_Q hlam
  have hlam3 : lam ∈ S3 := hcfg.Q_subset hlam
  have hslam : star lam ∈ Q := hcfg.Q_star _ hlam
  have hslam3 : star lam ∈ S3 := hcfg.Q_subset hslam
  have hslamne : star lam ≠ lam := hcfg.subcoherent.star_ne lam (hcfg.Q_subset_S hlam)
  have hcfS : ∀ {χ χ' : L → ℂ}, χ ∈ S → χ' ∈ S → χ ≠ χ' → cfInner χ χ' = 0 := by
    intro χ χ' hχ hχ' hne
    rw [← charInner_eq_cfInner]
    exact hcfg.subcoherent.charInner_eq_zero χ hχ χ' hχ' hne
  have hmemS : ∀ {χ χ' : L → ℂ}, χ ∈ S → χ' ∈ S → χ 1 = χ' 1 →
      χ - χ' ∈ charSpanZero (S : Set (L → ℂ)) := fun hχ hχ' hd =>
    mem_charSpanZero.2 ⟨Submodule.sub_mem _ (Submodule.subset_span hχ)
      (Submodule.subset_span hχ'), by rw [Pi.sub_apply, hd, sub_self]⟩
  have hβmem : ∀ {u : L → ℂ}, u ∈ S3 → u - k • ψ ∈ charSpanZero (S : Set (L → ℂ)) := by
    intro u hu
    refine mem_charSpanZero.2 ⟨Submodule.sub_mem _
      (Submodule.subset_span (hcfg.S3_subset hu))
      (Submodule.smul_mem _ _ (Submodule.subset_span (hcfg.S1_subset hcfg.psi_mem))), ?_⟩
    rw [Pi.sub_apply, Pi.smul_apply, zsmul_eq_mul, hcfg.S3_degree _ hu,
      hcfg.S1_degree _ hcfg.psi_mem]
    push_cast
    ring
  have hzmem : lam - star lam ∈ charSpanZero (S : Set (L → ℂ)) :=
    hmemS (hcfg.S3_subset hlam3) (hcfg.S3_subset hslam3)
      (by rw [hcfg.S3_degree _ hlam3, hcfg.S3_degree _ hslam3])
  have hzmemS3 : lam - star lam ∈ charSpanZero (S3 : Set (L → ℂ)) :=
    mem_charSpanZero.2 ⟨Submodule.sub_mem _ (Submodule.subset_span hlam3)
      (Submodule.subset_span hslam3), by
      simp [hcfg.S3_degree _ hlam3, hcfg.S3_degree _ hslam3]⟩
  have htauSub : ∀ {u v : L → ℂ}, u ∈ charSpanZero (S : Set (L → ℂ)) →
      v ∈ charSpanZero (S : Set (L → ℂ)) → tau (u - v) = tau u - tau v := fun hu hv =>
    hcfg.subcoherent.map_sub (mem_intSpanZeroAtOne.2 (mem_charSpanZero.1 hu))
      (mem_intSpanZeroAtOne.2 (mem_charSpanZero.1 hv))
  set z : G → ℂ := tau (lam - star lam) with hzdef
  have hz : z = spanImage S3 ν₃ lam - spanImage S3 ν₃ (star lam) := by
    rw [hzdef, spanImage_sub_eq hlam3 hslam3, ← hcfg.nu3_eq_tau ⟨lam - star lam, hzmemS3⟩]
    rfl
  have hzz : cfInner z z = 2 := by
    rw [hz]
    have h1 : cfInner (spanImage S3 ν₃ lam) (spanImage S3 ν₃ lam) = 1 := by
      rw [spanImage_of_mem hlam3, hcfg.nu3_isometry,
        cfInner_eq_ite_of_mem_Irr (hcfg.Q_subset_Irr hlam) (hcfg.Q_subset_Irr hlam), if_pos rfl]
    have h2 : cfInner (spanImage S3 ν₃ lam) (spanImage S3 ν₃ (star lam)) = 0 := by
      rw [spanImage_of_mem hlam3, spanImage_of_mem hslam3, hcfg.nu3_isometry]
      exact hcfS (hcfg.S3_subset hlam3) (hcfg.S3_subset hslam3) (Ne.symm hslamne)
    have h3 : cfInner (spanImage S3 ν₃ (star lam)) (spanImage S3 ν₃ lam) = 0 := by
      rw [spanImage_of_mem hlam3, spanImage_of_mem hslam3, hcfg.nu3_isometry]
      exact hcfS (hcfg.S3_subset hslam3) (hcfg.S3_subset hlam3) hslamne
    have h4 : cfInner (spanImage S3 ν₃ (star lam)) (spanImage S3 ν₃ (star lam)) = 1 := by
      rw [spanImage_of_mem hslam3, hcfg.nu3_isometry,
        cfInner_eq_ite_of_mem_Irr (hcfg.Q_subset_Irr hslam) (hcfg.Q_subset_Irr hslam), if_pos rfl]
    rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, h1, h2, h3, h4]
    ring
  have hXop : ∀ χ' ∈ S3, ∀ f : Submodule.span ℤ (S1 : Set (L → ℂ)),
      cfInner (spanImage S3 ν₃ χ') (ν₁ f : G → ℂ) = 0 := by
    intro χ' hχ' f
    rw [spanImage_of_mem hχ', ← conj_cfInner, hcfg.cfInner_nu1_nu3_eq_zero, map_zero]
  have hzν : ∀ f : Submodule.span ℤ (S1 : Set (L → ℂ)), cfInner z (ν₁ f : G → ℂ) = 0 := by
    intro f
    rw [hz, cfInner_sub_left, hXop lam hlam3 f, hXop (star lam) hslam3 f]
    ring
  have hzΓ : cfInner z Γ = 1 := by rw [← conj_cfInner, hΓz]; simp
  have hΓ2 : cfInner (Γ - z) (Γ - z) = 1 := by
    rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, hΓΓ, hΓz, hzΓ, hzz]
    ring
  have hΓΓ2 : cfInner Γ (Γ - z) = 0 := by rw [cfInner_sub_right, hΓΓ, hΓz]; ring
  have hΓ2ν : ∀ f : Submodule.span ℤ (S1 : Set (L → ℂ)),
      cfInner (Γ - z) (ν₁ f : G → ℂ) = 0 := by
    intro f
    rw [cfInner_sub_left, hΓν f, hzν f]
    ring
  have hzIrr : z ∈ Submodule.span ℤ (Irr G) :=
    mem_span_Irr_of_mem_virtualChars
      (tau_mem_virtualChars hcfg.subcoherent (mem_intSpanZeroAtOne.2 (mem_charSpanZero.1 hzmem)))
  have hΓ2Irr : (Γ - z) ∈ Submodule.span ℤ (Irr G) := Submodule.sub_mem _ hΓIrr hzIrr
  have hlamS1 : lam ∉ (S1 : Set (L → ℂ)) := fun h =>
    (Finset.disjoint_left.1 hcfg.disjoint h) hlam3
  have hslamS1 : star lam ∉ (S1 : Set (L → ℂ)) := fun h =>
    (Finset.disjoint_left.1 hcfg.disjoint h) hslam3
  have hne : lam ≠ star lam := Ne.symm hslamne
  have hdeglam : lam 1 = (k : ℂ) * (d : ℂ) := by
    rw [hcfg.S3_degree _ hlam3]; push_cast; ring
  have hdegslam : (star lam) 1 = (k : ℂ) * (d : ℂ) := by
    rw [hcfg.S3_degree _ hslam3]; push_cast; ring
  have hdne : ((d : ℂ)) ≠ 0 := by
    have := hcfg.d_pos
    exact_mod_cast this.ne'
  have htau1 : ∀ χ ∈ S1, tau (χ - ψ) = spanImage S1 ν₁ χ - spanImage S1 ν₁ ψ := by
    intro χ hχ
    have hmem : χ - ψ ∈ charSpanZero (S1 : Set (L → ℂ)) :=
      mem_charSpanZero.2 ⟨Submodule.sub_mem _ (Submodule.subset_span hχ)
        (Submodule.subset_span hcfg.psi_mem), by
        simp [hcfg.S1_degree _ hχ, hcfg.S1_degree _ hcfg.psi_mem]⟩
    rw [spanImage_sub_eq hχ hcfg.psi_mem, ← hcfg.nu1_eq_tau ⟨χ - ψ, hmem⟩]
    rfl
  have htaub : tau (star lam - k • ψ) = (Γ - z) - k • spanImage S1 ν₁ ψ := by
    rw [show star lam - k • ψ = (lam - k • ψ) - (lam - star lam) from by abel,
      htauSub (hβmem hlam3) hzmem, hbeta, ← hzdef]
    abel
  obtain ⟨ν, hν1, hν2⟩ := exists_isCoherentWith_insert_pair_of_orthonormal (e := (d : ℂ)) (k := k)
    (S := S) (S1 := S1) (a := lam) (b := star lam) (ψ := ψ) (ν₁ := ν₁) (tau := tau) (R := R)
    hcfg.subcoherent (by
      refine Set.union_subset (by exact_mod_cast hcfg.S1_subset) ?_
      intro x hx
      rcases hx with rfl | hx
      · exact_mod_cast hcfg.Q_subset_S hlam
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact_mod_cast hcfg.Q_subset_S hslam)
    hcfg.S1_subset_Irr (hcfg.Q_subset_Irr hlam) (hcfg.Q_subset_Irr hslam)
    hlamS1 hslamS1 hne hcfg.psi_mem hcfg.S1_degree hdne hdeglam hdegslam hcfg.nu1_isometry
    ⟨Γ, mem_virtualChars_of_mem_span_Irr hΓIrr⟩
    ⟨Γ - z, mem_virtualChars_of_mem_span_Irr hΓ2Irr⟩ hΓΓ hΓ2 hΓΓ2 hΓν hΓ2ν htau1 hbeta htaub
  exact ⟨ν, hν1, hν2⟩

end IsWeightedEqualityConfig

end WeightedEqualityBridge

end CFSG.FeitThompson
