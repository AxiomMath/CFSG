module

public import CFSG.FeitThompson.Representations.CyclicTITwoColumnHalfSelection
public import CFSG.FeitThompson.Representations.CyclicTIAxesNonrealConjugatePairs
import CFSG.FeitThompson.Representations.ParityRealCharacterInnerProducts
import CFSG.FeitThompson.Representations.IntegralOrthonormalBlockProjection
import CFSG.FeitThompson.Representations.DadeAveragingOrthogonalProjection
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
import CFSG.FeitThompson.Representations.SaturatedSignedArraySingleCharacter
import CFSG.FeitThompson.Representations.ConjugatePairsDisjointBlocksCoherence
import CFSG.FeitThompson.Representations.MixedValuesNormTwoArrayDifference
public import CFSG.FeitThompson.Representations.DisjointAntirealBlocksOrthogonal
public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate ComplexOrder

theorem starIrr_involutive {X : Type*} [Group X] [Finite X] :
    Function.Involutive (starIrr (X := X)) := fun χ => starIrr_starIrr χ

variable {G : Type*} [Group G] [Fintype G]

section Projection

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ι → G → ℂ}

omit [Group G] in
theorem cfInner_self_eq_sum_add (he : IsOrthonormalFamily e) (f : G → ℂ) :
    cfInner f f = (∑ r, cfInner f (e r) * conj (cfInner f (e r)))
      + cfInner (f - ∑ r, cfInner f (e r) • e r) (f - ∑ r, cfInner f (e r) • e r) := by
  have hgram : ∀ p q : ι, cfInner (e p) (e q) = if p = q then (1 : ℂ) else 0 :=
    IntegralBlockProjection.cfInner_of_isOrthonormalFamily he
  set c : ι → ℂ := fun r => cfInner f (e r) with hc
  have h1 : cfInner (∑ r, c r • e r) f = ∑ r, c r * conj (c r) := by
    rw [cfInner_sum_smul_left]
    exact Finset.sum_congr rfl fun r _ => by rw [← conj_cfInner]
  have h2 : cfInner f (∑ r, c r • e r) = ∑ r, conj (c r) * c r := by
    rw [cfInner_sum_smul_right]
  have h3 : cfInner (∑ r, c r • e r) (∑ r, c r • e r) = ∑ r, c r * conj (c r) := by
    rw [cfInner_sum_smul_of_gram_diag (g := fun _ => 1) hgram]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, h1, h2, h3,
    Finset.sum_congr rfl fun r _ => mul_comm (conj (c r)) (c r)]
  ring

omit [Group G] in
theorem sum_mul_conj_cfInner_le (he : IsOrthonormalFamily e) (f : G → ℂ) :
    (∑ r, cfInner f (e r) * conj (cfInner f (e r))) ≤ cfInner f f := by
  rw [cfInner_self_eq_sum_add he f]
  simpa using cfInner_self_nonneg (f - ∑ r, cfInner f (e r) • e r)

omit [Group G] in
theorem cfInner_eq_sub_ite_of_sum_smul_eq (he : IsOrthonormalFamily e) {f : G → ℂ}
    {r₁ : ι} {a : ℤ} {n : ℕ}
    (hproj : ∑ r, cfInner f (e r) • e r = (a : ℂ) • (∑ r, e r) - (n : ℂ) • e r₁) (s : ι) :
    cfInner f (e s) = ((a - if s = r₁ then (n : ℤ) else 0 : ℤ) : ℂ) := by
  have hgram : ∀ p q : ι, cfInner (e p) (e q) = if p = q then (1 : ℂ) else 0 :=
    IntegralBlockProjection.cfInner_of_isOrthonormalFamily he
  have hsum : ∀ s : ι, cfInner (∑ r, e r) (e s) = 1 := by
    intro s
    rw [cfInner_sum_left, Finset.sum_congr rfl fun r _ => hgram r s]
    simp
  have h : cfInner (∑ r, cfInner f (e r) • e r) (e s)
      = cfInner ((a : ℂ) • (∑ r, e r) - (n : ℂ) • e r₁) (e s) := by rw [hproj]
  rw [cfInner_sum_smul_right_of_gram_diag (g := fun _ => 1) hgram, mul_one,
    cfInner_sub_left, cfInner_smul_left, cfInner_smul_left, hsum, hgram] at h
  rw [h]
  by_cases hs : s = r₁
  · subst hs; simp
  · rw [if_neg hs, if_neg (Ne.symm hs)]
    push_cast
    ring

theorem sum_sq_sub_ite (r₁ : ι) (a : ℤ) {n : ℕ} (hcard : Fintype.card ι = n) :
    ∑ r : ι, (a - (if r = r₁ then (n : ℤ) else 0)) ^ 2
      = (n : ℤ) * (a * (a - 2)) + (n : ℤ) ^ 2 := by
  have hterm : ∀ r : ι, (a - (if r = r₁ then (n : ℤ) else 0)) ^ 2
      = a ^ 2 - (if r = r₁ then 2 * a * (n : ℤ) - (n : ℤ) ^ 2 else 0) := by
    intro r
    by_cases h : r = r₁ <;> simp [h]
    ring
  rw [Finset.sum_congr rfl fun r _ => hterm r, Finset.sum_sub_distrib,
    Finset.sum_ite_eq' Finset.univ r₁ (fun _ => 2 * a * (n : ℤ) - (n : ℤ) ^ 2)]
  simp [hcard]
  ring

end Projection

theorem eq_zero_or_eq_two_of_even_of_mul_le {n a : ℤ} (hn : 2 ≤ n) (heven : 2 ∣ a)
    (h : n * (a * (a - 2)) ≤ 2) : a = 0 ∨ a = 2 := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h0, h2⟩ := hcon
  obtain ⟨k, hk⟩ := heven
  have h8 : 8 ≤ a * (a - 2) := by
    subst hk
    rcases lt_trichotomy k 0 with hklt | hkeq | hkgt
    · nlinarith
    · omega
    · rcases eq_or_lt_of_le (show 1 ≤ k by omega) with h1 | h1
      · omega
      · nlinarith
  nlinarith

variable {W W1 W2 : Subgroup G} [Fintype ↥W] {σ : classFun ↥W →ₗ[ℂ] classFun G}

namespace IsCyclicTIPair

theorem star_prodCharEta_starIrr [Finite ↥W1] [Finite ↥W2] (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (i : Irr ↥W1) (j : Irr ↥W2) :
    star (hW.prodCharEta σ i j) = hW.prodCharEta σ (starIrr i) (starIrr j) :=
  hW.star_prodCharEta hσ (coe_starIrr i) (coe_starIrr j)

theorem star_prodCharEtaColSum (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (j : Irr ↥W2) :
    star (hW.prodCharEtaColSum σ j) = hW.prodCharEtaColSum σ (starIrr j) := by
  have h1 := hW.finite_left
  have h2 := hW.finite_right
  have : Fintype (Irr ↥W1) := Fintype.ofFinite _
  rw [hW.prodCharEtaColSum_eq_sum, hW.prodCharEtaColSum_eq_sum, star_sum,
    Finset.sum_congr rfl fun i _ => hW.star_prodCharEta_starIrr hσ i j]
  exact Fintype.sum_bijective starIrr starIrr_involutive.bijective _ _ fun i => rfl

theorem prodCharEtaColSum_principal_im_eq_zero (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (x : G) :
    (hW.prodCharEtaColSum σ (principalIrr ↥W2) x).im = 0 := by
  have h2 := hW.finite_right
  have h := hW.star_prodCharEtaColSum hσ (principalIrr ↥W2)
  rw [starIrr_principalIrr] at h
  exact Complex.conj_eq_iff_im.1 (congrFun h x)

theorem prodCharEtaColSum_mem_span_Irr (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (j : Irr ↥W2) :
    hW.prodCharEtaColSum σ j ∈ Submodule.span ℤ (Irr G) := by
  have h1 := hW.finite_left
  have : Fintype (Irr ↥W1) := Fintype.ofFinite _
  rw [hW.prodCharEtaColSum_eq_sum]
  exact Submodule.sum_mem _ fun i _ =>
    virtualChars_le_span_Irr (hW.prodCharEta_mem_virtualChars hσ i j)

open scoped Classical in
theorem cfInner_prodCharEtaColSum_prodCharEta (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (j : Irr ↥W2) (i : Irr ↥W1) (l : Irr ↥W2) :
    cfInner (hW.prodCharEtaColSum σ j) (hW.prodCharEta σ i l) = if j = l then 1 else 0 := by
  have h1 := hW.finite_left
  have : Fintype (Irr ↥W1) := Fintype.ofFinite _
  rw [hW.prodCharEtaColSum_eq_sum, cfInner_sum_left,
    Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · rw [hW.cfInner_prodCharEta hσ]
    by_cases h : j = l <;> simp [h]
  · intro k _ hk
    rw [hW.cfInner_prodCharEta hσ]
    simp [hk]

omit [Fintype ↥W] in
theorem cfInner_prodCharEtaColSum_eq_zero (hW : IsCyclicTIPair W W1 W2)
    (j : Irr ↥W2) {f : G → ℂ}
    (hf : ∀ (i : Irr ↥W1) (l : Irr ↥W2), IsOrthogonal f (hW.prodCharEta σ i l)) :
    cfInner (hW.prodCharEtaColSum σ j) f = 0 := by
  have h1 := hW.finite_left
  have : Fintype (Irr ↥W1) := Fintype.ofFinite _
  rw [hW.prodCharEtaColSum_eq_sum, cfInner_sum_left]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← conj_cfInner, isOrthogonal_iff.1 (hf i j), map_zero]

theorem eq_prodCharEta_sub_of_isOrthonormal_of_odd (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (hodd : Odd (Nat.card G))
    {n : ℕ} (hn : 2 ≤ n) {e : Fin n → G → ℂ} (he : IsOrthonormalFamily e)
    (hemem : ∀ r, e r ∈ Submodule.span ℤ (Irr G))
    (heη : ∀ (r : Fin n) (k : Irr ↥W1) (l : Irr ↥W2), IsOrthogonal (e r) (hW.prodCharEta σ k l))
    (heV : ∀ r, ∀ x ∈ cyclicTIDiff W W1 W2, e r x = 0)
    {i : Irr ↥W1} {j : Irr ↥W2} (hj : j ≠ principalIrr ↥W2)
    {φ β : G → ℂ} {a : ℤ} (hφ : φ ∈ Submodule.span ℤ (Irr G))
    (hφnorm : cfInner φ φ = 2 + (n : ℂ) ^ 2)
    (hproj : ∑ r, cfInner φ (e r) • e r
      = (a : ℂ) • (∑ r, e r) - (n : ℂ) • e ⟨0, by omega⟩)
    (hψ : cfInner (hW.prodCharEtaColSum σ (principalIrr ↥W2) - e ⟨0, by omega⟩) φ = (n : ℂ) - 1)
    (hφV : ∀ v : ↥W, (v : G) ∈ cyclicTIDiff W W1 W2 →
      φ (v : G) = hW.prodChar (i : ↥W1 → ℂ) (j : ↥W2 → ℂ) v
        - hW.prodChar (i : ↥W1 → ℂ) ((principalIrr ↥W2 : Irr ↥W2) : ↥W2 → ℂ) v)
    (hβ : β = φ - hW.prodCharEta σ i j + hW.prodCharEta σ i (principalIrr ↥W2)
      + (n : ℂ) • e ⟨0, by omega⟩)
    (hβreal : ∀ x, (β x).im = 0) (hβ1 : cfInner β (1 : G → ℂ) = 0) :
    a = 0 ∧ φ = hW.prodCharEta σ i j - hW.prodCharEta σ i (principalIrr ↥W2)
      - (n : ℂ) • e ⟨0, by omega⟩ := by
  classical
  set r₁ : Fin n := ⟨0, by omega⟩ with hr₁
  set P0 : G → ℂ := hW.prodCharEtaColSum σ (principalIrr ↥W2) with hP0
  set T : G → ℂ := ∑ r, e r with hT
  set Y : G → ℂ := (a : ℂ) • T - (n : ℂ) • e r₁ with hY
  have hsmul_mem : ∀ (m : ℤ) {x : G → ℂ}, x ∈ Submodule.span ℤ (Irr G) →
      ((m : ℂ)) • x ∈ Submodule.span ℤ (Irr G) := by
    intro m x hx
    rw [Int.cast_smul_eq_zsmul ℂ]
    exact Submodule.smul_mem _ m hx
  have hnsmul_mem : ∀ {x : G → ℂ}, x ∈ Submodule.span ℤ (Irr G) →
      ((n : ℂ)) • x ∈ Submodule.span ℤ (Irr G) := by
    intro x hx
    have := hsmul_mem (n : ℤ) hx
    rwa [Int.cast_natCast] at this
  have hTmem : T ∈ Submodule.span ℤ (Irr G) := Submodule.sum_mem _ fun r _ => hemem r
  have hYmem : Y ∈ Submodule.span ℤ (Irr G) :=
    sub_mem (hsmul_mem a hTmem) (hnsmul_mem (hemem r₁))
  have hP0mem : P0 ∈ Submodule.span ℤ (Irr G) := hW.prodCharEtaColSum_mem_span_Irr hσ _
  have hηmem : ∀ (k : Irr ↥W1) (l : Irr ↥W2),
      hW.prodCharEta σ k l ∈ Submodule.span ℤ (Irr G) := fun k l =>
    virtualChars_le_span_Irr (hW.prodCharEta_mem_virtualChars hσ k l)
  have hβmem : β ∈ Submodule.span ℤ (Irr G) := by
    rw [hβ]
    exact add_mem (add_mem (sub_mem hφ (hηmem i j)) (hηmem i _)) (hnsmul_mem (hemem r₁))
  have hcoeff : ∀ s, cfInner φ (e s)
      = ((a - if s = r₁ then (n : ℤ) else 0 : ℤ) : ℂ) :=
    cfInner_eq_sub_ite_of_sum_smul_eq he hproj
  have hcoeff₁ : cfInner φ (e r₁) = ((a : ℂ) - (n : ℂ)) := by
    rw [hcoeff r₁]; simp
  have hP0φ : cfInner P0 φ = (a : ℂ) - 1 := by
    have h1 : cfInner (e r₁) φ = (a : ℂ) - (n : ℂ) := by
      rw [← conj_cfInner, hcoeff₁]
      simp
    rw [cfInner_sub_left, h1] at hψ
    linear_combination hψ
  have hP0e : ∀ r, cfInner P0 (e r) = 0 := fun r =>
    hW.cfInner_prodCharEtaColSum_eq_zero _ (heη r)
  have hP0β : cfInner P0 β = (a : ℂ) := by
    rw [hβ, cfInner_add_right, cfInner_add_right, cfInner_sub_right, hP0φ, cfInner_smul_right,
      hP0e r₁,
      hW.cfInner_prodCharEtaColSum_prodCharEta hσ (principalIrr ↥W2) i j,
      hW.cfInner_prodCharEtaColSum_prodCharEta hσ (principalIrr ↥W2) i (principalIrr ↥W2),
      if_neg (Ne.symm hj), if_pos rfl]
    ring
  have haeven : (2 : ℤ) ∣ a := by
    obtain ⟨p, hp⟩ := exists_int_cfInner_of_mem_span_Irr hP0mem
      (Submodule.subset_span (one_mem_Irr (G := G)))
    have hmod := intCast_cfInner_modEq_mul_of_odd hodd hP0mem hβmem
      (hW.prodCharEtaColSum_principal_im_eq_zero hσ) hβreal hP0β hp (b := 0) (by simpa using hβ1)
    simpa using hmod.dvd
  have hbessel := sum_mul_conj_cfInner_le he φ
  have hsumeq : (∑ r, cfInner φ (e r) * conj (cfInner φ (e r)))
      = ((∑ r : Fin n, (a - if r = r₁ then (n : ℤ) else 0) ^ 2 : ℤ) : ℂ) := by
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hcoeff r, map_intCast]
    push_cast
    ring
  have hRHS : (2 : ℂ) + (n : ℂ) ^ 2 = ((2 + (n : ℤ) ^ 2 : ℤ) : ℂ) := by push_cast; ring
  rw [hsumeq, hφnorm, sum_sq_sub_ite r₁ a (Fintype.card_fin n), hRHS] at hbessel
  have hbessel' : (n : ℤ) * (a * (a - 2)) + (n : ℤ) ^ 2 ≤ 2 + (n : ℤ) ^ 2 := by
    exact_mod_cast hbessel
  have hn' : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have ha02 : a = 0 ∨ a = 2 :=
    eq_zero_or_eq_two_of_even_of_mul_le hn' haeven (by linarith)
  have hmul0 : a * (a - 2) = 0 := by rcases ha02 with rfl | rfl <;> ring
  have hYeq : ∑ r, cfInner φ (e r) • e r = Y := hproj
  set X : G → ℂ := φ - Y with hX
  have hXnorm : cfInner X X = 2 := by
    have hpy := cfInner_self_eq_sum_add he φ
    rw [hsumeq, sum_sq_sub_ite r₁ a (Fintype.card_fin n), hmul0, hYeq, hφnorm] at hpy
    rw [hX]
    push_cast at hpy
    linear_combination -hpy
  have hXmem : X ∈ Submodule.span ℤ (Irr G) := sub_mem hφ hYmem
  have hYV : ∀ x ∈ cyclicTIDiff W W1 W2, Y x = 0 := by
    intro x hx
    have hTx : T x = 0 := by
      rw [hT]
      simpa using Finset.sum_eq_zero fun r (_ : r ∈ Finset.univ) => heV r x hx
    simp [hY, hTx, heV r₁ x hx]
  have hXV : ∀ v : ↥W, (v : G) ∈ cyclicTIDiff W W1 W2 →
      X (v : G) = (1 : ℂ) * (hW.prodChar (i : ↥W1 → ℂ) (j : ↥W2 → ℂ) v
        - hW.prodChar (i : ↥W1 → ℂ) ((principalIrr ↥W2 : Irr ↥W2) : ↥W2 → ℂ) v) := by
    intro v hv
    rw [hX, Pi.sub_apply, hYV _ hv, hφV v hv]
    ring
  have hXeq : X = hW.prodCharEta σ i j - hW.prodCharEta σ i (principalIrr ↥W2) := by
    have h := hW.eq_signed_sub_prodCharEta hσ
      (i := i) (j := j) (k := i) (l := principalIrr ↥W2)
      (by simpa using hj) (ε := 1) (Or.inl rfl) hXmem hXnorm hXV
    simpa using h
  have hβT : β = (a : ℂ) • T := by
    have hφXY : φ = X + Y := by rw [hX]; ring
    rw [hβ, hφXY, hXeq, hY]
    ring
  have ha0 : a = 0 := by
    have h : cfInner P0 ((a : ℂ) • T) = 0 := by
      rw [cfInner_smul_right, hT, cfInner_sum_right,
        Finset.sum_congr rfl fun r _ => hP0e r]
      simp
    rw [← hβT, hP0β] at h
    exact_mod_cast h
  refine ⟨ha0, ?_⟩
  have hφXY : φ = X + Y := by rw [hX]; ring
  rw [hφXY, hXeq, hY, ha0]
  simp
  ring

end IsCyclicTIPair

end CFSG.FeitThompson

end
