module

public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing
public import CFSG.FeitThompson.Representations.ClassFunctionCauchySchwarzProjection
import CFSG.FeitThompson.Representations.ArrayProjectionEnergySaturation
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
public import CFSG.FeitThompson.Representations.AdditiveArraySupportBound

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open ComplexConjugate Finset
open scoped ComplexOrder

variable {G : Type*} [Fintype G]

theorem cfInner_eq_classFunInner (f h : G → ℂ) :
    cfInner f h = CauchySchwarzProjection.classFunInner f h := by
  rw [cfInner_def, CauchySchwarzProjection.classFunInner_apply, Nat.card_eq_fintype_card]

theorem IsOrthonormalFamily.cfInner_eq_ite {ι : Type*} [DecidableEq ι] {η : ι → G → ℂ}
    (hη : IsOrthonormalFamily η) (i j : ι) :
    cfInner (η i) (η j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h; simp [hη.cfInner_self i]
  · simp [h, isOrthogonal_iff.1 (hη.isOrthogonal h)]

theorem sum_norm_sq_cfInner_le {ι : Type*} [Fintype ι] [DecidableEq ι] {η : ι → G → ℂ}
    (hη : IsOrthonormalFamily η) (f : G → ℂ) :
    ∑ k, ‖cfInner f (η k)‖ ^ 2 ≤ (cfInner f f).re := by
  have hη' : ∀ k l, CauchySchwarzProjection.classFunInner (η k) (η l) = if k = l then 1 else 0 :=
    fun k l => by rw [← cfInner_eq_classFunInner]; exact hη.cfInner_eq_ite k l
  have hpyth := CauchySchwarzProjection.classFunInner_self_eq_add_of_inner_eq hη' f
    (fun k => CauchySchwarzProjection.classFunInner f (η k)) (fun _ => rfl)
  have hsum : (∑ k, CauchySchwarzProjection.classFunInner f (η k) *
      conj (CauchySchwarzProjection.classFunInner f (η k))) =
      ((∑ k, ‖cfInner f (η k)‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.mul_conj', cfInner_eq_classFunInner]
  rw [hsum] at hpyth
  have hre := congrArg Complex.re hpyth
  simp only [Complex.add_re, Complex.ofReal_re] at hre
  rw [cfInner_eq_classFunInner, hre]
  have := CauchySchwarzProjection.classFunInner_self_re_nonneg
    (f - ∑ k, CauchySchwarzProjection.classFunInner f (η k) • η k)
  linarith

variable [Group G]

theorem cfInner_eq_zero_of_cfInner_self_re_lt_min {ι κ : Type*} [Finite ι] [Finite κ]
    [DecidableEq ι] [DecidableEq κ] {η : ι × κ → G → ℂ} {f : G → ℂ}
    (hηmem : ∀ p, η p ∈ Submodule.span ℤ (Irr G)) (hη : IsOrthonormalFamily η)
    (hf : f ∈ Submodule.span ℤ (Irr G))
    (hrect : ∀ i k : ι, ∀ j l : κ, cfInner f (η (i, j)) + cfInner f (η (k, l))
      = cfInner f (η (i, l)) + cfInner f (η (k, j)))
    (hnorm : (cfInner f f).re < min (Nat.card ι) (Nat.card κ)) :
    ∀ p, cfInner f (η p) = 0 := by
  classical
  have : Fintype ι := Fintype.ofFinite _
  have : Fintype κ := Fintype.ofFinite _
  choose a ha using fun p => exists_int_cfInner_of_mem_span_Irr hf (hηmem p)
  by_contra hcon
  push Not at hcon
  obtain ⟨p₀, hp₀⟩ := hcon
  set A : ι → κ → ℂ := fun i j => cfInner f (η (i, j)) with hA
  have hAne : ∃ i j, A i j ≠ 0 := ⟨p₀.1, p₀.2, hp₀⟩
  have hcard : min (Nat.card ι) (Nat.card κ) ≤ {p : ι × κ | A p.1 p.2 ≠ 0}.ncard :=
    min_le_ncard_support_of_add_swap A hrect hAne
  have hcard' : min (Nat.card ι) (Nat.card κ) ≤ #{p : ι × κ | A p.1 p.2 ≠ 0} := by
    rwa [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred] at hcard
  have hone : ∀ p ∈ ({p : ι × κ | A p.1 p.2 ≠ 0} : Finset _), (1 : ℝ) ≤ ‖cfInner f (η p)‖ ^ 2 := by
    intro p hp
    have hp' : cfInner f (η p) ≠ 0 := by simpa [hA] using hp
    have hane : a p ≠ 0 := by
      intro h
      rw [ha p, h] at hp'
      simp at hp'
    have h1 : (1 : ℝ) ≤ ‖cfInner f (η p)‖ := by
      rw [ha p, Complex.norm_intCast]
      exact_mod_cast Int.one_le_abs hane
    nlinarith [norm_nonneg (cfInner f (η p))]
  have h1 : ((#{p : ι × κ | A p.1 p.2 ≠ 0} : ℕ) : ℝ)
      ≤ ∑ p ∈ ({p : ι × κ | A p.1 p.2 ≠ 0} : Finset _), ‖cfInner f (η p)‖ ^ 2 := by
    calc ((#{p : ι × κ | A p.1 p.2 ≠ 0} : ℕ) : ℝ)
        = ∑ _p ∈ ({p : ι × κ | A p.1 p.2 ≠ 0} : Finset _), (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum hone
  have h2 : ∑ p ∈ ({p : ι × κ | A p.1 p.2 ≠ 0} : Finset _), ‖cfInner f (η p)‖ ^ 2
      ≤ ∑ p : ι × κ, ‖cfInner f (η p)‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
  have h3 : ∑ p : ι × κ, ‖cfInner f (η p)‖ ^ 2 ≤ (cfInner f f).re := sum_norm_sq_cfInner_le hη f
  have h4 : ((min (Nat.card ι) (Nat.card κ) : ℕ) : ℝ)
      ≤ ((#{p : ι × κ | A p.1 p.2 ≠ 0} : ℕ) : ℝ) := by exact_mod_cast hcard'
  have hlt : ((min (Nat.card ι) (Nat.card κ) : ℕ) : ℝ)
      < ((min (Nat.card ι) (Nat.card κ) : ℕ) : ℝ) := by
    calc ((min (Nat.card ι) (Nat.card κ) : ℕ) : ℝ) ≤ _ := h4
      _ ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ _ := h3
      _ < _ := hnorm
  simp at hlt

theorem isOrthogonal_of_cfInner_self_lt_min {m n : ℕ} {η : Fin m → Fin n → G → ℂ}
    {f : G → ℂ} (hηmem : ∀ i j, η i j ∈ Submodule.span ℤ (Irr G))
    (hη : IsOrthonormalFamily fun p : Fin m × Fin n => η p.1 p.2)
    (hf : f ∈ Submodule.span ℤ (Irr G))
    (hrect : ∀ i k : Fin m, ∀ j l : Fin n,
      cfInner f (η i j) + cfInner f (η k l) = cfInner f (η i l) + cfInner f (η k j))
    (hnorm : cfInner f f < ((min m n : ℕ) : ℂ)) :
    ∀ i j, IsOrthogonal f (η i j) := by
  have hre : (cfInner f f).re < min (Nat.card (Fin m)) (Nat.card (Fin n)) := by
    have := (Complex.lt_def.1 hnorm).1
    simpa using this
  have h := cfInner_eq_zero_of_cfInner_self_re_lt_min (η := fun p : Fin m × Fin n => η p.1 p.2)
    (f := f) (fun p => hηmem p.1 p.2) hη hf (fun i k j l => hrect i k j l) hre
  exact fun i j => isOrthogonal_iff.2 (h (i, j))

end CFSG.FeitThompson
