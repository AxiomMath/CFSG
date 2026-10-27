module

public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing
import CFSG.FeitThompson.Representations.DadeAveragingOrthogonalProjection
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.DisjointAntirealBlocksOrthogonal
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
public import CFSG.FeitThompson.Representations.UnitInnerProductSignedPair

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace IntegralBlockProjection

open ComplexOrder

section Arith

variable {ι : Type*} (a : ι → ℤ) (R : Finset ι)

theorem sum_le_sum_sq : ∑ r ∈ R, a r ≤ ∑ r ∈ R, a r ^ 2 :=
  Finset.sum_le_sum fun r _ => Int.le_self_sq (a r)

theorem sum_sq_eq_sum_iff :
    ∑ r ∈ R, a r ^ 2 = ∑ r ∈ R, a r ↔ ∀ r ∈ R, a r = 0 ∨ a r = 1 := by
  rw [eq_comm, Finset.sum_eq_sum_iff_of_le fun r _ => Int.le_self_sq (a r)]
  refine forall₂_congr fun r _ => ?_
  constructor
  · intro h
    have h2 : a r * (a r - 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact Or.inl h3
    · exact Or.inr (by linarith)
  · rintro (h | h) <;> rw [h] <;> ring

end Arith

variable {G : Type*} [Group G] [Fintype G] {R : Finset (G → ℂ)} {f : G → ℂ}
  {a : (G → ℂ) → ℤ}

omit [Group G] in
theorem cfInner_of_isOrthonormalFamily {ι : Type*} [DecidableEq ι] {η : ι → G → ℂ}
    (hη : IsOrthonormalFamily η) (i j : ι) :
    cfInner (η i) (η j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h; simpa using hη.cfInner_self i
  · simpa [h] using isOrthogonal_iff.1 (hη.isOrthogonal h)

theorem exists_int_cfInner_forall_mem
    (hR : ↑R ⊆ (Submodule.span ℤ (Irr G) : Set (G → ℂ)))
    (hf : f ∈ Submodule.span ℤ (Irr G)) :
    ∃ a : (G → ℂ) → ℤ, ∀ r ∈ R, cfInner f r = (a r : ℂ) := by
  classical
  choose! a ha using fun (r : G → ℂ) (hr : r ∈ R) =>
    exists_int_cfInner_of_mem_span_Irr hf (hR hr)
  exact ⟨a, ha⟩

omit [Group G] in
theorem sum_cfInner_eq_intCast (ha : ∀ r ∈ R, cfInner f r = (a r : ℂ)) :
    ∑ r ∈ R, cfInner f r = ((∑ r ∈ R, a r : ℤ) : ℂ) := by
  push_cast
  exact Finset.sum_congr rfl ha

omit [Group G] in
theorem sum_cfInner_smul_eq (ha : ∀ r ∈ R, cfInner f r = (a r : ℂ)) :
    ∑ r ∈ R, cfInner f r • r = ∑ r ∈ R, (a r : ℂ) • r :=
  Finset.sum_congr rfl fun r hr => by rw [ha r hr]

omit [Group G] in
theorem cfInner_sum_cfInner_smul_left (hone : ∀ r ∈ R, cfInner r r = 1)
    (hzero : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → cfInner r s = 0) {s : G → ℂ} (hs : s ∈ R) :
    cfInner (∑ r ∈ R, cfInner f r • r) s = cfInner f s := by
  rw [cfInner_sum_left, Finset.sum_eq_single_of_mem s hs]
  · rw [cfInner_smul_left, hone s hs, mul_one]
  · intro r hr hne
    rw [cfInner_smul_left, hzero r hr s hs hne, mul_zero]

omit [Group G] in
theorem isOrthogonal_sub_sum_cfInner_smul (hone : ∀ r ∈ R, cfInner r r = 1)
    (hzero : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → cfInner r s = 0) {s : G → ℂ} (hs : s ∈ R) :
    IsOrthogonal (f - ∑ r ∈ R, cfInner f r • r) s := by
  rw [isOrthogonal_iff, cfInner_sub_left, cfInner_sum_cfInner_smul_left hone hzero hs, sub_self]

omit [Group G] in
theorem cfInner_sum_cfInner_smul_self (hone : ∀ r ∈ R, cfInner r r = 1)
    (hzero : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → cfInner r s = 0)
    (ha : ∀ r ∈ R, cfInner f r = (a r : ℂ)) :
    cfInner (∑ r ∈ R, cfInner f r • r) (∑ r ∈ R, cfInner f r • r)
      = ((∑ r ∈ R, a r ^ 2 : ℤ) : ℂ) := by
  rw [cfInner_sum_right]
  push_cast
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [cfInner_smul_right, cfInner_sum_cfInner_smul_left hone hzero hr, ha r hr]
  simp [sq]

omit [Group G] in
theorem cfInner_self_eq_add (hone : ∀ r ∈ R, cfInner r r = 1)
    (hzero : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → cfInner r s = 0) :
    cfInner f f = cfInner (∑ r ∈ R, cfInner f r • r) (∑ r ∈ R, cfInner f r • r)
      + cfInner (f - ∑ r ∈ R, cfInner f r • r) (f - ∑ r ∈ R, cfInner f r • r) := by
  set P := ∑ r ∈ R, cfInner f r • r with hP
  have h₁ : cfInner (f - P) P = 0 := by
    rw [hP, cfInner_sum_right]
    exact Finset.sum_eq_zero fun r hr => by
      rw [cfInner_smul_right,
        isOrthogonal_iff.1 (isOrthogonal_sub_sum_cfInner_smul hone hzero hr), mul_zero]
  have h₂ : cfInner P (f - P) = 0 := by rw [← conj_cfInner, h₁, map_zero]
  have hsum : P + (f - P) = f := add_sub_cancel _ _
  calc cfInner f f = cfInner (P + (f - P)) (P + (f - P)) := by rw [hsum]
    _ = _ := by rw [cfInner_add_left, cfInner_add_right, cfInner_add_right, h₁, h₂]; ring

omit [Group G] in
theorem intCast_sum_le_cfInner_sum_cfInner_smul_self (hone : ∀ r ∈ R, cfInner r r = 1)
    (hzero : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → cfInner r s = 0)
    (ha : ∀ r ∈ R, cfInner f r = (a r : ℂ)) :
    ((∑ r ∈ R, a r : ℤ) : ℂ)
      ≤ cfInner (∑ r ∈ R, cfInner f r • r) (∑ r ∈ R, cfInner f r • r) := by
  rw [cfInner_sum_cfInner_smul_self hone hzero ha]
  exact_mod_cast sum_le_sum_sq a R

omit [Group G] in
theorem cfInner_sum_cfInner_smul_self_eq_intCast_sum_iff (hone : ∀ r ∈ R, cfInner r r = 1)
    (hzero : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → cfInner r s = 0)
    (ha : ∀ r ∈ R, cfInner f r = (a r : ℂ)) :
    cfInner (∑ r ∈ R, cfInner f r • r) (∑ r ∈ R, cfInner f r • r)
        = ((∑ r ∈ R, a r : ℤ) : ℂ) ↔ ∀ r ∈ R, a r = 0 ∨ a r = 1 := by
  rw [cfInner_sum_cfInner_smul_self hone hzero ha, ← sum_sq_eq_sum_iff a R]
  exact_mod_cast Iff.rfl

omit [Group G] in
theorem exists_subset_sum_cfInner_smul_eq (ha : ∀ r ∈ R, cfInner f r = (a r : ℂ))
    (h01 : ∀ r ∈ R, a r = 0 ∨ a r = 1) :
    ∃ S ⊆ R, (S.card : ℤ) = ∑ r ∈ R, a r ∧ ∑ r ∈ R, cfInner f r • r = ∑ r ∈ S, r := by
  classical
  refine ⟨R.filter fun r => a r = 1, Finset.filter_subset _ _, ?_, ?_⟩
  · rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun r hr => ?_
    rcases h01 r hr with h | h <;> simp [h]
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun r hr => ?_
    rcases h01 r hr with h | h <;> simp [ha r hr, h]

theorem eq_sum_cfInner_smul_of_cfInner_self_eq (hone : ∀ r ∈ R, cfInner r r = 1)
    (hzero : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → cfInner r s = 0)
    (ha : ∀ r ∈ R, cfInner f r = (a r : ℂ))
    (hn : cfInner f f = ((∑ r ∈ R, a r : ℤ) : ℂ)) :
    (∀ r ∈ R, a r = 0 ∨ a r = 1) ∧ f = ∑ r ∈ R, cfInner f r • r := by
  set P := ∑ r ∈ R, cfInner f r • r with hP
  have hpy : cfInner f f = cfInner P P + cfInner (f - P) (f - P) :=
    cfInner_self_eq_add hone hzero
  have hle : ((∑ r ∈ R, a r : ℤ) : ℂ) ≤ cfInner P P :=
    intCast_sum_le_cfInner_sum_cfInner_smul_self hone hzero ha
  have hE : (0 : ℂ) ≤ cfInner (f - P) (f - P) := cfInner_self_nonneg _
  have h1 : cfInner P P + cfInner (f - P) (f - P) ≤ cfInner P P + 0 := by
    rw [add_zero, ← hpy, hn]; exact hle
  have hz : cfInner (f - P) (f - P) = 0 := le_antisymm ((add_le_add_iff_left _).1 h1) hE
  have hPP : cfInner P P = ((∑ r ∈ R, a r : ℤ) : ℂ) := by rw [hn.symm, hpy, hz, add_zero]
  refine ⟨(cfInner_sum_cfInner_smul_self_eq_intCast_sum_iff hone hzero ha).1 hPP, ?_⟩
  have : Nonempty G := ⟨1⟩
  have hfP := cfInner_self_eq_zero.1 hz
  rwa [sub_eq_zero] at hfP

theorem exists_int_coeff_and_bounds (hR : ↑R ⊆ (Submodule.span ℤ (Irr G) : Set (G → ℂ)))
    (hone : ∀ r ∈ R, cfInner r r = 1)
    (hzero : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → cfInner r s = 0)
    (hf : f ∈ Submodule.span ℤ (Irr G)) :
    ∃ a : (G → ℂ) → ℤ, (∀ r ∈ R, cfInner f r = (a r : ℂ)) ∧
      (∀ s ∈ R, IsOrthogonal (f - ∑ r ∈ R, cfInner f r • r) s) ∧
      cfInner (∑ r ∈ R, cfInner f r • r) (∑ r ∈ R, cfInner f r • r)
        = ((∑ r ∈ R, a r ^ 2 : ℤ) : ℂ) ∧
      (∑ r ∈ R, a r ≤ ∑ r ∈ R, a r ^ 2) ∧
      cfInner f f = cfInner (∑ r ∈ R, cfInner f r • r) (∑ r ∈ R, cfInner f r • r)
        + cfInner (f - ∑ r ∈ R, cfInner f r • r) (f - ∑ r ∈ R, cfInner f r • r) ∧
      (cfInner (∑ r ∈ R, cfInner f r • r) (∑ r ∈ R, cfInner f r • r)
          = ((∑ r ∈ R, a r : ℤ) : ℂ) ↔ ∀ r ∈ R, a r = 0 ∨ a r = 1) := by
  obtain ⟨a, ha⟩ := exists_int_cfInner_forall_mem hR hf
  exact ⟨a, ha, fun s hs => isOrthogonal_sub_sum_cfInner_smul hone hzero hs,
    cfInner_sum_cfInner_smul_self hone hzero ha, sum_le_sum_sq a R,
    cfInner_self_eq_add hone hzero,
    cfInner_sum_cfInner_smul_self_eq_intCast_sum_iff hone hzero ha⟩

end IntegralBlockProjection

end CFSG.FeitThompson
