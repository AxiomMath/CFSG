module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSubflag

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (IsLinePerm)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (IsSpReducedWord exists_word_length_eq
  spLength_eq_invCount)

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

variable (ε) in
@[expose] def overgroupCuts (h : UnitaryFieldData p f K) (c : K) (hc : c ∈ h.traceZero)
    (A : Subgroup (hypSU h r ε)) : Set ℕ :=
  {i | ∃ k : Fin r, (k : ℕ) + 1 = i ∧ uWeylRep ε h k c hc ∉ A}

theorem overgroupCuts_subset (h : UnitaryFieldData p f K) {c : K} (hc : c ∈ h.traceZero)
    (A : Subgroup (hypSU h r ε)) : overgroupCuts ε h c hc A ⊆ Set.Icc 1 r := by
  rintro _ ⟨k, rfl, -⟩
  exact ⟨by omega, k.2⟩

theorem add_one_mem_overgroupCuts_iff (h : UnitaryFieldData p f K) {c : K}
    (hc : c ∈ h.traceZero) (A : Subgroup (hypSU h r ε)) (k : Fin r) :
    (k : ℕ) + 1 ∈ overgroupCuts ε h c hc A ↔ uWeylRep ε h k c hc ∉ A := by
  constructor
  · rintro ⟨k', hk', hnot⟩
    obtain rfl : k' = k := Fin.ext (by omega)
    exact hnot
  · exact fun hnot => ⟨k, rfl, hnot⟩

theorem eq_flagStabilizer_overgroupCuts (h : UnitaryFieldData p f K) (hr : 1 ≤ r)
    (hε : ε ≤ 1) {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) (A : Subgroup (hypSU h r ε))
    (hBA : hypBorel h r ε ≤ A) : A = flagStabilizer h r ε (overgroupCuts ε h c hc A) := by
  set I := overgroupCuts ε h c hc A with hIdef
  have hI : I ⊆ Set.Icc 1 r := overgroupCuts_subset h hc A
  have hallowed : ∀ k : Fin r, (k : ℕ) + 1 ∉ I ↔ uWeylRep ε h k c hc ∈ A := fun k => by
    rw [hIdef, add_one_mem_overgroupCuts_iff, not_not]
  obtain ⟨hgen, hmemiff, -⟩ := unitary_subflag_generation h hr hε hc hc0 hI
  have hB := hypBorel_le_flagStabilizer (h := h) (ε := ε) hI
  apply le_antisymm
  ·
    intro g hg
    obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := exists_mem_uBruhatCell h hε hc hc0 g
    have hdot : weylElt h hc hc0 w.2 ∈ A := by
      have := mul_mem (mul_mem (inv_mem (hBA hb₁)) hg) (inv_mem (hBA hb₂))
      rwa [show b₁⁻¹ * (b₁ * weylElt h hc hc0 w.2 * b₂) * b₂⁻¹ = weylElt h hc hc0 w.2 by
        group] at this
    have hwA : (hypBorel h r ε).map (MulAut.conj (weylElt h hc hc0 w.2)).toMonoidHom ≤ A := by
      rintro _ ⟨b, hb, rfl⟩
      exact mul_mem (mul_mem hdot (hBA hb)) (inv_mem hdot)
    obtain ⟨l, hlen, hprod⟩ := exists_word_length_eq _ (w : Equiv.Perm (Fin r ⊕ Fin r)) w.2 rfl
    have hred : IsSpReducedWord (w : Equiv.Perm (Fin r ⊕ Fin r)) l :=
      ⟨hprod, by rw [hlen, spLength_eq_invCount w.2]⟩
    have hall := unitary_reduced_word_extraction h hc hc0 A hBA l _ w.2 hwA hred
    have hmono : IsLinePerm (weylPerm (ε := ε) (w : Equiv.Perm (Fin r ⊕ Fin r)))
        (((uWordProd ε h c hc l : hypSU h r ε) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K) := by
      rw [← hprod]
      exact isLinePerm_uWordProd hc hc0 l
    obtain ⟨t, ht, hteq⟩ := exists_torus_of_isLinePerm hc hc0 w.2 hmono
    have hword : uWordProd ε h c hc l ∈ flagStabilizer h r ε I := by
      rw [hgen]
      exact Subgroup.mem_sup_right (uWordProd_mem_closure hc fun k hk =>
        (hallowed k).mpr (hall k hk))
    have hw' : weylElt h hc hc0 w.2 = uWordProd ε h c hc l * t⁻¹ := by
      rw [hteq, mul_inv_cancel_right]
    rw [hw']
    exact mul_mem (mul_mem (hB hb₁) (mul_mem hword (hB (inv_mem (hypTorus_le_hypBorel h ht)))))
      (hB hb₂)
  ·
    rw [hgen]
    refine sup_le hBA ((Subgroup.closure_le _).mpr ?_)
    rintro _ ⟨k, hk, rfl⟩
    exact (hallowed k).mp hk

theorem unitary_Borel_overgroups (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) (A : Subgroup (hypSU h r ε))
    (hBA : hypBorel h r ε ≤ A) :
    overgroupCuts ε h c hc A ⊆ Set.Icc 1 r ∧
    A = flagStabilizer h r ε (overgroupCuts ε h c hc A) ∧
    (∀ I ⊆ Set.Icc 1 r, A = flagStabilizer h r ε I → I = overgroupCuts ε h c hc A) ∧
    ∀ {c' : K} (hc' : c' ∈ h.traceZero), c' ≠ 0 →
      overgroupCuts ε h c' hc' A = overgroupCuts ε h c hc A := by
  have huniq : ∀ {c' : K} (hc' : c' ∈ h.traceZero), c' ≠ 0 → ∀ I ⊆ Set.Icc 1 r,
      A = flagStabilizer h r ε I → I = overgroupCuts ε h c' hc' A := by
    intro c' hc' hc0' I hI hAI
    obtain ⟨-, hmemiff, -⟩ := unitary_subflag_generation h hr hε hc' hc0' hI
    ext i
    constructor
    · intro hi
      obtain ⟨hi1, hir⟩ := hI hi
      refine ⟨⟨i - 1, by omega⟩, by change i - 1 + 1 = i; omega, fun hmem => ?_⟩
      rw [hAI] at hmem
      exact (hmemiff _).mp hmem (by
        rw [show ((⟨i - 1, by omega⟩ : Fin r) : ℕ) + 1 = i by
          change i - 1 + 1 = i
          omega]
        exact hi)
    · rintro ⟨k, rfl, hnot⟩
      by_contra hk
      rw [hAI] at hnot
      exact hnot ((hmemiff k).mpr hk)
  refine ⟨overgroupCuts_subset h hc A, eq_flagStabilizer_overgroupCuts h hr hε hc hc0 A hBA,
    huniq hc hc0, fun hc' hc0' => ?_⟩
  exact (huniq hc' hc0' _ (overgroupCuts_subset h hc A)
    (eq_flagStabilizer_overgroupCuts h hr hε hc hc0 A hBA)).symm

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
