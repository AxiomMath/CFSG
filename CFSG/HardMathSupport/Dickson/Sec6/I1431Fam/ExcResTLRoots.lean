module

public import CFSG.HardMathSupport.Foote.Proving.RootStringOne
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallF4Const
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Foote.Proving
open scoped commutatorElement

set_option linter.unusedSectionVars false


theorem excTL_noG2 {τ : Tag} (hτ : τ ≠ .G2) : NoG2 τ := by
  cases τ
  · exact absurd rfl hτ
  · exact noG2_F4
  all_goals exact fun i => Or.inl (by simp [Tag.symmetrizer])

theorem excTL_a2_ne {τ : Tag} (hτ : τ ≠ .G2) {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hsum : IsRoot τ (γ + δ)) : γ ≠ δ ∧ γ ≠ -δ := by
  refine ⟨fun h => ?_, fun h => hsum.ne_zero (by rw [h, neg_add_cancel])⟩
  subst h
  have h1 := iform_self_cases (excTL_noG2 hτ) hγ
  have h2 := iform_self_cases (excTL_noG2 hτ) hsum
  have h3 := iform_nsmul_add_nsmul 1 1 γ γ
  simp only [one_smul, Nat.cast_one] at h3
  omega

theorem excTL_a2_not_isRoot {τ : Tag} (hτ : τ ≠ .G2) {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hδ : IsRoot τ δ) (hsum : IsRoot τ (γ + δ)) (h2 : ¬ IsRoot τ ((2 : ℤ) • γ + δ))
    (h3 : ¬ IsRoot τ (γ + (2 : ℤ) • δ)) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hij : (i, j) ≠ (1, 1)) : ¬ IsRoot τ (i • γ + j • δ) := by
  obtain ⟨hne, hne'⟩ := excTL_a2_ne hτ hγ hsum
  by_cases hc : (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)
  · rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa [two_smul] using h3
    · simpa [two_smul] using h2
  · refine not_isRoot_nsmul_add_nsmul (excTL_noG2 hτ) hγ hδ hne hne' hi hj ?_
    rintro (⟨rfl, rfl⟩ | h | h)
    · exact hij rfl
    · exact hc (Or.inl h)
    · exact hc (Or.inr h)

theorem excTL_a2_commutator {τ : Tag} (hτ : τ ≠ .G2) {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hδ : IsRoot τ δ) (hsum : IsRoot τ (γ + δ)) (h1 : ¬ IsRoot τ (γ - δ))
    (h2 : ¬ IsRoot τ ((2 : ℤ) • γ + δ)) (h3 : ¬ IsRoot τ (γ + (2 : ℤ) • δ)) :
    ∃ e : ℤ, (e = 1 ∨ e = -1) ∧ ∀ (R : Type) [CommRing R] (c d : R),
      pinnedX τ R γ c * pinnedX τ R δ d * pinnedX τ R γ (-c) * pinnedX τ R δ (-d) =
        pinnedX τ R (γ + δ) ((e : R) * c * d) := by
  obtain ⟨hne, hne'⟩ := excTL_a2_ne hτ hγ hsum
  have hno : ∀ p ∈ commCandidates, p ≠ (1, 1) → ¬ IsRoot τ (p.1 • γ + p.2 • δ) := by
    intro p hp hp1
    obtain ⟨⟨h1', -⟩, h2', -⟩ := mem_commCandidates.1 hp
    exact excTL_a2_not_isRoot hτ hγ hδ hsum h2 h3 h1' h2' hp1
  cases τ
  · exact absurd rfl hτ
  ·
    obtain ⟨C, hC, hF⟩ := exists_pinnedX_commFormula_F4_exact hγ hδ hne hne'
    have hlist := commPairs_eq_single_of_string_one hsum hno
    have h11 : ((1, 1) : ℕ × ℕ) ∈ commPairs .F4 γ δ := by rw [hlist]; simp
    have hC11 := hC (1, 1) h11
    have hnr : ¬ IsRoot .F4 (δ - γ) := fun h => h1 (by simpa using IsRoot.neg h)
    simp only [hnr, and_false, ite_false] at hC11
    refine ⟨C (1, 1), ?_, fun R _ c d => ?_⟩
    · rcases abs_eq (by norm_num : (0 : ℤ) ≤ 1) |>.1 hC11 with h | h <;> simp [h]
    · have := hF R c d
      rw [hlist] at this
      simpa using this
  all_goals
    obtain ⟨C, ⟨hC1, hC2⟩, hF⟩ := commutator_pinnedX_string_one hγ hδ hne hne' hsum hno
    have hC2' : |C| ≤ 1 := by simpa [RootOps.commConstBound] using hC2
    refine ⟨C, ?_, hF⟩
    rcases abs_eq (zero_le_one' ℤ) |>.1 (le_antisymm hC2' hC1) with h | h
    exacts [Or.inl h, Or.inr h]

theorem excTL_a2_commute {τ : Tag} (hτ : τ ≠ .G2) {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hδ : IsRoot τ δ) (hsum : IsRoot τ (γ + δ)) (h2 : ¬ IsRoot τ ((2 : ℤ) • γ + δ))
    (h3 : ¬ IsRoot τ (γ + (2 : ℤ) • δ)) (K : Type) [Field K] (s t u : K) :
    Commute (pinnedX τ K γ s) (pinnedX τ K (γ + δ) u) ∧
      Commute (pinnedX τ K δ t) (pinnedX τ K (γ + δ) u) := by
  obtain ⟨hne, hne'⟩ := excTL_a2_ne hτ hγ hsum
  have hindep := linIndepPair_of_ne hγ hδ hne hne'
  refine ⟨?_, ?_⟩
  · refine commute_of_forall_not_isRoot hγ hsum ?_ ?_ ?_ K _ (mem_rootSubgroup.2 ⟨s, rfl⟩) _
      (mem_rootSubgroup.2 ⟨u, rfl⟩)
    · intro h
      exact hδ.ne_zero (by simpa using h)
    · intro h
      have h' := eq_neg_iff_add_eq_zero.1 h
      have := (hindep 2 1 (by rw [two_smul, one_smul, add_assoc, h'])).1
      omega
    · intro a b ha hb
      have e : a • γ + b • (γ + δ) = (a + b) • γ + b • δ := by
        rw [smul_add, ← add_assoc, ← add_nsmul]
      rw [e]
      exact excTL_a2_not_isRoot hτ hγ hδ hsum h2 h3 (by omega) hb (by simp; omega)
  · refine commute_of_forall_not_isRoot hδ hsum ?_ ?_ ?_ K _ (mem_rootSubgroup.2 ⟨t, rfl⟩) _
      (mem_rootSubgroup.2 ⟨u, rfl⟩)
    · intro h
      exact hγ.ne_zero (by simpa using h)
    · intro h
      have h' := eq_neg_iff_add_eq_zero.1 h
      have := (hindep 1 2 (by rw [one_smul, two_smul, ← h']; abel)).2
      omega
    · intro a b ha hb
      have e : a • δ + b • (γ + δ) = b • γ + (a + b) • δ := by
        rw [smul_add, add_nsmul]; abel
      rw [e]
      exact excTL_a2_not_isRoot hτ hγ hδ hsum h2 h3 hb (by omega) (by simp; omega)

end CFSG.HardMathSupport.Dickson.Sec6.I1431
