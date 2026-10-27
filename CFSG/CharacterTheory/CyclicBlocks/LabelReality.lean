module

public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeInversionFamily

public section

open scoped BigOperators Classical

namespace CFSG.CyclicBlocks

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal

theorem label_character_isConj {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (θ : basis.index) {g h : G} (hgh : IsConj g h) :
    (basis.representation θ).character g = (basis.representation θ).character h := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hgh
  rw [← hc]
  simp only [FiniteComplexRepresentation.character, Representation.char_conj]

theorem real_of_one_add_sub_real {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) {a b : basis.index} (hab : b ≠ a) {δ : ℤ}
    (hδ : δ = 1 ∨ δ = -1)
    (hreal : ∀ g, starRingEnd ℂ (1 + δ * (basis.representation a).character g -
        δ * (basis.representation b).character g) =
      1 + δ * (basis.representation a).character g - δ * (basis.representation b).character g) :
    (∀ g, starRingEnd ℂ ((basis.representation a).character g) =
      (basis.representation a).character g) ∧
    ∀ g, starRingEnd ℂ ((basis.representation b).character g) =
      (basis.representation b).character g := by
  obtain ⟨a', ha'⟩ := exists_conj_label basis a
  obtain ⟨b', hb'⟩ := exists_conj_label basis b
  have hfun : (fun g => 1 + (δ : ℂ) * (basis.representation a').character g -
      δ * (basis.representation b').character g) =
      fun g => 1 + (δ : ℂ) * (basis.representation a).character g -
        δ * (basis.representation b).character g := by
    funext g
    rw [ha', hb', ← hreal g]
    simp only [map_sub, map_add, map_mul, map_one, map_intCast]
  have hpair := fun (θ : basis.index) => congrArg
    (fun F => characterPairing F (basis.representation θ).character) hfun
  have hδ0 : (δ : ℂ) ≠ 0 := by rcases hδ with rfl | rfl <;> norm_num
  have haa : a' = a := by
    have h := hpair a
    simp only [characterPairing_one_add_sub_left, characterPairing_label_label] at h
    simp only [hab, ↓reduceIte] at h
    by_contra hne
    simp only [hne, ↓reduceIte] at h
    by_cases hb'a : b' = a
    · simp only [hb'a, ↓reduceIte] at h
      apply hδ0
      linear_combination (-1 / 2 : ℂ) * h
    · simp only [hb'a, ↓reduceIte] at h
      apply hδ0
      linear_combination (-1 : ℂ) * h
  have hbb : b' = b := by
    have h := hpair b
    simp only [characterPairing_one_add_sub_left, characterPairing_label_label, haa] at h
    have hab' : a ≠ b := fun h' => hab h'.symm
    simp only [hab', ↓reduceIte] at h
    by_contra hne
    simp only [hne, ↓reduceIte] at h
    apply hδ0
    linear_combination h
  refine ⟨fun g => ?_, fun g => ?_⟩
  · rw [← ha' g, haa]
  · rw [← hb' g, hbb]

end CFSG.CyclicBlocks
