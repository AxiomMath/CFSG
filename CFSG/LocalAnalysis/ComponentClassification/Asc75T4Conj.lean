module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Dichotomy

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix

variable {G : Type} [Group G] [Finite G]

theorem twoPrimeLayerIn_rightConjugate (Q : Subgroup G) (g : G) :
    twoPrimeLayerIn (rightConjugate Q g) = rightConjugate (twoPrimeLayerIn Q) g :=
  twoPrimeLayerIn_map _ (MulAut.conj g⁻¹).injective Q

theorem oddCoreIn_rightConjugate (Q : Subgroup G) (g : G) :
    oddCoreIn (rightConjugate Q g) = rightConjugate (oddCoreIn Q) g :=
  oddCoreIn_map _ (MulAut.conj g⁻¹).injective Q

omit [Finite G] in
theorem HasFourGroup.map {G' : Type*} [Group G'] {X : Subgroup G} (h : HasFourGroup X)
    {f : G →* G'} (hf : Function.Injective f) : HasFourGroup (X.map f) := by
  obtain ⟨E, hEX, hE, hE4⟩ := h
  refine ⟨E.map f, map_mono hEX, ?_, by rw [card_map_of_injective hf, hE4]⟩
  rintro _ ⟨e, he, rfl⟩
  rw [← map_pow, hE e he, map_one]

omit [Finite G] in
theorem hasFourGroup_rightConjugate_iff {X : Subgroup G} {g : G} :
    HasFourGroup (rightConjugate X g) ↔ HasFourGroup X := by
  refine ⟨fun h => ?_, fun h => h.map (MulAut.conj g⁻¹).injective⟩
  have h' := h.map (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rwa [rightConjugate, map_map, show (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom
    = MonoidHom.id G by ext; simp; group, map_id] at h'

theorem caseIPair_rightConjugate_iff {A B : Subgroup G} {g : G} :
    CaseIPair (rightConjugate B g) (rightConjugate A g) ↔ CaseIPair B A := by
  unfold CaseIPair
  rw [← AschbacherTheorem3.rightConjugate_normalizer, ← AschbacherTheorem3.rightConjugate_inf,
    hasFourGroup_rightConjugate_iff, twoPrimeLayerIn_rightConjugate,
    ← AschbacherTheorem3.rightConjugate_normalizer]
  exact imp_congr_right fun _ =>
    map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective

omit [Finite G] in
theorem eq_of_even_inf_rightConjugate {Q : Subgroup G} (htight : TightlyEmbedded Q) {a b : G}
    (h : Even (Nat.card (rightConjugate Q a ⊓ rightConjugate Q b : Subgroup G))) :
    rightConjugate Q a = rightConjugate Q b := by
  have heq : rightConjugate Q a ⊓ rightConjugate Q b =
      rightConjugate (Q ⊓ rightConjugate Q (b * a⁻¹)) a := by
    rw [AschbacherTheorem3.rightConjugate_inf, rightConjugate_mul, inv_mul_cancel_right]
  rw [heq, rightConjugate_card] at h
  have hn := mem_normalizer_of_even_inf htight h
  rw [← rightConjugate_eq_self_iff] at hn
  calc rightConjugate Q a = rightConjugate (rightConjugate Q (b * a⁻¹)) a := by rw [hn]
    _ = rightConjugate Q b := by rw [rightConjugate_mul, inv_mul_cancel_right]

@[expose] def NoThm3Alt3 (Q : Subgroup G) : Prop :=
  ∀ g : G, g ∉ normalizer (Q : Set G) → ∀ T : Subgroup G,
    IsSylowOf 2 T (rightConjugate Q g ⊓ normalizer (Q : Set G)) → ¬ Thm3Alt3 (bar Q Q) (bar Q T)

theorem caseIPair_self_rightConjugate (h3 : AschbacherTheorem3.Theorem3Statement)
    {Q : Subgroup G} (htight : TightlyEmbedded Q) (hno : NoThm3Alt3 Q) (g : G) :
    CaseIPair Q (rightConjugate Q g) := by
  intro h4
  by_cases hg : g ∈ normalizer (Q : Set G)
  · rw [(rightConjugate_eq_self_iff Q g).mpr hg]
    exact (twoPrimeLayerIn_le Q).trans le_normalizer
  obtain ⟨E, hEO, hE, hE4⟩ := h4
  obtain ⟨T, hT, hET⟩ := AschbacherTheorem3.exists_isSylowOf_le (isPGroup_of_sq_eq_one hE) hEO
  rcases le_normalizer_or_thm3Alt3 h3 htight hg hT hET hE hE4 with h | h
  · exact h
  · exact absurd h (hno g hg T hT)

theorem caseIPair_rightConjugate (h3 : AschbacherTheorem3.Theorem3Statement) {Q : Subgroup G}
    (htight : TightlyEmbedded Q) (hno : NoThm3Alt3 Q) (a b : G) :
    CaseIPair (rightConjugate Q b) (rightConjugate Q a) := by
  have h := caseIPair_self_rightConjugate h3 htight hno (a * b⁻¹)
  rw [← caseIPair_rightConjugate_iff (g := b), rightConjugate_mul, inv_mul_cancel_right] at h
  exact h

theorem twoPrimeLayerIn_le_normalizer_of_le {Q : Subgroup G}
    (h4 : HasFourGroup (twoPrimeLayerIn Q)) {a b : G}
    (hI : CaseIPair (rightConjugate Q b) (rightConjugate Q a))
    (h : twoPrimeLayerIn (rightConjugate Q a) ≤ normalizer (rightConjugate Q b : Set G)) :
    twoPrimeLayerIn (rightConjugate Q b) ≤ normalizer (rightConjugate Q a : Set G) := by
  refine hI ((h4.map (f := (MulAut.conj a⁻¹).toMonoidHom) (MulAut.conj a⁻¹).injective).mono
    (le_inf ?_ ?_))
  · change rightConjugate (twoPrimeLayerIn Q) a ≤ _
    rw [← twoPrimeLayerIn_rightConjugate]
    exact twoPrimeLayerIn_le _
  · change rightConjugate (twoPrimeLayerIn Q) a ≤ _
    rw [← twoPrimeLayerIn_rightConjugate]
    exact h

end CFSG.ComponentClassification.Asc75T4
