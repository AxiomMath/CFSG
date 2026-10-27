module

public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldCovering
public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldQuaternionFull

public noncomputable section

namespace CFSG.Wreathed.SmallerRecognitionOriginalField

open CFSG.Assembly.LowTwoRank FullSylowCoveringObstruction
open OriginalCoveringSylowNormalizer OriginalSylowNormalizerWitness
open scoped Classical Pointwise

variable {G : Type} [Group G] [Finite G]

theorem original_prime_normalizer_component_image_top
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {ell : ℕ} (hell : ell.Prime) (P : Sylow ell (centralizerOddCore n S e)) :
    ComponentCoveringLocal.originalImage n S e
      (Subgroup.normalizer (ambientSylow (involutionCentralizer n S e) P : Set G)) = ⊤ :=
  original_normalizer_quotient_image hell (involutionCentralizer n S e) P

theorem original_prime_normalizer_component_cover
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {ell : ℕ} (hell : ell.Prime) (P : Sylow ell (centralizerOddCore n S e)) :
    CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e
        (Subgroup.normalizer (ambientSylow (involutionCentralizer n S e) P : Set G)) := by
  rw [original_prime_normalizer_component_image_top n S e hell P]
  exact le_top

variable [IsSimpleGroup G]

theorem original_prime_normalizer_full_original_field_alternatives
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G)
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    (P : Sylow ell (centralizerOddCore n S e))
    (hSP : (S : Subgroup G) ≤ Subgroup.normalizer
      (ambientSylow (involutionCentralizer n S e) P : Set G)) :
    let N := involutionCentralizer n S e
    let A := ambientSylow N P
    let K := Subgroup.normalizer (A : Set G)
    let O := ambientOddCore K
    5 ≤ p ^ f ∧ K < ⊤ ∧ A ≠ ⊥ ∧ Odd (Nat.card A) ∧ A ≤ O ∧ O ≠ ⊥ ∧
      CFSG.oddCore K ≠ ⊥ ∧
      (K.comap N.subtype).map (centralizerOddCoreMap n S e) = ⊤ ∧
      ComponentCoveringLocal.originalImage n S e K = ⊤ ∧
      (N : Set G) = (ambientOddCore N : Set G) * (K ⊓ N : Set G) ∧
      O ⊓ N ≤ ambientOddCore N ∧
      (∃ B : Sylow ell ↥(O ⊓ N), (B : Subgroup _).map (O ⊓ N).subtype = A) ∧
      (∃ Q : Sylow ell O, A ≤ (Q : Subgroup O).map O.subtype ∧
        (S : Subgroup G) ≤ Subgroup.normalizer
          (((Q : Subgroup O).map O.subtype) : Set G)) ∧
      (∀ Q : Sylow ell O, A ≤ (Q : Subgroup O).map O.subtype ∧
        ((Q : Subgroup O).map O.subtype) ⊓ N = A) ∧
      FullSylowCoveringConclusion n S e K hSP ∧
      ComponentCoveringLocal.ComponentCoveringLocalConclusion n hn S e K hSP ∧
      (CoveringFactorizationBranch n S e K hSP ∨
        CoveringTypeIObstruction n S e K ∧
          OriginalComponentCoreConclusion n hn S e p f K hSP) := by
  let N := involutionCentralizer n S e
  let A := ambientSylow N P
  let K := Subgroup.normalizer (A : Set G)
  obtain ⟨hK, _, hAO, hquotient, hON, hO, hB, hQ, hCQ⟩ :=
    original_covering_normalizer_structure n hn S e hell hdiv P hSP
  have hcover := original_prime_normalizer_component_cover n S e hell P
  have hproduct := original_sylow_normalizer_set_product hell N P
  have hcore : CFSG.oddCore K ≠ ⊥ := by
    intro h
    apply hO
    change (CFSG.oddCore K).map K.subtype = ⊥
    rw [h, Subgroup.map_bot]
  obtain ⟨hcomponent, halt⟩ := full_sylow_component_cover_original_field_alternatives
    hnonab n hn S e hfour p f hp hpodd hf hlocal hrec K hSP hK hcover
  exact ⟨statedPSL_two_odd_parameter_at_least_five p f hp hpodd hf hlocal,
    hK, original_Sylow_nontrivial hell N hdiv P, original_Sylow_odd N P,
    hAO, hO, hcore, hquotient, original_prime_normalizer_component_image_top n S e hell P,
    hproduct, hON, hB, hQ, hCQ,
    full_Sylow_covering_subgroup_has_factorization_or_exact_typeI_obstruction
      hnonab n hn S e K hSP hproduct, hcomponent, halt⟩

theorem original_each_prime_has_full_original_field_normalizer_alternatives
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G)
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e)) :
    (∃ P : Sylow ell (centralizerOddCore n S e),
      (S : Subgroup G) ≤ Subgroup.normalizer
        (ambientSylow (involutionCentralizer n S e) P : Set G)) ∧
    ∀ P : Sylow ell (centralizerOddCore n S e),
      ∀ hSP : (S : Subgroup G) ≤ Subgroup.normalizer
        (ambientSylow (involutionCentralizer n S e) P : Set G),
      let N := involutionCentralizer n S e
      let A := ambientSylow N P
      let K := Subgroup.normalizer (A : Set G)
      let O := ambientOddCore K
      5 ≤ p ^ f ∧ K < ⊤ ∧ A ≠ ⊥ ∧ Odd (Nat.card A) ∧ A ≤ O ∧ O ≠ ⊥ ∧
        CFSG.oddCore K ≠ ⊥ ∧
        (K.comap N.subtype).map (centralizerOddCoreMap n S e) = ⊤ ∧
        ComponentCoveringLocal.originalImage n S e K = ⊤ ∧
        (N : Set G) = (ambientOddCore N : Set G) * (K ⊓ N : Set G) ∧
        O ⊓ N ≤ ambientOddCore N ∧
        (∃ B : Sylow ell ↥(O ⊓ N), (B : Subgroup _).map (O ⊓ N).subtype = A) ∧
        (∃ Q : Sylow ell O, A ≤ (Q : Subgroup O).map O.subtype ∧
          (S : Subgroup G) ≤ Subgroup.normalizer
            (((Q : Subgroup O).map O.subtype) : Set G)) ∧
        (∀ Q : Sylow ell O, A ≤ (Q : Subgroup O).map O.subtype ∧
          ((Q : Subgroup O).map O.subtype) ⊓ N = A) ∧
        FullSylowCoveringConclusion n S e K hSP ∧
        ComponentCoveringLocal.ComponentCoveringLocalConclusion n hn S e K hSP ∧
        (CoveringFactorizationBranch n S e K hSP ∨
          CoveringTypeIObstruction n S e K ∧
            OriginalComponentCoreConclusion n hn S e p f K hSP) := by
  refine ⟨original_invariant_prime_Sylow_exists n hn S e hell, ?_⟩
  intro P hSP
  exact original_prime_normalizer_full_original_field_alternatives hnonab n hn S e hfour
    p f hp hpodd hf hlocal hrec hell hdiv P hSP

theorem original_prime_nonfactorizing_normalizer_has_original_field_simple_core
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G)
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    (P : Sylow ell (centralizerOddCore n S e))
    (hSP : (S : Subgroup G) ≤ Subgroup.normalizer
      (ambientSylow (involutionCentralizer n S e) P : Set G))
    (hnonfactor :
      let N := involutionCentralizer n S e
      let K := Subgroup.normalizer (ambientSylow N P : Set G)
      (K : Set G) ≠ ((CFSG.oddCore K).map K.subtype : Set G) * (K ⊓ N : Set G)) :
    let N := involutionCentralizer n S e
    let K := Subgroup.normalizer (ambientSylow N P : Set G)
    K < ⊤ ∧ CFSG.oddCore K ≠ ⊥ ∧
      FullSylowCoveringConclusion n S e K hSP ∧
      ComponentCoveringLocal.ComponentCoveringLocalConclusion n hn S e K hSP ∧
      CoveringTypeIObstruction n S e K ∧
      OriginalComponentCoreConclusion n hn S e p f K hSP := by
  obtain ⟨_, hK, _, _, _, _, hO, _, _, _, _, _, _, _, hfull, hcomponent, halt⟩ :=
    original_prime_normalizer_full_original_field_alternatives hnonab n hn S e hfour
      p f hp hpodd hf hlocal hrec hell hdiv P hSP
  refine ⟨hK, hO, hfull, hcomponent, ?_⟩
  rcases halt with hfactor | htype
  · exact False.elim (hnonfactor hfactor.factorization)
  · exact htype

end CFSG.Wreathed.SmallerRecognitionOriginalField
