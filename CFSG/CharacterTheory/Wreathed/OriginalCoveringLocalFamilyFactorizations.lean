module
public import CFSG.CharacterTheory.Wreathed.OriginalCoveringLocalFamilySameField
public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldQuaternionPrimeNormalizer

public noncomputable section
open scoped Classical Pointwise
namespace CFSG.Wreathed.OriginalCoveringLocalFamily
open CFSG.Assembly.LowTwoRank FullSylowCoveringObstruction SmallerRecognitionOriginalField
open OriginalCoveringSylowNormalizer OriginalSylowNormalizerWitness
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem original_component_core_forces_trivial_odd_core
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcore : OriginalComponentCoreConclusion n hn S e p f K hSK) : CFSG.oddCore K = ⊥ := by
  let L := SimpleOddIndexQuotient.involutionClosure (K ⧸ CFSG.oddCore K)
  rcases hcore with ⟨hLN, hLne, hmin, huniq, hsimple, hnonabL, hindex,
    hSL, hcent, hcoord, hmodel, hident⟩
  let : L.Normal := hLN
  let : IsSimpleGroup L := hsimple
  exact same_field_simple_odd_index_quotient_trivial_odd_kernel
    hnonab n hn S e hfour p f hp hpodd hf hq hlocal K hSK (CFSG.oddCore K)
    (CFSG.ComponentClassification.OddCore.odd_card K) L hindex hnonabL hmodel

theorem smaller_recognition_forces_original_full_sylow_covering_factorizations
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G)
    (K : Subgroup G) (hproper : K < ⊤) (hSK : (S : Subgroup G) ≤ K)
    (hcover : (involutionCentralizer n S e : Set G) =
      (ambientOddCore (involutionCentralizer n S e) : Set G) *
        (K ⊓ involutionCentralizer n S e : Set G))
    (hO : CFSG.oddCore K ≠ ⊥) :
    FullSylowCoveringConclusion n S e K hSK ∧
      ComponentCoveringLocal.ComponentCoveringLocalConclusion n hn S e K hSK ∧
      CoveringFactorizationBranch n S e K hSK := by
  have hwhole : ComponentCoveringLocal.originalImage n S e K = ⊤ := by
    apply eq_top_iff.mpr
    intro z hz
    let N := involutionCentralizer n S e
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore N) z
    have haN : (a : G) ∈ (ambientOddCore N : Set G) * (K ⊓ N : Set G) := hcover ▸ a.property
    obtain ⟨r, hr, c, hc, hrc⟩ := Set.mem_mul.mp haN
    obtain ⟨rN, hrN, hrval⟩ := hr
    change (rN : G) = r at hrval
    have hqR : QuotientGroup.mk' (CFSG.oddCore N) rN = 1 :=
      QuotientGroup.eq_one_iff _ |>.mpr hrN
    let cN : N := ⟨c, hc.2⟩
    have heq : rN * cN = a := Subtype.ext (by
      change (rN : G) * c = (a : G)
      rw [hrval]
      exact hrc)
    refine ⟨cN, hc.1, ?_⟩
    change QuotientGroup.mk' (CFSG.oddCore N) cN = QuotientGroup.mk' (CFSG.oddCore N) a
    rw [← heq, map_mul, hqR, one_mul]
  have hcoverL : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e K := hwhole ▸ le_top
  obtain ⟨hcomponent, halt⟩ := full_sylow_component_cover_original_field_alternatives
    hnonab n hn S e hfour p f hp hpodd hf hlocal hrec K hSK hproper hcoverL
  refine ⟨full_Sylow_covering_subgroup_has_factorization_or_exact_typeI_obstruction
    hnonab n hn S e K hSK hcover, hcomponent, ?_⟩
  rcases halt with hfactor | htype
  · exact hfactor
  · exact False.elim (hO (original_component_core_forces_trivial_odd_core
      hnonab n hn S e hfour p f hp hpodd hf hq hlocal K hSK htype.2))


theorem original_prime_normalizer_full_factorizations
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
      CoveringFactorizationBranch n S e K hSP := by
  obtain ⟨hq, hK, hA, hAodd, hAO, hO, hcore, hquotient, hwhole, hproduct,
    hON, hB, hQ, hCQ, hfull, hcomponent, halt⟩ :=
      original_prime_normalizer_full_original_field_alternatives
        hnonab n hn S e hfour p f hp hpodd hf hlocal hrec hell hdiv P hSP
  have hfactor : CoveringFactorizationBranch n S e
      (Subgroup.normalizer (ambientSylow (involutionCentralizer n S e) P : Set G)) hSP := by
    rcases halt with hfactor | htype
    · exact hfactor
    · exact False.elim (hcore (original_component_core_forces_trivial_odd_core
        hnonab n hn S e hfour p f hp hpodd hf hq hlocal _ hSP htype.2))
  exact ⟨hq, hK, hA, hAodd, hAO, hO, hcore, hquotient, hwhole, hproduct,
    hON, hB, hQ, hCQ, hfull, hcomponent, hfactor⟩

theorem original_each_prime_has_full_factorizing_normalizers
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
        CoveringFactorizationBranch n S e K hSP := by
  refine ⟨original_invariant_prime_Sylow_exists n hn S e hell, ?_⟩
  intro P hSP
  exact original_prime_normalizer_full_factorizations hnonab n hn S e hfour
    p f hp hpodd hf hlocal hrec hell hdiv P hSP

end CFSG.Wreathed.OriginalCoveringLocalFamily
