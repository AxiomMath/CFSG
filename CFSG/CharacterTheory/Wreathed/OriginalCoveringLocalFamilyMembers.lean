module

public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldQuaternionNormalizer
public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldCovering

public noncomputable section
open scoped Classical Pointwise
namespace CFSG.Wreathed.OriginalCoveringLocalFamily
open OriginalSylowNormalizerWitness OriginalCoveringSylowNormalizer
open CFSG.Assembly.LowTwoRank FullSylowCoveringObstruction SmallerRecognitionOriginalField

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
@[expose] def IsOriginalCoveringLocal (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (ell : ℕ) (D : Subgroup G) : Prop :=
  ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup ell U ∧ D = Subgroup.normalizer (U : Set G) ∧
    (S : Subgroup G) ≤ D ∧
    (involutionCentralizer n S e : Set G) =
      (ambientOddCore (involutionCentralizer n S e) : Set G) *
        (D ⊓ involutionCentralizer n S e : Set G) ∧
    ∃ P : Sylow ell (centralizerOddCore n S e),
      ambientSylow (involutionCentralizer n S e) P ≤ D

theorem original_covering_local_family_nonempty (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) {ell : ℕ} (hell : ell.Prime)
    (hdiv : ell ∣ Nat.card (centralizerOddCore n S e)) :
    ∃ D : Subgroup G, IsOriginalCoveringLocal n S e ell D := by
  obtain ⟨P, hSP⟩ := original_invariant_prime_Sylow_exists n hn S e hell
  let N := involutionCentralizer n S e
  let U := ambientSylow N P
  refine ⟨Subgroup.normalizer (U : Set G), U,
    original_Sylow_nontrivial hell N hdiv P, ?_, rfl, hSP,
    original_sylow_normalizer_set_product hell N P, P, Subgroup.le_normalizer⟩
  exact (P.isPGroup'.map (CFSG.oddCore N).subtype).map N.subtype

variable [IsSimpleGroup G]

theorem original_covering_local_family_member_structure
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    (D : Subgroup G) (hD : IsOriginalCoveringLocal n S e ell D) :
    D < ⊤ ∧ ambientOddCore D ≠ ⊥ ∧ CFSG.oddCore D ≠ ⊥ ∧
      ∀ U : Subgroup G, U ≠ ⊥ → IsPGroup ell U → D = Subgroup.normalizer (U : Set G) →
        U ≤ ambientOddCore D := by
  let : Fact ell.Prime := ⟨hell⟩
  have hellodd : Odd ell :=
    (CFSG.ComponentClassification.OddCore.odd_card (involutionCentralizer n S e)).of_dvd_nat hdiv
  obtain ⟨U, hU, hUp, rfl, hSD, hcover, hP⟩ := hD
  have hUodd : Odd (Nat.card U) := by
    obtain ⟨a, ha⟩ := hUp.exists_card_eq
    rw [ha]
    exact hellodd.pow
  have hO := odd_subgroup_actual_normalizer_odd_core_ne_bot U hU hUodd
  have hOambient : ambientOddCore (Subgroup.normalizer (U : Set G)) ≠ ⊥ := by
    intro h
    have hUO := odd_subgroup_le_actual_normalizer_odd_core U hUodd
    exact hU (eq_bot_iff.mpr (hUO.trans_eq h))
  refine ⟨original_odd_subgroup_normalizer_proper n hn S e U hU hUodd, hOambient, hO, ?_⟩
  intro V hV hVp hnorm
  have hVodd : Odd (Nat.card V) := by
    obtain ⟨a, ha⟩ := hVp.exists_card_eq
    rw [ha]
    exact hellodd.pow
  rw [hnorm]
  exact odd_subgroup_le_actual_normalizer_odd_core V hVodd

theorem original_covering_local_family_member_full_original_field_alternatives
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G)
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    (D : Subgroup G) (hD : IsOriginalCoveringLocal n S e ell D) :
    5 ≤ p ^ f ∧ D < ⊤ ∧ ambientOddCore D ≠ ⊥ ∧ CFSG.oddCore D ≠ ⊥ ∧
      ∃ hSD : (S : Subgroup G) ≤ D,
        FullSylowCoveringConclusion n S e D hSD ∧
        ComponentCoveringLocal.ComponentCoveringLocalConclusion n hn S e D hSD ∧
        (CoveringFactorizationBranch n S e D hSD ∨
          CoveringTypeIObstruction n S e D ∧
            OriginalComponentCoreConclusion n hn S e p f D hSD) := by
  have hstructure := original_covering_local_family_member_structure n hn S e hell hdiv D hD
  obtain ⟨U, hU, hUp, hDU, hSD, hcover, hP⟩ := hD
  have hwhole : ComponentCoveringLocal.originalImage n S e D = ⊤ := by
    apply eq_top_iff.mpr
    intro z hz
    let N := involutionCentralizer n S e
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore N) z
    have haN : (a : G) ∈ (ambientOddCore N : Set G) * (D ⊓ N : Set G) := hcover ▸ a.property
    obtain ⟨r, hr, c, hc, hrc⟩ := Set.mem_mul.mp haN
    obtain ⟨rN, hrN, hrval⟩ := hr
    change (rN : G) = r at hrval
    have hqR : QuotientGroup.mk' (CFSG.oddCore N) rN = 1 := QuotientGroup.eq_one_iff _ |>.mpr hrN
    let cN : N := ⟨c, hc.2⟩
    have heq : rN * cN = a := Subtype.ext (by
      change (rN : G) * c = (a : G)
      rw [hrval]
      exact hrc)
    refine ⟨cN, hc.1, ?_⟩
    change QuotientGroup.mk' (CFSG.oddCore N) cN = QuotientGroup.mk' (CFSG.oddCore N) a
    rw [← heq, map_mul, hqR, one_mul]
  have hcoverL : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e D := hwhole ▸ le_top
  obtain ⟨hlocalD, halt⟩ := full_sylow_component_cover_original_field_alternatives
    hnonab n hn S e hfour p f hp hpodd hf hlocal hrec D hSD hstructure.1 hcoverL
  refine ⟨statedPSL_two_odd_parameter_at_least_five p f hp hpodd hf hlocal,
    hstructure.1, hstructure.2.1, hstructure.2.2.1, hSD, ?_, hlocalD, halt⟩
  exact full_Sylow_covering_subgroup_has_factorization_or_exact_typeI_obstruction
    hnonab n hn S e D hSD hcover

end CFSG.Wreathed.OriginalCoveringLocalFamily
