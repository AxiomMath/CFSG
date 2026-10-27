module

public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalField

public noncomputable section

namespace CFSG.Wreathed.SmallerRecognitionOriginalField

open CFSG.Assembly.LowTwoRank FullSylowCoveringObstruction
open scoped Classical Pointwise

theorem statedPSL_two_odd_parameter_at_least_five {J : Type} [Group J]
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : StatedClassicalModel J .PSL 2 p f) : 5 ≤ p ^ f := by
  have hthree : 3 ≤ p ^ f := (hp.odd_iff.mp hpodd).trans (Nat.le_self_pow (by omega) p)
  have hne : p ^ f ≠ 3 := by
    intro heq
    exact hmodel.1.2.2.2.2 (by simp only [heq])
  obtain ⟨k, hk⟩ := hpodd.pow (n := f)
  omega

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

@[expose] def OriginalCoveringCoreConclusion
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (p f : ℕ) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : (involutionCentralizer n S e : Set G) =
      ((centralizerOddCore n S e).map (involutionCentralizer n S e).subtype : Set G) *
        (K ⊓ involutionCentralizer n S e : Set G)) : Prop :=
    let O := CFSG.oddCore K
    let X := K ⧸ O
    let alpha := QuotientGroup.mk' O
    let T := FullSylowCoveringObstruction.subgroupSylow S K hSK
    let Sbar := T.mapSurjective (QuotientGroup.mk'_surjective O)
    let L := SimpleOddIndexQuotient.involutionClosure X
    L.Normal ∧ L ≠ ⊥ ∧
      (∀ N : Subgroup X, N.Normal → N ≤ L → N = ⊥ ∨ N = L) ∧
      (∀ N : Subgroup X, N.Normal → N ≠ ⊥ →
        (∀ M : Subgroup X, M.Normal → M ≤ N → M = ⊥ ∨ M = N) → N = L) ∧
      IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧ Odd L.index ∧
      (Sbar : Subgroup X) ≤ L ∧ Subgroup.centralizer (L : Set X) = ⊥ ∧
      (∃ SL : Sylow 2 L,
        (SL : Subgroup L) = (Sbar : Subgroup X).subgroupOf L ∧
        (SL : Subgroup L).map L.subtype =
          ((S : Subgroup G).subgroupOf K).map alpha ∧
        ∃ (E : S ≃* SL) (eL : SL ≃* Wreath (2 ^ n)),
          (∀ s : S, ((E s : L) : X) = alpha (⟨(s : G), hSK s.property⟩ : K)) ∧
          ∀ s : S, eL (E s) = e s) ∧
      ((p ^ f % 4 = 1 ∧ StatedClassicalModel L .PSL 3 p f) ∨
        (p ^ f % 4 = 3 ∧ StatedClassicalModel L .PSU 3 p f)) ∧
      ∃ (hLN : L.Normal) (hodd : Odd L.index),
        letI : L.Normal := hLN
        CoveringOriginalFullCenterIdentification n hn S e K hSK
          (actual_odd_core_covering_iff_product.mpr hcover) L hodd

theorem smaller_recognition_original_covering_product
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) (hproper : K < ⊤)
    (hcover : (involutionCentralizer n S e : Set G) =
      ((centralizerOddCore n S e).map (involutionCentralizer n S e).subtype : Set G) *
        (K ⊓ involutionCentralizer n S e : Set G))
    (hfusion : ∀ x y : K, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hindex : ∀ D : Subgroup K, D.index ≠ 2) :
    OriginalCoveringCoreConclusion n hn S e p f K hSK hcover :=
  smaller_recognition_identifies_covering_obstruction_over_original_field hnonab n hn S e
    hfour p f hp hpodd hf hlocal hrec K hSK hproper
      (actual_odd_core_covering_iff_product.mpr hcover) hfusion hindex

theorem smaller_recognition_original_covering_typeI
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) (hproper : K < ⊤)
    (hcover : (involutionCentralizer n S e : Set G) =
      ((centralizerOddCore n S e).map (involutionCentralizer n S e).subtype : Set G) *
        (K ⊓ involutionCentralizer n S e : Set G))
    (hnonfactor : (K : Set G) ≠ ((CFSG.oddCore K).map K.subtype : Set G) *
      (K ⊓ involutionCentralizer n S e : Set G)) :
    FullSylowCoveringConclusion n S e K hSK ∧
      CoveringTypeIObstruction n S e K ∧
      OriginalCoveringCoreConclusion n hn S e p f K hSK hcover := by
  have hfull := full_Sylow_covering_subgroup_has_factorization_or_exact_typeI_obstruction
    hnonab n hn S e K hSK hcover
  have htype : CoveringTypeIObstruction n S e K := by
    rcases hfull.alternatives with hfactor | htype
    · exact False.elim (hnonfactor hfactor.factorization)
    · exact htype
  exact ⟨hfull, htype, smaller_recognition_original_covering_product hnonab n hn S e
    hfour p f hp hpodd hf hlocal hrec K hSK hproper hcover
      htype.one_involution_class htype.no_index_two⟩

end CFSG.Wreathed.SmallerRecognitionOriginalField
