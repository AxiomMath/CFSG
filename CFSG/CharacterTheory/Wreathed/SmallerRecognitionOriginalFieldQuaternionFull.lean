module

public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldQuaternionTransport
public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldComponent
public import CFSG.CharacterTheory.Wreathed.ComponentCoveringLocalConclusion

public noncomputable section

namespace CFSG.Wreathed.SmallerRecognitionOriginalField

open CFSG.Assembly.LowTwoRank FullSylowCoveringObstruction
open scoped Classical Pointwise

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

omit [IsSimpleGroup G] in
@[expose] def OriginalComponentCoreConclusion
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (p f : ℕ) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) : Prop :=
  let O := CFSG.oddCore K
  let X := K ⧸ O
  let alpha := QuotientGroup.mk' O
  let T := subgroupSylow S K hSK
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
      (SL : Subgroup L).map L.subtype = ((S : Subgroup G).subgroupOf K).map alpha ∧
      ∃ (E : S ≃* SL) (eL : SL ≃* Wreath (2 ^ n)),
        (∀ s : S, ((E s : L) : X) = alpha (⟨(s : G), hSK s.property⟩ : K)) ∧
        ∀ s : S, eL (E s) = e s) ∧
    ((p ^ f % 4 = 1 ∧ StatedClassicalModel L .PSL 3 p f) ∨
      (p ^ f % 4 = 3 ∧ StatedClassicalModel L .PSU 3 p f)) ∧
    ∃ (hLN : L.Normal) (hodd : Odd L.index),
      letI : L.Normal := hLN
      ∃ hnormal : (ComponentCoveringLocal.originalImage n S e K).Normal,
        OriginalComponentFullCenterIdentification n hn S e K hSK hnormal L hodd

omit [Finite G] [IsSimpleGroup G] in
@[expose] def OriginalFactorizationCenterIntersection
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hxK : wreathModelHom S e (Original.x (2 ^ n)) ∈ K) : Prop :=
  (K : Set G) = ((CFSG.oddCore K).map K.subtype : Set G) *
    (K ⊓ involutionCentralizer n S e : Set G) ∧
  QuotientGroup.mk' (CFSG.oddCore K)
    (⟨wreathModelHom S e (Original.x (2 ^ n)), hxK⟩ : K) ∈
      Subgroup.center (K ⧸ CFSG.oddCore K) ∧
  (CFSG.oddCore K).map K.subtype ⊓ involutionCentralizer n S e =
    (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊓ K

theorem full_sylow_component_cover_original_field_alternatives
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) (hproper : K < ⊤)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e K) :
    ComponentCoveringLocal.ComponentCoveringLocalConclusion n hn S e K hSK ∧
      (CoveringFactorizationBranch n S e K hSK ∨
        CoveringTypeIObstruction n S e K ∧
          OriginalComponentCoreConclusion n hn S e p f K hSK) := by
  have hpne : p ≠ 2 := by
    rintro rfl
    norm_num at hpodd
  have hfull :=
    ComponentCoveringLocal.component_covering_full_Sylow_subgroup_local_layer_and_fusion_alternative
      hnonab n hn S e hfour p f hp hpne hf hlocal K hSK hcover
  refine ⟨hfull, ?_⟩
  rcases hfull.alternatives with hfactor | htype
  · exact Or.inl hfactor
  · exact Or.inr ⟨htype,
      smaller_recognition_identifies_component_obstruction_over_original_field
        hnonab n hn S e hfour p f hp hpodd hf hlocal hrec K hSK hproper hcover
          htype.one_involution_class htype.no_index_two⟩

theorem full_position_original_component_alternatives
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G)
    (K : Subgroup G) (hproper : K < ⊤) (hO : CFSG.oddCore K ≠ ⊥)
    (hxK : wreathModelHom S e (Original.x (2 ^ n)) ∈ K)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e K)
    (P : Sylow 2 K) (g : G)
    (hfix : g * wreathModelHom S e (Original.x (2 ^ n)) * g⁻¹ =
      wreathModelHom S e (Original.x (2 ^ n)))
    (hPS : ((P : Subgroup K).map K.subtype).map (MulAut.conj g).toMonoidHom ≤ S)
    (hfull : (positionedSylowEmbedding S e K P g hPS).range = ⊤) :
    let Kg := K.map (MulAut.conj g).toMonoidHom
    g ∈ involutionCentralizer n S e ∧ Kg < ⊤ ∧ CFSG.oddCore Kg ≠ ⊥ ∧
      ∃ hSKg : (S : Subgroup G) ≤ Kg,
        CFSG.layer (centralizerOddCoreQuotient n S e) ≤
          ComponentCoveringLocal.originalImage n S e Kg ∧
        ComponentCoveringLocal.ComponentCoveringLocalConclusion n hn S e Kg hSKg ∧
        (OriginalFactorizationCenterIntersection n S e K hxK ∨
          CoveringTypeIObstruction n S e Kg ∧
            OriginalComponentCoreConclusion n hn S e p f Kg hSKg) := by
  let Kg := K.map (MulAut.conj g).toMonoidHom
  obtain ⟨hg, hKg, hOg, hSKg, hcoverg⟩ := original_full_position_component_covering_data
    hnonab n hn S e hfour K hproper hO hcover P g hfix hPS hfull
  obtain ⟨hlocalg, halt⟩ := full_sylow_component_cover_original_field_alternatives
    hnonab n hn S e hfour p f hp hpodd hf hlocal hrec Kg hSKg hKg hcoverg
  refine ⟨hg, hKg, hOg, hSKg, hcoverg, hlocalg, ?_⟩
  rcases halt with hfactor | htype
  · left
    apply (original_conjugation_factorization_center_intersection_iff
      n S e K hxK g hfix).mp
    exact ⟨hfactor.factorization, hfactor.original_involution_central,
      hfactor.core_intersection⟩
  · exact Or.inr htype

end CFSG.Wreathed.SmallerRecognitionOriginalField
