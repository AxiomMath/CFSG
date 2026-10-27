module

public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldQuaternionFull
public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldQuaternionProper

public noncomputable section

namespace CFSG.Wreathed.SmallerRecognitionOriginalField

open CFSG.Assembly.LowTwoRank FullSylowCoveringObstruction
open scoped Classical Pointwise

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

omit [IsSimpleGroup G] in
@[expose] def OriginalFullPositionTypeIObstruction
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (p f : ℕ) (K : Subgroup G)
    (hxK : wreathModelHom S e (Original.x (2 ^ n)) ∈ K) : Prop :=
  ∃ (P : Sylow 2 K)
    (hxP : (⟨wreathModelHom S e (Original.x (2 ^ n)), hxK⟩ : K) ∈ P) (g : G)
    (hPS : ((P : Subgroup K).map K.subtype).map (MulAut.conj g).toMonoidHom ≤ S),
    let Kg := K.map (MulAut.conj g).toMonoidHom
    let i := positionedSylowEmbedding S e K P g hPS
    Function.Injective i ∧ Original.Y (2 ^ n) ≤ i.range ∧ i.range = ⊤ ∧
      i ⟨(⟨wreathModelHom S e (Original.x (2 ^ n)), hxK⟩ : K), hxP⟩ =
        Original.x (2 ^ n) ∧
      (∀ a : P, wreathModelHom S e (i a) = g * ((a : K) : G) * g⁻¹) ∧
      g * wreathModelHom S e (Original.x (2 ^ n)) * g⁻¹ =
        wreathModelHom S e (Original.x (2 ^ n)) ∧
      g ∈ involutionCentralizer n S e ∧ Kg < ⊤ ∧ CFSG.oddCore Kg ≠ ⊥ ∧
      ∃ hSKg : (S : Subgroup G) ≤ Kg,
        CFSG.layer (centralizerOddCoreQuotient n S e) ≤
          ComponentCoveringLocal.originalImage n S e Kg ∧
        ComponentCoveringLocal.ComponentCoveringLocalConclusion n hn S e Kg hSKg ∧
        CoveringTypeIObstruction n S e Kg ∧
        OriginalComponentCoreConclusion n hn S e p f Kg hSKg

theorem original_component_cover_arbitrary_sylow_alternatives
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G)
    (K : Subgroup G) (hproper : K < ⊤) (hO : CFSG.oddCore K ≠ ⊥)
    (hxK : wreathModelHom S e (Original.x (2 ^ n)) ∈ K)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e K) :
    OriginalFactorizationCenterIntersection n S e K hxK ∨
      OriginalFullPositionTypeIObstruction n hn S e p f K hxK := by
  let Q : Sylow 2 (originalComponentPreimage n S e K) := Classical.choice inferInstance
  obtain ⟨P, hxP, g, hPS, _, hfix, _, hinj, hY, hx, hvalue⟩ :=
    original_component_covering_quaternion_sylow_position
      hnonab n hn S e hfour K hxK hcover Q
  by_cases hfull : (positionedSylowEmbedding S e K P g hPS).range = ⊤
  · obtain ⟨hg, hKg, hOg, hSKg, hcoverg, hlocalg, halt⟩ :=
      full_position_original_component_alternatives hnonab n hn S e hfour
        p f hp hpodd hf hlocal hrec K hproper hO hxK hcover P g hfix hPS hfull
    rcases halt with hfactor | ⟨htype, hcore⟩
    · exact Or.inl hfactor
    · exact Or.inr ⟨P, hxP, g, hPS, hinj, hY, hfull, hx, hvalue, hfix,
        hg, hKg, hOg, hSKg, hcoverg, hlocalg, htype, hcore⟩
  · have hpne : p ≠ 2 := by
      rintro rfl
      norm_num at hpodd
    exact Or.inl (proper_position_original_factorization_and_intersection
      hnonab n hn S e hfour p f hp hpne hf hlocal K hxK hcover P hxP g hPS hY
        (lt_top_iff_ne_top.mpr hfull) hx)

theorem original_nonfactorizing_component_cover_full_position
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
    (hnonfactor : ¬ OriginalFactorizationCenterIntersection n S e K hxK) :
    OriginalFullPositionTypeIObstruction n hn S e p f K hxK := by
  exact (original_component_cover_arbitrary_sylow_alternatives hnonab n hn S e hfour
    p f hp hpodd hf hlocal hrec K hproper hO hxK hcover).resolve_left hnonfactor

end CFSG.Wreathed.SmallerRecognitionOriginalField
