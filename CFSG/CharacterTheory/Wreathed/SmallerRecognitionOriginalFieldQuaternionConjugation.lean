module
public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldQuaternionPosition

public noncomputable section
namespace CFSG.Wreathed.SmallerRecognitionOriginalField
open scoped Classical
universe u
variable {G : Type u} [Group G]

theorem original_involution_fixing_conjugator_mem_centralizer
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g : G)
    (hfix : g * wreathModelHom S e (Original.x (2 ^ n)) * g⁻¹ =
      wreathModelHom S e (Original.x (2 ^ n))) : g ∈ involutionCentralizer n S e := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  exact mul_inv_eq_iff_eq_mul.mp hfix

theorem original_centralizer_conjugation_ambient
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g b : involutionCentralizer n S e) :
    ((MulAut.conj g b : involutionCentralizer n S e) : G) =
      (g : G) * (b : G) * (g : G)⁻¹ := rfl

theorem original_component_image_conjugation
    {G : Type} [Group G] (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (g : involutionCentralizer n S e) :
    ComponentCoveringLocal.originalImage n S e (K.map (MulAut.conj (g : G)).toMonoidHom) =
      (ComponentCoveringLocal.originalImage n S e K).map
        (MulAut.conj (centralizerOddCoreMap n S e g)).toMonoidHom := by
  ext h
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨k, hk, heq⟩ := Subgroup.mem_map.mp hb
    let kg : involutionCentralizer n S e := g⁻¹ * b * g
    have hkg : (kg : G) = k := by
      change (g : G)⁻¹ * (b : G) * (g : G) = k
      have hbval : (b : G) = (g : G) * k * (g : G)⁻¹ := heq.symm
      rw [hbval]
      simp [mul_assoc]
    have hkgK : kg ∈ ComponentCoveringLocal.originalCentralizerSubgroup n S e K := by
      change (kg : G) ∈ K
      rw [hkg]
      exact hk
    refine Subgroup.mem_map.mpr ⟨centralizerOddCoreMap n S e kg,
      Subgroup.mem_map.mpr ⟨kg, hkgK, rfl⟩, ?_⟩
    simp [kg, MulAut.conj_apply, map_mul, map_inv, mul_assoc]
  · rintro ⟨h, ⟨b, hb, rfl⟩, rfl⟩
    refine Subgroup.mem_map.mpr ⟨g * b * g⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨(b : G), hb, rfl⟩
    · simp [MulAut.conj_apply, map_mul, map_inv]

theorem ambient_conjugation_odd_core_image
    (K : Subgroup G) (g : G) :
    (CFSG.oddCore (K.map (MulAut.conj g).toMonoidHom)).map
      (K.map (MulAut.conj g).toMonoidHom).subtype =
      ((CFSG.oddCore K).map K.subtype).map (MulAut.conj g).toMonoidHom := by
  let E := K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hcore := CFSG.ComponentClassification.OddCore.equiv_invariant E
  change (CFSG.oddCore K).map E.toMonoidHom =
    CFSG.oddCore (K.map (MulAut.conj g).toMonoidHom) at hcore
  rw [← hcore, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem original_component_coverage_after_conjugation
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e K)
    (g : involutionCentralizer n S e) :
    CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e
        (K.map (MulAut.conj (g : G)).toMonoidHom) := by
  let : (CFSG.layer (centralizerOddCoreQuotient n S e)).Normal :=
    ActualCentralizerSemilinear.actual_layer_normal hnonab n hn S e hfour
  rw [original_component_image_conjugation]
  have hM := Subgroup.Normal.map_conj_eq
    (CFSG.layer (centralizerOddCoreQuotient n S e)) (centralizerOddCoreMap n S e g)
  exact hM ▸ Subgroup.map_mono hcover

theorem full_positioned_image_original_sylow_containment
    (S : Sylow 2 G) {m : ℕ} (e : S ≃* Wreath m) (K : Subgroup G)
    (P : Sylow 2 K) (g : G)
    (hPS : ((P : Subgroup K).map K.subtype).map (MulAut.conj g).toMonoidHom ≤ S)
    (hfull : (positionedSylowEmbedding S e K P g hPS).range = ⊤) :
    (S : Subgroup G) ≤ K.map (MulAut.conj g).toMonoidHom := by
  intro s hs
  let sS : S := ⟨s, hs⟩
  obtain ⟨p, hp⟩ := MonoidHom.range_eq_top.mp hfull (e sS)
  refine Subgroup.mem_map.mpr ⟨((p : K) : G), (p : K).property, ?_⟩
  have h := positionedSylowEmbedding_ambient S e K P g hPS p
  rw [hp] at h
  simpa [wreathModelHom] using h.symm

theorem conjugated_original_subgroup_proper_and_odd_core
    (K : Subgroup G) (g : G) (hproper : K < ⊤) (hO : CFSG.oddCore K ≠ ⊥) :
    K.map (MulAut.conj g).toMonoidHom < ⊤ ∧
      CFSG.oddCore (K.map (MulAut.conj g).toMonoidHom) ≠ ⊥ := by
  have hK : K.map (MulAut.conj g).toMonoidHom ≠ ⊤ := by
    intro ht
    have htop : (⊤ : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective
    have hEq : K = ⊤ := Subgroup.map_injective (MulAut.conj g).injective (ht.trans htop.symm)
    exact hproper.ne hEq
  refine ⟨lt_top_iff_ne_top.mpr hK, ?_⟩
  intro ho
  have hh := ambient_conjugation_odd_core_image K g
  rw [ho, Subgroup.map_bot] at hh
  have hc : (CFSG.oddCore K).map K.subtype = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp hh.symm
  exact hO ((Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp hc)

theorem original_full_position_component_covering_data
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G) (hproper : K < ⊤) (hO : CFSG.oddCore K ≠ ⊥)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e K)
    (P : Sylow 2 K) (g : G)
    (hfix : g * wreathModelHom S e (Original.x (2 ^ n)) * g⁻¹ =
      wreathModelHom S e (Original.x (2 ^ n)))
    (hPS : ((P : Subgroup K).map K.subtype).map (MulAut.conj g).toMonoidHom ≤ S)
    (hfull : (positionedSylowEmbedding S e K P g hPS).range = ⊤) :
    let Kg := K.map (MulAut.conj g).toMonoidHom
    g ∈ involutionCentralizer n S e ∧ Kg < ⊤ ∧ CFSG.oddCore Kg ≠ ⊥ ∧
      (S : Subgroup G) ≤ Kg ∧
      CFSG.layer (centralizerOddCoreQuotient n S e) ≤
        ComponentCoveringLocal.originalImage n S e Kg := by
  have hg := original_involution_fixing_conjugator_mem_centralizer n S e g hfix
  obtain ⟨hKg, hOg⟩ := conjugated_original_subgroup_proper_and_odd_core K g hproper hO
  exact ⟨hg, hKg, hOg, full_positioned_image_original_sylow_containment S e K P g hPS hfull,
    original_component_coverage_after_conjugation hnonab n hn S e hfour K hcover ⟨g, hg⟩⟩

end CFSG.Wreathed.SmallerRecognitionOriginalField
