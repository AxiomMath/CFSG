module

public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldQuaternionAssembly

public noncomputable section
namespace CFSG.Wreathed.SmallerRecognitionOriginalField
open CFSG.Assembly.LowTwoRank
open scoped Classical Pointwise

universe u

theorem odd_subgroup_le_actual_normalizer_odd_core
    {G : Type u} [Group G] (W : Subgroup G) (hodd : Odd (Nat.card W)) :
    W ≤ (CFSG.oddCore (Subgroup.normalizer (W : Set G))).map
      (Subgroup.normalizer (W : Set G)).subtype := by
  let K := Subgroup.normalizer (W : Set G)
  have hWK : W ≤ K := Subgroup.le_normalizer
  have hoddK : Odd (Nat.card (W.subgroupOf K)) := by
    rw [← Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hWK]
    exact hodd
  have hcore : W.subgroupOf K ≤ CFSG.oddCore K := le_sSup ⟨inferInstance, hoddK⟩
  calc
    W = (W.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hWK).symm
    _ ≤ (CFSG.oddCore K).map K.subtype := Subgroup.map_mono hcore

theorem odd_subgroup_actual_normalizer_odd_core_ne_bot
    {G : Type u} [Group G] (W : Subgroup G)
    (hW : W ≠ ⊥) (hodd : Odd (Nat.card W)) :
    CFSG.oddCore (Subgroup.normalizer (W : Set G)) ≠ ⊥ := by
  intro h
  have hle := odd_subgroup_le_actual_normalizer_odd_core W hodd
  rw [h, Subgroup.map_bot] at hle
  exact hW (eq_bot_iff.mpr hle)

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

omit [Finite G] in
theorem original_odd_subgroup_normalizer_proper
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (W : Subgroup G) (hW : W ≠ ⊥) (hodd : Odd (Nat.card W)) :
    Subgroup.normalizer (W : Set G) < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro h
  let : W.Normal := Subgroup.normalizer_eq_top_iff.mp h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W with hbot | htop
  · exact hW hbot
  · have hGodd : Odd (Nat.card G) := by
      rw [htop, Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv] at hodd
      exact hodd
    have hS : Nat.card S = 2 * (2 ^ n) ^ 2 := by
      rw [Nat.card_congr e.toEquiv]
      exact (wreath_center_involution_and_quaternion_coordinates n hn).card
    exact hGodd.not_two_dvd_nat (dvd_trans
      (hS ▸ dvd_mul_right 2 ((2 ^ n) ^ 2)) (Subgroup.card_subgroup_dvd_card _))

omit [Finite G] [IsSimpleGroup G] in
theorem original_odd_normalizer_intersection
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (W : Subgroup G) :
    ComponentCoveringLocal.originalCentralizerSubgroup n S e
      (Subgroup.normalizer (W : Set G)) =
        (Subgroup.normalizer (W : Set G)).comap (involutionCentralizer n S e).subtype := rfl

omit [Finite G] [IsSimpleGroup G] in
theorem original_centralizer_coverage_passes_to_odd_subgroup_normalizer
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (P W : Subgroup G)
    (hWP : W ≤ P)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ((Subgroup.centralizer (P : Set G)).comap (involutionCentralizer n S e).subtype).map
        (centralizerOddCoreMap n S e)) :
    CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e (Subgroup.normalizer (W : Set G)) := by
  apply hcover.trans
  apply Subgroup.map_mono
  intro c hc
  exact Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hWP hc)

omit [Finite G] [IsSimpleGroup G] in
theorem original_centralizing_lift_coverage_passes_to_odd_subgroup_normalizer
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (J : Subgroup (involutionCentralizer n S e))
    (hJ : J.map (centralizerOddCoreMap n S e) =
      CFSG.layer (centralizerOddCoreQuotient n S e))
    (hJR : ∀ j : J, ∀ r : centralizerOddCore n S e,
      (j : involutionCentralizer n S e) * (r : involutionCentralizer n S e) =
        (r : involutionCentralizer n S e) * (j : involutionCentralizer n S e))
    (W : Subgroup G)
    (hWR : W ≤ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype) :
    CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e (Subgroup.normalizer (W : Set G)) := by
  rw [← hJ]
  apply Subgroup.map_mono
  intro j hj
  apply Subgroup.centralizer_le_normalizer _
  apply Subgroup.mem_centralizer_iff.mpr
  intro w hw
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp (hWR hw)
  exact (congrArg (involutionCentralizer n S e).subtype
    (hJR ⟨j, hj⟩ ⟨r, hr⟩)).symm

omit [Finite G] [IsSimpleGroup G] in
theorem original_involution_normalizes_subgroup_of_odd_core
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (W : Subgroup G)
    (hWR : W ≤ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype) :
    wreathModelHom S e (Original.x (2 ^ n)) ∈ Subgroup.normalizer (W : Set G) := by
  apply Subgroup.centralizer_le_normalizer _
  apply Subgroup.mem_centralizer_iff.mpr
  intro w hw
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp (hWR hw)
  exact Subgroup.mem_centralizer_singleton_iff.mp r.property

theorem original_odd_subgroup_normalizer_component_cover_alternatives
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G) (W : Subgroup G)
    (hW : W ≠ ⊥) (hodd : Odd (Nat.card W))
    (hxW : wreathModelHom S e (Original.x (2 ^ n)) ∈ Subgroup.normalizer (W : Set G))
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e (Subgroup.normalizer (W : Set G))) :
    let K := Subgroup.normalizer (W : Set G)
    K < ⊤ ∧ W ≤ (CFSG.oddCore K).map K.subtype ∧ CFSG.oddCore K ≠ ⊥ ∧
      (OriginalFactorizationCenterIntersection n S e K hxW ∨
        OriginalFullPositionTypeIObstruction n hn S e p f K hxW) := by
  have hproper := original_odd_subgroup_normalizer_proper n hn S e W hW hodd
  have hcore := odd_subgroup_actual_normalizer_odd_core_ne_bot W hW hodd
  exact ⟨hproper, odd_subgroup_le_actual_normalizer_odd_core W hodd, hcore,
    original_component_cover_arbitrary_sylow_alternatives hnonab n hn S e hfour
      p f hp hpodd hf hlocal hrec _ hproper hcore hxW hcover⟩

theorem original_centralizer_covered_odd_subgroup_normalizer_alternatives
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G) (P : Subgroup G)
    (hPR : P ≤ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ((Subgroup.centralizer (P : Set G)).comap (involutionCentralizer n S e).subtype).map
        (centralizerOddCoreMap n S e)) :
    ∀ W : Subgroup G, W ≤ P → W ≠ ⊥ →
      ∃ hxW : wreathModelHom S e (Original.x (2 ^ n)) ∈ Subgroup.normalizer (W : Set G),
        let K := Subgroup.normalizer (W : Set G)
        K < ⊤ ∧ W ≤ (CFSG.oddCore K).map K.subtype ∧ CFSG.oddCore K ≠ ⊥ ∧
          (OriginalFactorizationCenterIntersection n S e K hxW ∨
            OriginalFullPositionTypeIObstruction n hn S e p f K hxW) := by
  intro W hWP hW
  have hWR := hWP.trans hPR
  have hodd : Odd (Nat.card W) :=
    (OriginalSylowNormalizerWitness.ambientOddCore_odd (involutionCentralizer n S e)).of_dvd_nat
      (Subgroup.card_dvd_of_le hWR)
  have hxW := original_involution_normalizes_subgroup_of_odd_core n S e W hWR
  refine ⟨hxW, ?_⟩
  exact original_odd_subgroup_normalizer_component_cover_alternatives
    hnonab n hn S e hfour p f hp hpodd hf hlocal hrec W hW hodd hxW
      (original_centralizer_coverage_passes_to_odd_subgroup_normalizer n S e P W hWP hcover)

theorem original_centralizing_lift_odd_subgroup_normalizer_alternatives
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G)
    (J : Subgroup (involutionCentralizer n S e))
    (hJ : J.map (centralizerOddCoreMap n S e) =
      CFSG.layer (centralizerOddCoreQuotient n S e))
    (hJR : ∀ j : J, ∀ r : centralizerOddCore n S e,
      (j : involutionCentralizer n S e) * (r : involutionCentralizer n S e) =
        (r : involutionCentralizer n S e) * (j : involutionCentralizer n S e)) :
    ∀ W : Subgroup G,
      W ≤ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype → W ≠ ⊥ →
      ∃ hxW : wreathModelHom S e (Original.x (2 ^ n)) ∈ Subgroup.normalizer (W : Set G),
        let K := Subgroup.normalizer (W : Set G)
        K < ⊤ ∧ W ≤ (CFSG.oddCore K).map K.subtype ∧ CFSG.oddCore K ≠ ⊥ ∧
          (OriginalFactorizationCenterIntersection n S e K hxW ∨
            OriginalFullPositionTypeIObstruction n hn S e p f K hxW) := by
  intro W hWR hW
  have hodd : Odd (Nat.card W) :=
    (OriginalSylowNormalizerWitness.ambientOddCore_odd (involutionCentralizer n S e)).of_dvd_nat
      (Subgroup.card_dvd_of_le hWR)
  have hxW := original_involution_normalizes_subgroup_of_odd_core n S e W hWR
  refine ⟨hxW, ?_⟩
  exact original_odd_subgroup_normalizer_component_cover_alternatives
    hnonab n hn S e hfour p f hp hpodd hf hlocal hrec W hW hodd hxW
      (original_centralizing_lift_coverage_passes_to_odd_subgroup_normalizer
        n S e J hJ hJR W hWR)

end CFSG.Wreathed.SmallerRecognitionOriginalField
