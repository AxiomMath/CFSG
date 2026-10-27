module

public import CFSG.CharacterTheory.Wreathed.OriginalCoveringLocalFamilyFactorizations
public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldQuaternionAssembly
public import CFSG.CharacterTheory.Wreathed.CompatibleCentralizerFamiliesLocal

public section

open scoped Classical Pointwise

namespace CFSG.Wreathed.ComponentCoverFactorizations

open CFSG.Assembly.LowTwoRank FullSylowCoveringObstruction SmallerRecognitionOriginalField
  OriginalCoveringLocalFamily

variable {G : Type} [Group G]

theorem le_oddCore_normalizer (W : Subgroup G) (hWodd : Odd (Nat.card W)) :
    W ≤ (CFSG.oddCore (Subgroup.normalizer (W : Set G))).map
      (Subgroup.normalizer (W : Set G)).subtype := by
  intro w hw
  have hle : W.subgroupOf (Subgroup.normalizer (W : Set G)) ≤
      CFSG.oddCore (Subgroup.normalizer (W : Set G)) := by
    apply le_sSup
    refine ⟨Subgroup.normal_in_normalizer, ?_⟩
    rw [CFSG.natCard_subgroupOf_eq _ _ Subgroup.le_normalizer]
    exact hWodd
  exact ⟨⟨w, Subgroup.le_normalizer hw⟩, hle hw, rfl⟩

theorem normalizer_lt_top_of_odd [IsSimpleGroup G] (h2 : 2 ∣ Nat.card G) (W : Subgroup G)
    (hW : W ≠ ⊥) (hWodd : Odd (Nat.card W)) : Subgroup.normalizer (W : Set G) < ⊤ := by
  refine lt_top_iff_ne_top.mpr fun htop => ?_
  have hWn : W.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases hWn.eq_bot_or_eq_top with h | h
  · exact hW h
  · rw [h, Subgroup.card_top] at hWodd
    exact (Nat.not_even_iff_odd.mpr hWodd) (even_iff_two_dvd.mpr h2)

@[expose] def NormalizerFactorization (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (W : Subgroup G) : Prop :=
  Subgroup.normalizer (W : Set G) < ⊤ ∧
    W ≤ (CFSG.oddCore (Subgroup.normalizer (W : Set G))).map
      (Subgroup.normalizer (W : Set G)).subtype ∧
    (CFSG.oddCore (Subgroup.normalizer (W : Set G))).map
      (Subgroup.normalizer (W : Set G)).subtype ≠ ⊥ ∧
    (Subgroup.normalizer (W : Set G) : Set G) =
      ((CFSG.oddCore (Subgroup.normalizer (W : Set G))).map
        (Subgroup.normalizer (W : Set G)).subtype : Set G) *
        (Subgroup.normalizer (W : Set G) ⊓ involutionCentralizer n S e : Set G) ∧
    (CFSG.oddCore (Subgroup.normalizer (W : Set G))).map
        (Subgroup.normalizer (W : Set G)).subtype ⊓ involutionCentralizer n S e =
      (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊓
        Subgroup.normalizer (W : Set G)

variable [Finite G] [IsSimpleGroup G]

theorem smaller_recognition_factors_full_sylow_component_covering_subgroups
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G)
    (K : Subgroup G) (hproper : K < ⊤) (hSK : (S : Subgroup G) ≤ K)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e K)
    (hO : CFSG.oddCore K ≠ ⊥) :
    (K : Set G) = ((CFSG.oddCore K).map K.subtype : Set G) *
        (K ⊓ involutionCentralizer n S e : Set G) ∧
      (CFSG.oddCore K).map K.subtype ⊓ involutionCentralizer n S e =
        (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊓ K := by
  obtain ⟨-, halt⟩ := full_sylow_component_cover_original_field_alternatives
    hnonab n hn S e hfour p f hp hpodd hf hlocal hrec K hSK hproper hcover
  rcases halt with hfactor | htype
  · exact ⟨hfactor.factorization, hfactor.core_intersection⟩
  · exact False.elim (hO (original_component_core_forces_trivial_odd_core
      hnonab n hn S e hfour p f hp hpodd hf hq hlocal K hSK htype.2))

theorem smaller_recognition_factors_every_involution_containing_component_covering_subgroup
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G)
    (K : Subgroup G) (hproper : K < ⊤)
    (hxK : wreathModelHom S e (Original.x (2 ^ n)) ∈ K)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e K)
    (hO : CFSG.oddCore K ≠ ⊥) :
    OriginalFactorizationCenterIntersection n S e K hxK := by
  rcases original_component_cover_arbitrary_sylow_alternatives hnonab n hn S e hfour
      p f hp hpodd hf hlocal hrec K hproper hO hxK hcover with hfactor | htype
  · exact hfactor
  · obtain ⟨P, hxP, g, hPS, hinj, hY, hfull, hx, hvalue, hfix, hg, hKg, hOg, hSKg, hcoverg,
      hlocalg, htypeI, hcore⟩ := htype
    exact False.elim (hOg (original_component_core_forces_trivial_odd_core
      hnonab n hn S e hfour p f hp hpodd hf hq hlocal _ hSKg hcore))

omit [Finite G] [IsSimpleGroup G] in
theorem original_x_mem_normalizer_of_le (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (W : Subgroup G) (hW : W ≤ involutionCentralizer n S e) :
    wreathModelHom S e (Original.x (2 ^ n)) ∈ Subgroup.normalizer (W : Set G) := by
  apply CFSG.centralizer_le_normalizer W
  intro w hw
  exact (Eq.symm (SemiconjBy.eq ((hW hw) _ rfl)))

omit [IsSimpleGroup G] in
theorem odd_card_of_le_oddCore (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (W : Subgroup G)
    (hW : W ≤ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype) :
    Odd (Nat.card W) := by
  have hR : Odd (Nat.card ((centralizerOddCore n S e).map
      (involutionCentralizer n S e).subtype)) := by
    rw [Subgroup.card_subtype]
    exact CFSG.Wreathed.weakClosure_oddCore_card _
  exact Odd.of_dvd_nat hR (Subgroup.card_dvd_of_le hW)

theorem normalizerFactorization_of_cover
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G)
    (W : Subgroup G) (hW : W ≠ ⊥) (hWodd : Odd (Nat.card W))
    (hxW : wreathModelHom S e (Original.x (2 ^ n)) ∈ Subgroup.normalizer (W : Set G))
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e (Subgroup.normalizer (W : Set G))) :
    NormalizerFactorization n S e W := by
  have h2 : 2 ∣ Nat.card G := by
    rw [← CFSG.Wreathed.CompatibleFamilies.orderOf_x S e hn]
    exact orderOf_dvd_natCard _
  have hK := normalizer_lt_top_of_odd h2 W hW hWodd
  have hWO := le_oddCore_normalizer W hWodd
  have hOG : (CFSG.oddCore (Subgroup.normalizer (W : Set G))).map
      (Subgroup.normalizer (W : Set G)).subtype ≠ ⊥ := fun h => hW (le_bot_iff.mp (h ▸ hWO))
  have hO : CFSG.oddCore (Subgroup.normalizer (W : Set G)) ≠ ⊥ := fun h => hOG (by
    rw [h, Subgroup.map_bot])
  obtain ⟨hfac, -, hint⟩ :=
    smaller_recognition_factors_every_involution_containing_component_covering_subgroup
      hnonab n hn S e hfour p f hp hpodd hf hq hlocal hrec _ hK hxW hcover hO
  exact ⟨hK, hWO, hOG, hfac, hint⟩

theorem component_covering_criterion_produces_actual_odd_subgroup_normalizer_factorizations
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G) :
    (∀ W : Subgroup G, W ≠ ⊥ → Odd (Nat.card W) →
      wreathModelHom S e (Original.x (2 ^ n)) ∈ Subgroup.normalizer (W : Set G) →
      CFSG.layer (centralizerOddCoreQuotient n S e) ≤
        ComponentCoveringLocal.originalImage n S e (Subgroup.normalizer (W : Set G)) →
      NormalizerFactorization n S e W) ∧
    (∀ P : Subgroup G,
      P ≤ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype →
      CFSG.layer (centralizerOddCoreQuotient n S e) ≤
        ((Subgroup.centralizer (P : Set G)).subgroupOf (involutionCentralizer n S e)).map
          (centralizerOddCoreMap n S e) →
      ∀ W : Subgroup G, W ≤ P → W ≠ ⊥ → NormalizerFactorization n S e W) ∧
    (∀ J : Subgroup G, J ≤ involutionCentralizer n S e →
      (J.subgroupOf (involutionCentralizer n S e)).map (centralizerOddCoreMap n S e) =
        CFSG.layer (centralizerOddCoreQuotient n S e) →
      ⁅J, (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype⁆ = ⊥ →
      ∀ W : Subgroup G,
        W ≤ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype →
        W ≠ ⊥ → NormalizerFactorization n S e W) := by
  have hcrit := normalizerFactorization_of_cover hnonab n hn S e hfour p f hp hpodd hf hq
    hlocal hrec
  have hRN : (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ≤
      involutionCentralizer n S e := by
    rintro _ ⟨r, -, rfl⟩
    exact r.property
  refine ⟨hcrit, ?_, ?_⟩
  · intro P hP hcov W hWP hW
    have hWR := hWP.trans hP
    refine hcrit W hW (odd_card_of_le_oddCore n S e W hWR)
      (original_x_mem_normalizer_of_le n S e W (hWR.trans hRN)) (hcov.trans ?_)
    apply Subgroup.map_mono
    intro c hc
    exact CFSG.centralizer_le_normalizer W (Subgroup.centralizer_le hWP hc)
  · intro J hJN hJ hJR W hWR hW
    refine hcrit W hW (odd_card_of_le_oddCore n S e W hWR)
      (original_x_mem_normalizer_of_le n S e W (hWR.trans hRN)) ?_
    rw [← hJ]
    apply Subgroup.map_mono
    intro c hc
    have hcR : (c : G) ∈ Subgroup.centralizer
        (((centralizerOddCore n S e).map (involutionCentralizer n S e).subtype : Subgroup G) :
          Set G) := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJR hc
    exact CFSG.centralizer_le_normalizer W (Subgroup.centralizer_le hWR hcR)

end CFSG.Wreathed.ComponentCoverFactorizations
