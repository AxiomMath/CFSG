module

public import CFSG.CharacterTheory.Wreathed.OriginalStationarityCoverageCriterion
public import CFSG.CharacterTheory.Wreathed.NormalComponentLiftLocal

public section

namespace CFSG.Wreathed.OriginalAllPrime

open CFSG.Wreathed.OriginalStationarityCoverageCriterion
open CFSG.Wreathed.OriginalSylowNormalizerWitness
open CFSG.Wreathed.OriginalSylowCentralizerCoverage
open CFSG.Wreathed.NoncentralScalarSylowCoverage
open CFSG.Wreathed.NormalComponentLift

variable {G : Type} [Group G] [Finite G]

@[expose] def originalX2 (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) : G :=
  wreathModelHom S e (Original.x2 (2 ^ n))

@[expose] def OriginalOrdinarySylow (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {ell : ℕ} (P : Sylow ell (centralizerOddCore n S e)) : Prop :=
  OriginalStationarity (involutionCentralizer n S e) P ∧
    originalX2 n S e ∈
      Subgroup.normalizer (ambientSylow (involutionCentralizer n S e) P : Set G) ∧
    ((∀ a ∈ ambientSylow (involutionCentralizer n S e) P,
        originalX2 n S e * a * (originalX2 n S e)⁻¹ = a) ∨
      (∀ a ∈ ambientSylow (involutionCentralizer n S e) P,
        originalX2 n S e * a * (originalX2 n S e)⁻¹ = a⁻¹))

@[expose] def OriginalAllPrimesOrdinary (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Prop :=
  ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (centralizerOddCore n S e) →
    ∃ P : Sylow ell (centralizerOddCore n S e), OriginalOrdinarySylow n S e P

omit [Finite G] in
theorem ambientSylow_eq_map (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {ell : ℕ} (P : Sylow ell (centralizerOddCore n S e)) :
    ambientSylow (involutionCentralizer n S e) P =
      (originalPrimeSubgroup n S e P).map (involutionCentralizer n S e).subtype :=
  rfl

theorem original_coverage_of_scalar
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    (P : Sylow ell (centralizerOddCore n S e))
    (hnorm : originalX2 n S e ∈
      Subgroup.normalizer (ambientSylow (involutionCentralizer n S e) P : Set G))
    (hscalar : (∀ a ∈ ambientSylow (involutionCentralizer n S e) P,
        originalX2 n S e * a * (originalX2 n S e)⁻¹ = a) ∨
      (∀ a ∈ ambientSylow (involutionCentralizer n S e) P,
        originalX2 n S e * a * (originalX2 n S e)⁻¹ = a⁻¹)) :
    OriginalCoverage n S e P := by
  set N := involutionCentralizer n S e
  set v : N := nModel n hn S e (Original.x2 (2 ^ n)) with hv
  have hvG : (v : G) = originalX2 n S e := rfl
  have hM := original_layer_data hnonab n hn S e hfour
  let : (CFSG.layer (centralizerOddCoreQuotient n S e)).Normal := by
    rw [(wreathed_centralizer_unique_component_data hnonab n hn S e hfour).layer]
    exact (wreathed_centralizer_unique_component_data hnonab n hn S e hfour).normal
  let : (show Subgroup (involutionCentralizer n S e ⧸ centralizerOddCore n S e) from
      CFSG.layer (centralizerOddCoreQuotient n S e)).Normal := by
    change (CFSG.layer (centralizerOddCoreQuotient n S e)).Normal
    infer_instance
  have hvnorm : v ∈ Subgroup.normalizer
      (((P : Subgroup (centralizerOddCore n S e)).map
        (centralizerOddCore n S e).subtype) : Set N) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    have h := Subgroup.mem_normalizer_iff.mp hnorm (a : G)
    constructor
    · intro ha
      have ha' : (a : G) ∈ ambientSylow N P := Subgroup.mem_map_of_mem _ ha
      obtain ⟨b, hb, hbe⟩ := Subgroup.mem_map.mp (h.mp ha')
      have hbeq : b = v * a * v⁻¹ := Subtype.ext hbe
      exact hbeq ▸ hb
    · intro ha
      have ha' : (v : G) * (a : G) * (v : G)⁻¹ ∈ ambientSylow N P :=
        Subgroup.mem_map_of_mem N.subtype ha
      obtain ⟨b, hb, hbe⟩ := Subgroup.mem_map.mp (h.mpr ha')
      have hbeq : b = a := Subtype.ext hbe
      exact hbeq ▸ hb
  have hvscalar : (∀ a ∈ (P : Subgroup (centralizerOddCore n S e)).map
        (centralizerOddCore n S e).subtype, v * a * v⁻¹ = a) ∨
      (∀ a ∈ (P : Subgroup (centralizerOddCore n S e)).map
        (centralizerOddCore n S e).subtype, v * a * v⁻¹ = a⁻¹) := by
    rcases hscalar with hc | hi
    · refine Or.inl fun a ha => Subtype.ext ?_
      exact hc (a : G) (Subgroup.mem_map_of_mem N.subtype ha)
    · refine Or.inr fun a ha => Subtype.ext ?_
      exact hi (a : G) (Subgroup.mem_map_of_mem N.subtype ha)
  exact noncentral_scalar_Sylow_action_gives_quasisimple_centralizer_coverage
    (centralizerOddCore n S e) (CFSG.layer (centralizerOddCoreQuotient n S e)) hM.1 hM.2
    hell hdiv P v hvnorm (centralizerOddCoreMap_y_not_mem_center n hn S e) hvscalar

theorem original_coverage_of_ordinary
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    (P : Sylow ell (centralizerOddCore n S e)) (hP : OriginalOrdinarySylow n S e P) :
    OriginalCoverage n S e P :=
  original_coverage_of_scalar hnonab n hn S e hfour hell hdiv P hP.2.1 hP.2.2

theorem original_all_prime_stationarity_and_coverage_of_ordinary
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (hord : OriginalAllPrimesOrdinary n S e) :
    OriginalAllPrimeStationarity n S e ∧ OriginalAllPrimeCoverage n S e := by
  constructor
  · intro ell hell hdiv
    obtain ⟨P, hP⟩ := hord ell hell hdiv
    exact ⟨P, hP.1⟩
  · intro ell hell hdiv
    obtain ⟨P, hP⟩ := hord ell hell hdiv
    exact ⟨P, original_coverage_of_ordinary hnonab n hn S e hfour hell hdiv P hP⟩

end CFSG.Wreathed.OriginalAllPrime
