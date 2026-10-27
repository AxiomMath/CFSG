module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeOrdinary
public import CFSG.LocalAnalysis.ABGTheoremB.Setting

public section

namespace CFSG.Wreathed.OriginalAllPrime

open CFSG.Wreathed.OriginalStationarityCoverageCriterion
open CFSG.Wreathed.OriginalSylowNormalizerWitness
open CFSG.Wreathed.OriginalSylowCentralizerCoverage
open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

@[expose] def wreathedSetting (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) :
    CFSG.ABGTheoremB.Setting G where
  x := wreathModelHom S e (Original.x (2 ^ n))
  x₂ := originalX2 n S e
  S := S
  height := n
  p := p
  f := f
  L₀ := ((CFSG.layer (centralizerOddCoreQuotient n S e)).comap
    (centralizerOddCoreMap n S e)).map (involutionCentralizer n S e).subtype

omit [Finite G] in
theorem wreathedSetting_N (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) :
    (wreathedSetting n S e p f).N = involutionCentralizer n S e :=
  rfl

omit [Finite G] in
theorem wreathedSetting_ON (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) :
    (wreathedSetting n S e p f).ON = ambientOddCore (involutionCentralizer n S e) :=
  rfl

theorem exists_original_sylow_of_isSylowOf (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {ell : ℕ} [Fact ell.Prime] {Rr : Subgroup G}
    (h : IsSylowOf ell Rr (ambientOddCore (involutionCentralizer n S e))) :
    ∃ P : Sylow ell (centralizerOddCore n S e),
      ambientSylow (involutionCentralizer n S e) P = Rr := by
  set N := involutionCentralizer n S e
  have hle : Rr ≤ N := h.le.trans (ambientOddCore_le N)
  have hRr : (Rr.subgroupOf N).map N.subtype = Rr := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hle]
  rw [← hRr] at h
  obtain ⟨Q, hQ⟩ := (isSylowOf_map_subtype_iff N).mp h
  refine ⟨Q, ?_⟩
  change ((Q : Subgroup (CFSG.oddCore N)).map (CFSG.oddCore N).subtype).map N.subtype = Rr
  rw [hQ, hRr]

omit [Finite G] in
theorem card_ambientOddCore (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (ambientOddCore (involutionCentralizer n S e)) =
      Nat.card (centralizerOddCore n S e) :=
  Nat.card_congr ((CFSG.oddCore (involutionCentralizer n S e)).equivMapOfInjective
    (involutionCentralizer n S e).subtype
      (involutionCentralizer n S e).subtype_injective).toEquiv.symm

theorem original_all_prime_of_theoremBStar
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hB : (wreathedSetting n S e p f).TheoremBStar) :
    OriginalAllPrimeStationarity n S e ∧ OriginalAllPrimeCoverage n S e := by
  have hx₂T : originalX2 n S e ∈ (wreathedSetting n S e p f).T :=
    Subgroup.subset_closure (by simp [wreathedSetting])
  have hdiv' : ∀ ell : ℕ, ell ∣ Nat.card (centralizerOddCore n S e) →
      ell ∣ Nat.card (wreathedSetting n S e p f).ON := by
    intro ell hdiv
    rw [wreathedSetting_ON, card_ambientOddCore]
    exact hdiv
  constructor
  · intro ell hell hdiv
    have : Fact ell.Prime := ⟨hell⟩
    obtain ⟨⟨Rr, hRsyl, hRst⟩, -⟩ := hB ell hell (hdiv' ell hdiv)
    obtain ⟨P, hP⟩ := exists_original_sylow_of_isSylowOf n S e hRsyl
    refine ⟨P, ?_⟩
    obtain ⟨Q, hQ⟩ := hRst
    unfold OriginalStationarity
    rw [hP]
    exact ⟨Q, hQ⟩
  · intro ell hell hdiv
    have : Fact ell.Prime := ⟨hell⟩
    obtain ⟨-, hCI⟩ := hB ell hell (hdiv' ell hdiv)
    rcases hCI with ⟨Rr, hRsyl, hTnorm, hTcent⟩ | ⟨Rr, hRsyl, hTnorm, hinv⟩
    · obtain ⟨P, hP⟩ := exists_original_sylow_of_isSylowOf n S e hRsyl
      refine ⟨P, original_coverage_of_scalar hnonab n hn S e hfour hell hdiv P ?_ (Or.inl ?_)⟩
      · rw [hP]
        exact hTnorm hx₂T
      · intro a ha
        rw [hP] at ha
        have hc := Subgroup.mem_centralizer_iff.mp (hTcent hx₂T) a ha
        rw [← hc, mul_inv_cancel_right]
    · obtain ⟨P, hP⟩ := exists_original_sylow_of_isSylowOf n S e hRsyl
      refine ⟨P, original_coverage_of_scalar hnonab n hn S e hfour hell hdiv P ?_ (Or.inr ?_)⟩
      · rw [hP]
        exact hTnorm hx₂T
      · intro a ha
        rw [hP] at ha
        exact hinv a ha

end CFSG.Wreathed.OriginalAllPrime
