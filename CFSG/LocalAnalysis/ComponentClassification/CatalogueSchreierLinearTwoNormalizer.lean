module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoCoordinateQuotients

public section

namespace CFSG.ComponentClassification.CatalogueSchreierLinearTwo

noncomputable section

open CFSG.GorensteinWalter OuterAutomorphisms

universe u

theorem translation_mem_coordinateG (K : Type u) [Field K] (b : K) :
    translation K b ∈ coordinateG K :=
  Subgroup.subset_closure (Or.inl ⟨b, rfl⟩)

theorem inversion_mem_coordinateG (K : Type u) [Field K] :
    inversion K ∈ coordinateG K :=
  Subgroup.subset_closure (Or.inr rfl)

theorem coordinateG_centralizer_eq_bot (K : Type u) [Field K] :
    Subgroup.centralizer (coordinateG K : Set (Equiv.Perm (Omega K))) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro c hc
  have hcomm (g : Equiv.Perm (Omega K)) (hg : g ∈ coordinateG K) (x : Omega K) :
      g (c x) = c (g x) :=
    congrArg (fun a : Equiv.Perm (Omega K) => a x)
      (Subgroup.mem_centralizer_iff.mp hc g hg)
  have hinf : c none = none := by
    cases h : c none with
    | none => rfl
    | some a =>
      have ht := hcomm (translation K 1) (translation_mem_coordinateG K 1) none
      simp only [h, translation_some, translation_none] at ht
      have h10 : (1 : K) = 0 :=
        add_left_cancel ((Option.some.inj ht).trans (add_zero a).symm)
      exact (one_ne_zero h10).elim
  have hzero : c (some 0) = some 0 := by
    have hi := hcomm (inversion K) (inversion_mem_coordinateG K) none
    simpa only [hinf, inversion_none] using hi.symm
  apply Equiv.ext
  intro x
  cases x with
  | none => exact hinf
  | some a =>
    have ht := hcomm (translation K a) (translation_mem_coordinateG K a) (some 0)
    simpa only [hzero, translation_some, zero_add, Equiv.Perm.one_apply] using ht.symm

theorem coordinateNormalizerAction_injective (K : Type u) [Field K] :
    Function.Injective (coordinateG K).normalizerMonoidHom := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [Subgroup.normalizerMonoidHom_ker, coordinateG_centralizer_eq_bot,
    Subgroup.bot_subgroupOf]

@[expose] def semilinearEquivCoordinateAut (K : Type u) [Field K] [Finite K] :
    PGammaL2 K ≃* MulAut (coordinateG K) :=
  (semilinearEquivAut K).trans (MulAut.congr (pslEquivCoordinateG K))

theorem coordinateNormalizer_eq_E (K : Type u) [Field K] [Finite K] :
    Subgroup.normalizer (coordinateG K : Set (Equiv.Perm (Omega K))) = coordinateE K := by
  apply (Subgroup.eq_of_le_of_card_ge (coordinateE_le_normalizer_G K) _).symm
  calc
    Nat.card (Subgroup.normalizer (coordinateG K : Set (Equiv.Perm (Omega K)))) ≤
        Nat.card (MulAut (coordinateG K)) :=
      Nat.card_le_card_of_injective _ (coordinateNormalizerAction_injective K)
    _ = Nat.card (PGammaL2 K) :=
      (Nat.card_congr (semilinearEquivCoordinateAut K).toEquiv).symm
    _ = Nat.card (coordinateE K) :=
      Nat.card_congr (semilinearEquivCoordinateE K).toEquiv

theorem coordinateNormalizer_decomposition (K : Type u) [Field K] [Finite K]
    (pi : Equiv.Perm (Omega K))
    (hpi : pi ∈ Subgroup.normalizer (coordinateG K : Set (Equiv.Perm (Omega K)))) :
    ∃ d : coordinateD K, ∃ sigma : K ≃+* K,
      pi = (d : Equiv.Perm (Omega K)) * fieldExtension K sigma := by
  rw [coordinateNormalizer_eq_E, ← coordinateSemilinearAction_range_eq_E] at hpi
  obtain ⟨g, rfl⟩ := hpi
  refine ⟨pglEquivCoordinateD K g.left, g.right, ?_⟩
  change coordinateSemilinearAction K g =
    coordinatePGLAction K g.left * fieldExtension K g.right
  calc
    coordinateSemilinearAction K g =
        coordinateSemilinearAction K
          (SemidirectProduct.inl g.left * SemidirectProduct.inr g.right) :=
      congrArg (coordinateSemilinearAction K)
        (SemidirectProduct.inl_left_mul_inr_right g).symm
    _ = _ := by rw [map_mul, coordinateSemilinearAction_inl, coordinateSemilinearAction_inr]

@[expose] def coordinateConjugation (K : Type u) [Field K] [Finite K] :
    coordinateE K →* MulAut (coordinateG K) :=
  (coordinateG K).normalizerMonoidHom.comp
    (Subgroup.inclusion (coordinateE_le_normalizer_G K))

theorem coordinateConjugation_apply_coe (K : Type u) [Field K] [Finite K]
    (e : coordinateE K) (g : coordinateG K) :
    ((coordinateConjugation K e g : coordinateG K) : Equiv.Perm (Omega K)) =
      (e : Equiv.Perm (Omega K)) * (g : Equiv.Perm (Omega K)) *
        (e : Equiv.Perm (Omega K))⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _

theorem coordinateConjugation_injective (K : Type u) [Field K] [Finite K] :
    Function.Injective (coordinateConjugation K) :=
  (coordinateNormalizerAction_injective K).comp (Subgroup.inclusion_injective _)

theorem coordinateConjugation_surjective (K : Type u) [Field K] [Finite K] :
    Function.Surjective (coordinateConjugation K) := by
  apply ((Nat.bijective_iff_injective_and_card (coordinateConjugation K)).mpr
    ⟨coordinateConjugation_injective K, ?_⟩).surjective
  exact (Nat.card_congr (semilinearEquivCoordinateE K).toEquiv).symm.trans
    (Nat.card_congr (semilinearEquivCoordinateAut K).toEquiv)

theorem coordinateNormalizerAction_surjective (K : Type u) [Field K] [Finite K] :
    Function.Surjective (coordinateG K).normalizerMonoidHom := by
  intro alpha
  obtain ⟨e, he⟩ := coordinateConjugation_surjective K alpha
  exact ⟨Subgroup.inclusion (coordinateE_le_normalizer_G K) e, he⟩

@[expose] def coordinateConjugationEquiv (K : Type u) [Field K] [Finite K] :
    coordinateE K ≃* MulAut (coordinateG K) :=
  MulEquiv.ofBijective (coordinateConjugation K)
    ⟨coordinateConjugation_injective K, coordinateConjugation_surjective K⟩

theorem coordinateConjugation_on_G (K : Type u) [Field K] [Finite K] (g : coordinateG K) :
    coordinateConjugation K
      ⟨g, ((coordinateG_le_D K).trans (coordinateD_le_E K)) g.property⟩ = MulAut.conj g := by
  apply MulEquiv.ext
  intro h
  apply Subtype.ext
  exact coordinateConjugation_apply_coe K _ h

theorem coordinateConjugation_G_image (K : Type u) [Field K] [Finite K] :
    ((coordinateG K).subgroupOf (coordinateE K)).map (coordinateConjugation K) =
      inner (coordinateG K) := by
  ext alpha
  constructor
  · rintro ⟨e, he, rfl⟩
    let g : coordinateG K := ⟨e, he⟩
    exact ⟨g, (coordinateConjugation_on_G K g).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨⟨g, ((coordinateG_le_D K).trans (coordinateD_le_E K)) g.property⟩,
      g.property, coordinateConjugation_on_G K g⟩

end

end CFSG.ComponentClassification.CatalogueSchreierLinearTwo
