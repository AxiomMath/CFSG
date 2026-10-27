module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatStatement
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (centerQuotientAut FixedCentralizerTwoFree)

@[expose] def FixedCentralizerTwoSmall {S : Type} [Group S] (σ : MulAut S)
    (D : Subgroup (fixedSubgroup σ)) : Prop :=
  ∀ U : Subgroup S, IsPGroup 2 U →
    U ≤ centralizer ((D.map (fixedSubgroup σ).subtype : Subgroup S) : Set S) →
    U ≤ fixedSubgroup σ → Nat.card U ≤ 2

@[expose] def SLmSmall (S : Type) [Group S] (m f : ℕ) : Prop :=
  f = 1 ∧ ((m = 4 ∧ ∃ n : ℕ, 5 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∨
    (m = 3 ∧ OddLieType S) ∨ ((m = 3 ∨ m = 4) ∧ NativeSporadic.SporadicRep S))

@[expose] def SLmOvergroup (K : Type) [Group K] (τ : MulAut K) (m f : ℕ) : Prop :=
  τ ∉ (MulAut.conj : K →* MulAut K).range ∧ Odd (Nat.card (center K)) ∧
    (LieModel (K ⧸ center K) .PSL m 2 (2 * f) ∨ SLmSmall (K ⧸ center K) m f)

@[expose] def CatSLmAlternating : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    (∃ n : ℕ, 5 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) →
    ∀ σ : MulAut S, orderOf σ = 2 → ∀ (m f : ℕ) (D : Subgroup (fixedSubgroup σ)), 3 ≤ m →
      IsComponent D → LieModel (D ⧸ center D) .PSL m 2 f → m = 4 ∧ f = 1

@[expose] def CatSLmEvenInner : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    EvenLieType S → ∀ σ : MulAut S, orderOf σ = 2 → σ ∈ (MulAut.conj : S →* MulAut S).range →
    ∀ (m f : ℕ) (D : Subgroup (fixedSubgroup σ)), IsComponent D →
      LieModel (D ⧸ center D) .PSL m 2 f → False

@[expose] def CatSLmEvenOuterAt (m : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    EvenLieType S → ∀ σ : MulAut S, orderOf σ = 2 → σ ∉ (MulAut.conj : S →* MulAut S).range →
    ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)), IsComponent D →
      LieModel (D ⧸ center D) .PSL m 2 f → FixedCentralizerTwoFree σ D →
        LieModel S .PSL m 2 (2 * f)

@[expose] def CatSLmEvenOuter : Prop :=
  ∀ m : ℕ, 3 ≤ m → CatSLmEvenOuterAt m

@[expose] def CatSLmOddLieAt (m : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    OddLieType S → ∀ σ : MulAut S, orderOf σ = 2 →
    ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)), IsComponent D →
      LieModel (D ⧸ center D) .PSL m 2 f → m = 3 ∧ f = 1

@[expose] def CatSLmOddLie : Prop :=
  ∀ m : ℕ, 3 ≤ m → CatSLmOddLieAt m

@[expose] def CatSLmSporadicAt (m : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    NativeSporadic.SporadicRep S → ∀ σ : MulAut S, orderOf σ = 2 →
    ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)), IsComponent D →
      LieModel (D ⧸ center D) .PSL m 2 f →
      ((σ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall σ D) ∨
        FixedCentralizerTwoFree σ D) → f = 1 ∧ (m = 3 ∨ m = 4)

@[expose] def CatSLmSporadic : Prop :=
  ∀ m : ℕ, 3 ≤ m → CatSLmSporadicAt m

@[expose] def CatSLmCovers : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → ∀ τ : MulAut K, orderOf τ = 2 →
    ∀ (m f : ℕ) (D : Subgroup (fixedSubgroup τ)), IsComponent D →
      LieModel (D ⧸ center D) .PSL m 2 f →
      orderOf (centerQuotientAut τ) = 2 ∧
        (τ ∈ (MulAut.conj : K →* MulAut K).range →
          centerQuotientAut τ ∈ (MulAut.conj : (K ⧸ center K) →* MulAut (K ⧸ center K)).range) ∧
        ∃ D' : Subgroup (fixedSubgroup (centerQuotientAut τ)), IsComponent D' ∧
          LieModel (D' ⧸ center D') .PSL m 2 f ∧
          (FixedCentralizerTwoFree τ D →
            Odd (Nat.card (center K)) ∧ FixedCentralizerTwoFree (centerQuotientAut τ) D') ∧
          (τ ∈ (MulAut.conj : K →* MulAut K).range → FixedCentralizerTwoSmall τ D →
            Odd (Nat.card (center K)) ∧ FixedCentralizerTwoSmall (centerQuotientAut τ) D')

@[expose] def SLmCatalogueClausesAt (m : ℕ) : Prop :=
  CatSLmAlternating ∧ CatSLmEvenInner ∧ CatSLmEvenOuterAt m ∧ CatSLmOddLieAt m ∧
    CatSLmSporadicAt m ∧ CatSLmCovers

@[expose] def SLmCatalogueClauses : Prop :=
  CatSLmAlternating ∧ CatSLmEvenInner ∧ CatSLmEvenOuter ∧ CatSLmOddLie ∧ CatSLmSporadic ∧
    CatSLmCovers

theorem slmCatalogueClausesAt_of_clauses (h : SLmCatalogueClauses) {m : ℕ} (hm : 3 ≤ m) :
    SLmCatalogueClausesAt m :=
  ⟨h.1, h.2.1, h.2.2.1 m hm, h.2.2.2.1 m hm, h.2.2.2.2.1 m hm, h.2.2.2.2.2⟩

@[expose] def SLmOvergroupCatalogue : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → Catalog (K ⧸ center K) →
    ∀ τ : MulAut K, orderOf τ = 2 → ∀ (m f : ℕ) (D : Subgroup (fixedSubgroup τ)), 3 ≤ m →
      IsComponent D → LieModel (D ⧸ center D) .PSL m 2 f → FixedCentralizerTwoFree τ D →
        SLmOvergroup K τ m f

theorem not_mem_range_conj_of_twoFree {S : Type} [Group S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) {σ : MulAut S} (hσ : orderOf σ = 2)
    {D : Subgroup (fixedSubgroup σ)} (hodd : FixedCentralizerTwoFree σ D) :
    σ ∉ (MulAut.conj : S →* MulAut S).range := by
  rintro ⟨t, rfl⟩
  have ht : orderOf t = 2 := by
    rw [← orderOf_injective _ (ComponentClassification.CatLeaf.mulAut_conj_injective_of_simple hna)
      t]
    exact hσ
  have hfix : ∀ x : S, x ∈ fixedSubgroup (MulAut.conj t) → x * t = t * x := by
    intro x hx
    have hx' : t * x * t⁻¹ = x := hx
    calc x * t = t * x * t⁻¹ * t := by rw [hx']
      _ = t * x := by group
  have hU := hodd (zpowers t) (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one]))
    (by
      rw [zpowers_le, mem_centralizer_iff]
      rintro _ ⟨d, -, rfl⟩
      exact hfix _ d.2)
    (by
      rw [zpowers_le]
      change t * t * t⁻¹ = t
      group)
  have h1 : t = 1 := zpowers_eq_bot.mp hU
  rw [h1, orderOf_one] at ht
  exact absurd ht (by norm_num)

theorem slm_simple_of_clauses {m : ℕ} (h : SLmCatalogueClausesAt m) {S : Type} [Group S]
    [Finite S] (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) (hcat : Catalog S)
    {σ : MulAut S} (hσ : orderOf σ = 2) {f : ℕ} (hm : 3 ≤ m) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) (hDm : LieModel (D ⧸ center D) .PSL m 2 f) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range → FixedCentralizerTwoSmall σ D →
        SLmSmall S m f) ∧
      (FixedCentralizerTwoFree σ D →
        σ ∉ (MulAut.conj : S →* MulAut S).range ∧
          (LieModel S .PSL m 2 (2 * f) ∨ SLmSmall S m f)) := by
  obtain ⟨hAlt, hEI, hEO, hOdd, hSpor, -⟩ := h
  have hcases := (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat
  refine ⟨fun hin hsmall => ?_, fun hodd => ?_⟩
  · rcases hcases with hA | ho | he | hsp
    · obtain ⟨h4, h1⟩ := hAlt S hS hna hA σ hσ m f D hm hD hDm
      exact ⟨h1, .inl ⟨h4, hA⟩⟩
    · obtain ⟨h3, h1⟩ := hOdd S hS hna ho σ hσ f D hD hDm
      exact ⟨h1, .inr (.inl ⟨h3, ho⟩)⟩
    · exact (hEI S hS hna he σ hσ hin m f D hD hDm).elim
    · obtain ⟨h1, h34⟩ := hSpor S hS hna hsp σ hσ f D hD hDm (.inl ⟨hin, hsmall⟩)
      exact ⟨h1, .inr (.inr ⟨h34, hsp⟩)⟩
  · have hout := not_mem_range_conj_of_twoFree hna hσ hodd
    refine ⟨hout, ?_⟩
    rcases hcases with hA | ho | he | hsp
    · obtain ⟨h4, h1⟩ := hAlt S hS hna hA σ hσ m f D hm hD hDm
      exact .inr ⟨h1, .inl ⟨h4, hA⟩⟩
    · obtain ⟨h3, h1⟩ := hOdd S hS hna ho σ hσ f D hD hDm
      exact .inr ⟨h1, .inr (.inl ⟨h3, ho⟩)⟩
    · exact .inl (hEO S hS hna he σ hσ hout f D hD hDm hodd)
    · obtain ⟨h1, h34⟩ := hSpor S hS hna hsp σ hσ f D hD hDm (.inr hodd)
      exact .inr ⟨h1, .inr (.inr ⟨h34, hsp⟩)⟩

theorem slm_inner_small_of_clauses {m : ℕ} (h : SLmCatalogueClausesAt m) {K : Type} [Group K]
    [Finite K] (hK : IsQuasisimple K) (hcat : Catalog (K ⧸ center K)) (τ : MulAut K)
    (hτ : orderOf τ = 2) {f : ℕ} (hm : 3 ≤ m) (D : Subgroup (fixedSubgroup τ)) (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSL m 2 f) (hin : τ ∈ (MulAut.conj : K →* MulAut K).range)
    (hsmall : FixedCentralizerTwoSmall τ D) : SLmSmall (K ⧸ center K) m f := by
  obtain ⟨hτ', hinn, D', hD', hD'm, -, hsmall'⟩ := h.2.2.2.2.2 K hK τ hτ m f D hD hDm
  obtain ⟨-, hs'⟩ := hsmall' hin hsmall
  exact (slm_simple_of_clauses h hK.2.1 hK.2.2 hcat hτ' hm hD' hD'm).1 (hinn hin) hs'

theorem slm_not_inner_of_clauses {m : ℕ} (h : SLmCatalogueClausesAt m) {K : Type} [Group K]
    [Finite K] (hK : IsQuasisimple K) (hcat : Catalog (K ⧸ center K)) (τ : MulAut K)
    (hτ : orderOf τ = 2) {f : ℕ} (hm : 3 ≤ m) (hf : 2 ≤ f) (D : Subgroup (fixedSubgroup τ))
    (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSL m 2 f) (hsmall : FixedCentralizerTwoSmall τ D) :
    τ ∉ (MulAut.conj : K →* MulAut K).range := fun hin => by
  have h1 := (slm_inner_small_of_clauses h hK hcat τ hτ hm D hD hDm hin hsmall).1
  omega

theorem slm_overgroup_catalogue {m : ℕ} (h : SLmCatalogueClausesAt m) {K : Type} [Group K]
    [Finite K] (hK : IsQuasisimple K) (hcat : Catalog (K ⧸ center K)) (τ : MulAut K)
    (hτ : orderOf τ = 2) {f : ℕ} (hm : 3 ≤ m) (D : Subgroup (fixedSubgroup τ)) (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSL m 2 f) (hodd : FixedCentralizerTwoFree τ D) :
    SLmOvergroup K τ m f := by
  obtain ⟨hτ', hinn, D', hD', hD'm, hodd', -⟩ := h.2.2.2.2.2 K hK τ hτ m f D hD hDm
  obtain ⟨hZ, hodd2⟩ := hodd' hodd
  obtain ⟨hout, hlist⟩ := (slm_simple_of_clauses h hK.2.1 hK.2.2 hcat hτ' hm hD' hD'm).2 hodd2
  exact ⟨fun hin => hout (hinn hin), hZ, hlist⟩

theorem slmOvergroupCatalogue_of_clauses (h : SLmCatalogueClauses) : SLmOvergroupCatalogue :=
  fun _ _ _ hK hcat τ hτ _ _ D hm hD hDm hodd =>
    slm_overgroup_catalogue (slmCatalogueClausesAt_of_clauses h hm) hK hcat τ hτ hm D hD hDm
      hodd

end CFSG.SeitzReduction.LinearPilot
