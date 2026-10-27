module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatStatement

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (centerQuotientAut FixedCentralizerTwoFree)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)

@[expose] def OmegaSmall (S : Type) [Group S] (m f : ℕ) : Prop :=
  m = 4 ∧ f = 1 ∧ NativeSporadic.SporadicRep S

@[expose] def OmegaOvergroup (K : Type) [Group K] (τ : MulAut K) (m f : ℕ) : Prop :=
  τ ∉ (MulAut.conj : K →* MulAut K).range ∧ Odd (Nat.card (center K)) ∧
    (LieModel (K ⧸ center K) .POmegaPlus m 2 (2 * f) ∨ OmegaSmall (K ⧸ center K) m f)

@[expose] def CatOmegaAlternating : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    (∃ n : ℕ, 5 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) →
    ∀ σ : MulAut S, orderOf σ = 2 → ∀ (t : StatedLieTag) (m f : ℕ)
      (D : Subgroup (fixedSubgroup σ)), (t = .POmegaPlus ∨ t = .POmegaMinus) →
      IsComponent D → LieModel (D ⧸ center D) t m 2 f → False

@[expose] def CatOmegaEvenInner : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    EvenLieType S → ∀ σ : MulAut S, orderOf σ = 2 → σ ∈ (MulAut.conj : S →* MulAut S).range →
    ∀ (t : StatedLieTag) (m f : ℕ) (D : Subgroup (fixedSubgroup σ)),
      (t = .POmegaPlus ∨ t = .POmegaMinus) → IsComponent D →
      LieModel (D ⧸ center D) t m 2 f → False

@[expose] def CatOmegaEvenOuterAt (m : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    EvenLieType S → ∀ σ : MulAut S, orderOf σ = 2 → σ ∉ (MulAut.conj : S →* MulAut S).range →
    ∀ (t : StatedLieTag) (f : ℕ) (D : Subgroup (fixedSubgroup σ)),
      (t = .POmegaPlus ∨ t = .POmegaMinus) → IsComponent D →
      LieModel (D ⧸ center D) t m 2 f → FixedCentralizerTwoFree σ D →
        LieModel S .POmegaPlus m 2 (2 * f)

@[expose] def CatOmegaOddLieAt (m : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    OddLieType S → ∀ σ : MulAut S, orderOf σ = 2 →
    ∀ (t : StatedLieTag) (f : ℕ) (D : Subgroup (fixedSubgroup σ)),
      (t = .POmegaPlus ∨ t = .POmegaMinus) → IsComponent D →
      LieModel (D ⧸ center D) t m 2 f → False

@[expose] def CatOmegaSporadicAt (m : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    NativeSporadic.SporadicRep S → ∀ σ : MulAut S, orderOf σ = 2 →
    ∀ (t : StatedLieTag) (f : ℕ) (D : Subgroup (fixedSubgroup σ)),
      (t = .POmegaPlus ∨ t = .POmegaMinus) → IsComponent D →
      LieModel (D ⧸ center D) t m 2 f →
      ((σ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall σ D ∧
          Odd (Nat.card (center D))) ∨ FixedCentralizerTwoFree σ D) → m = 4 ∧ f = 1

@[expose] def CatOmegaCovers : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → ∀ τ : MulAut K, orderOf τ = 2 →
    ∀ (t : StatedLieTag) (m f : ℕ) (D : Subgroup (fixedSubgroup τ)), IsComponent D →
      LieModel (D ⧸ center D) t m 2 f →
      orderOf (centerQuotientAut τ) = 2 ∧
        (τ ∈ (MulAut.conj : K →* MulAut K).range →
          centerQuotientAut τ ∈ (MulAut.conj : (K ⧸ center K) →* MulAut (K ⧸ center K)).range) ∧
        ∃ D' : Subgroup (fixedSubgroup (centerQuotientAut τ)), IsComponent D' ∧
          LieModel (D' ⧸ center D') t m 2 f ∧
          (Odd (Nat.card (center D)) → Odd (Nat.card (center D'))) ∧
          (FixedCentralizerTwoFree τ D →
            Odd (Nat.card (center K)) ∧ FixedCentralizerTwoFree (centerQuotientAut τ) D') ∧
          (τ ∈ (MulAut.conj : K →* MulAut K).range → FixedCentralizerTwoSmall τ D →
            Odd (Nat.card (center K)) ∧ FixedCentralizerTwoSmall (centerQuotientAut τ) D')

@[expose] def OmegaCatalogueClausesAt (m : ℕ) : Prop :=
  CatOmegaAlternating ∧ CatOmegaEvenInner ∧ CatOmegaEvenOuterAt m ∧ CatOmegaOddLieAt m ∧
    CatOmegaSporadicAt m ∧ CatOmegaCovers

@[expose] def OmegaOvergroupCatalogue : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → Catalog (K ⧸ center K) →
    ∀ τ : MulAut K, orderOf τ = 2 → ∀ (t : StatedLieTag) (m f : ℕ)
      (D : Subgroup (fixedSubgroup τ)), (t = .POmegaPlus ∨ t = .POmegaMinus) →
      IsComponent D → LieModel (D ⧸ center D) t m 2 f → FixedCentralizerTwoFree τ D →
        OmegaOvergroup K τ m f

set_option linter.unusedVariables false in
theorem statedLieAdmissible_of_lieModel_POmega {X : Type} [Group X] {t : StatedLieTag}
    {m p f : ℕ} (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (h : LieModel X t m p f) :
    StatedLieAdmissible t m p f :=
  CFSG.Blueprint.LieModel.admissible h

theorem four_le_of_lieModel_POmega {X : Type} [Group X] {t : StatedLieTag} {m p f : ℕ}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (h : LieModel X t m p f) : 4 ≤ m := by
  have hadm := statedLieAdmissible_of_lieModel_POmega ht h
  rcases ht with rfl | rfl <;> exact hadm.2.2

theorem one_le_of_lieModel_POmega {X : Type} [Group X] {t : StatedLieTag} {m p f : ℕ}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (h : LieModel X t m p f) : 1 ≤ f :=
  (statedLieAdmissible_of_lieModel_POmega ht h).2.1

theorem not_omegaSmall_of_ne {S : Type} [Group S] {m f : ℕ} (hmf : (m, f) ≠ (4, 1)) :
    ¬ OmegaSmall S m f := fun h => hmf (by rw [h.1, h.2.1])

theorem omega_simple_of_clauses {m : ℕ} (h : OmegaCatalogueClausesAt m) {S : Type} [Group S]
    [Finite S] (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) (hcat : Catalog S)
    {σ : MulAut S} (hσ : orderOf σ = 2) {t : StatedLieTag} {f : ℕ}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) (hDm : LieModel (D ⧸ center D) t m 2 f) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range → FixedCentralizerTwoSmall σ D →
        Odd (Nat.card (center D)) → OmegaSmall S m f) ∧
      (FixedCentralizerTwoFree σ D →
        σ ∉ (MulAut.conj : S →* MulAut S).range ∧
          (LieModel S .POmegaPlus m 2 (2 * f) ∨ OmegaSmall S m f)) := by
  obtain ⟨hAlt, hEI, hEO, hOdd, hSpor, -⟩ := h
  have hcases := (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat
  refine ⟨fun hin hsmall hZD => ?_, fun hodd => ?_⟩
  · rcases hcases with hA | ho | he | hsp
    · exact (hAlt S hS hna hA σ hσ t m f D ht hD hDm).elim
    · exact (hOdd S hS hna ho σ hσ t f D ht hD hDm).elim
    · exact (hEI S hS hna he σ hσ hin t m f D ht hD hDm).elim
    · obtain ⟨h4, h1⟩ := hSpor S hS hna hsp σ hσ t f D ht hD hDm (.inl ⟨hin, hsmall, hZD⟩)
      exact ⟨h4, h1, hsp⟩
  · have hout := LinearPilot.not_mem_range_conj_of_twoFree hna hσ hodd
    refine ⟨hout, ?_⟩
    rcases hcases with hA | ho | he | hsp
    · exact (hAlt S hS hna hA σ hσ t m f D ht hD hDm).elim
    · exact (hOdd S hS hna ho σ hσ t f D ht hD hDm).elim
    · exact .inl (hEO S hS hna he σ hσ hout t f D ht hD hDm hodd)
    · obtain ⟨h4, h1⟩ := hSpor S hS hna hsp σ hσ t f D ht hD hDm (.inr hodd)
      exact .inr ⟨h4, h1, hsp⟩

theorem omega_inner_small_of_clauses {m : ℕ} (h : OmegaCatalogueClausesAt m) {K : Type}
    [Group K] [Finite K] (hK : IsQuasisimple K) (hcat : Catalog (K ⧸ center K)) (τ : MulAut K)
    (hτ : orderOf τ = 2) {t : StatedLieTag} {f : ℕ} (ht : t = .POmegaPlus ∨ t = .POmegaMinus)
    (D : Subgroup (fixedSubgroup τ)) (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) t m 2 f) (hZD : Odd (Nat.card (center D)))
    (hin : τ ∈ (MulAut.conj : K →* MulAut K).range) (hsmall : FixedCentralizerTwoSmall τ D) :
    OmegaSmall (K ⧸ center K) m f := by
  obtain ⟨hτ', hinn, D', hD', hD'm, hZD', -, hsmall'⟩ := h.2.2.2.2.2 K hK τ hτ t m f D hD hDm
  obtain ⟨-, hs'⟩ := hsmall' hin hsmall
  exact (omega_simple_of_clauses h hK.2.1 hK.2.2 hcat hτ' ht hD' hD'm).1 (hinn hin) hs' (hZD' hZD)

theorem omega_not_inner_of_clauses {m : ℕ} (h : OmegaCatalogueClausesAt m) {K : Type} [Group K]
    [Finite K] (hK : IsQuasisimple K) (hcat : Catalog (K ⧸ center K)) (τ : MulAut K)
    (hτ : orderOf τ = 2) {t : StatedLieTag} {f : ℕ} (ht : t = .POmegaPlus ∨ t = .POmegaMinus)
    (hmf : (m, f) ≠ (4, 1)) (D : Subgroup (fixedSubgroup τ)) (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) t m 2 f) (hZD : Odd (Nat.card (center D)))
    (hsmall : FixedCentralizerTwoSmall τ D) : τ ∉ (MulAut.conj : K →* MulAut K).range :=
  fun hin => not_omegaSmall_of_ne hmf
    (omega_inner_small_of_clauses h hK hcat τ hτ ht D hD hDm hZD hin hsmall)

theorem omega_overgroup_catalogue {m : ℕ} (h : OmegaCatalogueClausesAt m) {K : Type} [Group K]
    [Finite K] (hK : IsQuasisimple K) (hcat : Catalog (K ⧸ center K)) (τ : MulAut K)
    (hτ : orderOf τ = 2) {t : StatedLieTag} {f : ℕ} (ht : t = .POmegaPlus ∨ t = .POmegaMinus)
    (D : Subgroup (fixedSubgroup τ)) (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) t m 2 f) (hodd : FixedCentralizerTwoFree τ D) :
    OmegaOvergroup K τ m f := by
  obtain ⟨hτ', hinn, D', hD', hD'm, -, hodd', -⟩ := h.2.2.2.2.2 K hK τ hτ t m f D hD hDm
  obtain ⟨hZ, hodd2⟩ := hodd' hodd
  obtain ⟨hout, hlist⟩ := (omega_simple_of_clauses h hK.2.1 hK.2.2 hcat hτ' ht hD' hD'm).2 hodd2
  exact ⟨fun hin => hout (hinn hin), hZ, hlist⟩

theorem omega_overgroup_catalogue_of_ne {m : ℕ} (h : OmegaCatalogueClausesAt m) {K : Type}
    [Group K] [Finite K] (hK : IsQuasisimple K) (hcat : Catalog (K ⧸ center K)) (τ : MulAut K)
    (hτ : orderOf τ = 2) {t : StatedLieTag} {f : ℕ} (ht : t = .POmegaPlus ∨ t = .POmegaMinus)
    (hmf : (m, f) ≠ (4, 1)) (D : Subgroup (fixedSubgroup τ)) (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) t m 2 f) (hodd : FixedCentralizerTwoFree τ D) :
    τ ∉ (MulAut.conj : K →* MulAut K).range ∧ Odd (Nat.card (center K)) ∧
      LieModel (K ⧸ center K) .POmegaPlus m 2 (2 * f) := by
  obtain ⟨hout, hZ, hlist⟩ := omega_overgroup_catalogue h hK hcat τ hτ ht D hD hDm hodd
  exact ⟨hout, hZ, hlist.resolve_right (not_omegaSmall_of_ne hmf)⟩

theorem omegaOvergroupCatalogue_of_clauses (h : ∀ m : ℕ, 4 ≤ m → OmegaCatalogueClausesAt m) :
    OmegaOvergroupCatalogue := by
  intro K _ _ hK hcat τ hτ t m f D ht hD hDm hodd
  exact omega_overgroup_catalogue (h m (four_le_of_lieModel_POmega ht hDm)) hK hcat τ hτ ht D
    hD hDm hodd

end CFSG.SeitzReduction.OmegaPilot
