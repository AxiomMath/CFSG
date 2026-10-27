module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatStatement

public section

namespace CFSG.SeitzReduction.E8Pilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (centerQuotientAut FixedCentralizerTwoFree)

@[expose] def E7Overgroup (K : Type) [Group K] (τ : MulAut K) (f : ℕ) : Prop :=
  τ ∉ (MulAut.conj : K →* MulAut K).range ∧ Odd (Nat.card (center K)) ∧
    LieModel (K ⧸ center K) .E7 0 2 (2 * f) ∧
    LieModel (fixedSubgroup (centerQuotientAut τ)) .E7 0 2 f

@[expose] def CatE7Alternating : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    (∃ n : ℕ, 5 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) →
    ∀ σ : MulAut S, orderOf σ = 2 → ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)),
      IsComponent D → LieModel D .E7 0 2 f → False

@[expose] def CatE7EvenInner : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    EvenLieType S → ∀ σ : MulAut S, orderOf σ = 2 → σ ∈ (MulAut.conj : S →* MulAut S).range →
    ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)), IsComponent D → LieModel D .E7 0 2 f → False

@[expose] def CatE7EvenOuter : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    EvenLieType S → ∀ σ : MulAut S, orderOf σ = 2 → σ ∉ (MulAut.conj : S →* MulAut S).range →
    ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)), IsComponent D → LieModel D .E7 0 2 f →
      LieModel S .E7 0 2 (2 * f) ∧ LieModel (fixedSubgroup σ) .E7 0 2 f

@[expose] def CatE7OddLie : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    OddLieType S → ∀ σ : MulAut S, orderOf σ = 2 → ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)),
      IsComponent D → LieModel D .E7 0 2 f → False

@[expose] def CatE7Sporadic : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    NativeSporadic.SporadicRep S → ∀ σ : MulAut S, orderOf σ = 2 →
    ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)), IsComponent D → LieModel D .E7 0 2 f →
      (σ ∈ (MulAut.conj : S →* MulAut S).range ∨ FixedCentralizerTwoFree σ D) → False

@[expose] def CatE7Covers : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → ∀ τ : MulAut K, orderOf τ = 2 →
    ∀ (f : ℕ) (D : Subgroup (fixedSubgroup τ)), IsComponent D → LieModel D .E7 0 2 f →
      orderOf (centerQuotientAut τ) = 2 ∧
        (τ ∈ (MulAut.conj : K →* MulAut K).range →
          centerQuotientAut τ ∈ (MulAut.conj : (K ⧸ center K) →* MulAut (K ⧸ center K)).range) ∧
        ∃ D' : Subgroup (fixedSubgroup (centerQuotientAut τ)), IsComponent D' ∧
          LieModel D' .E7 0 2 f ∧
          (FixedCentralizerTwoFree τ D →
            Odd (Nat.card (center K)) ∧ FixedCentralizerTwoFree (centerQuotientAut τ) D')

@[expose] def E7CatalogueClauses : Prop :=
  CatE7Alternating ∧ CatE7EvenInner ∧ CatE7EvenOuter ∧ CatE7OddLie ∧ CatE7Sporadic ∧
    CatE7Covers

theorem e7_simple_of_clauses (h : E7CatalogueClauses) {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) (hcat : Catalog S)
    {σ : MulAut S} (hσ : orderOf σ = 2) {f : ℕ} {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) (hD7 : LieModel D .E7 0 2 f) :
    σ ∉ (MulAut.conj : S →* MulAut S).range ∧
      (FixedCentralizerTwoFree σ D →
        LieModel S .E7 0 2 (2 * f) ∧ LieModel (fixedSubgroup σ) .E7 0 2 f) := by
  obtain ⟨hAlt, hEI, hEO, hOdd, hSpor, -⟩ := h
  have hcases := (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat
  have hinner : σ ∉ (MulAut.conj : S →* MulAut S).range := by
    intro hin
    rcases hcases with hA | ho | he | hsp
    · exact hAlt S hS hna hA σ hσ f D hD hD7
    · exact hOdd S hS hna ho σ hσ f D hD hD7
    · exact hEI S hS hna he σ hσ hin f D hD hD7
    · exact hSpor S hS hna hsp σ hσ f D hD hD7 (.inl hin)
  refine ⟨hinner, fun hodd => ?_⟩
  rcases hcases with hA | ho | he | hsp
  · exact (hAlt S hS hna hA σ hσ f D hD hD7).elim
  · exact (hOdd S hS hna ho σ hσ f D hD hD7).elim
  · exact hEO S hS hna he σ hσ hinner f D hD hD7
  · exact (hSpor S hS hna hsp σ hσ f D hD hD7 (.inr hodd)).elim

theorem e7_not_inner_of_clauses (h : E7CatalogueClauses) {K : Type} [Group K] [Finite K]
    (hK : IsQuasisimple K) (hcat : Catalog (K ⧸ center K)) (τ : MulAut K) (hτ : orderOf τ = 2)
    {f : ℕ} (D : Subgroup (fixedSubgroup τ)) (hD : IsComponent D)
    (hD7 : LieModel D .E7 0 2 f) : τ ∉ (MulAut.conj : K →* MulAut K).range := by
  obtain ⟨hτ', hinn, D', hD', hD'7, -⟩ := h.2.2.2.2.2 K hK τ hτ f D hD hD7
  exact fun hin => (e7_simple_of_clauses h hK.2.1 hK.2.2 hcat hτ' hD' hD'7).1 (hinn hin)

theorem e7_overgroup_catalogue (h : E7CatalogueClauses) {K : Type} [Group K] [Finite K]
    (hK : IsQuasisimple K) (hcat : Catalog (K ⧸ center K)) (τ : MulAut K) (hτ : orderOf τ = 2)
    {f : ℕ} (D : Subgroup (fixedSubgroup τ)) (hD : IsComponent D)
    (hD7 : LieModel D .E7 0 2 f) (hodd : FixedCentralizerTwoFree τ D) :
    E7Overgroup K τ f := by
  obtain ⟨hτ', hinn, D', hD', hD'7, hodd'⟩ := h.2.2.2.2.2 K hK τ hτ f D hD hD7
  obtain ⟨hout, hlist⟩ := e7_simple_of_clauses h hK.2.1 hK.2.2 hcat hτ' hD' hD'7
  obtain ⟨hZ, hodd2⟩ := hodd' hodd
  obtain ⟨htype, hfix⟩ := hlist hodd2
  exact ⟨fun hin => hout (hinn hin), hZ, htype, hfix⟩

end CFSG.SeitzReduction.E8Pilot
