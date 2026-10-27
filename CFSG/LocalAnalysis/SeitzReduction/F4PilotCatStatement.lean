module

public import CFSG.Foundations.Basic
public import CFSG.Milestones.CT_catalog_nonabelian_type_partition
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientAlgebra

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem map_center_mulAut {K : Type*} [Group K] (τ : MulAut K) :
    (center K).map τ.toMonoidHom = center K :=
  characteristic_iff_map_eq.mp inferInstance τ

@[expose] def centerQuotientAut {K : Type*} [Group K] (τ : MulAut K) : MulAut (K ⧸ center K) :=
  ComponentClassification.CatalogueBFixedCentralQuotient.onQuotient (center K) τ
    (map_center_mulAut τ)

theorem centerQuotientAut_mk {K : Type*} [Group K] (τ : MulAut K) (x : K) :
    centerQuotientAut τ (QuotientGroup.mk' (center K) x) = QuotientGroup.mk' (center K) (τ x) :=
  ComponentClassification.CatalogueBFixedCentralQuotient.onQuotient_mk _ _ _ x

@[expose] def FixedCentralizerTwoFree {S : Type} [Group S] (σ : MulAut S)
    (D : Subgroup (fixedSubgroup σ)) : Prop :=
  ∀ U : Subgroup S, IsPGroup 2 U →
    U ≤ centralizer ((D.map (fixedSubgroup σ).subtype : Subgroup S) : Set S) →
    U ≤ fixedSubgroup σ → U = ⊥

@[expose] def Sp6OvergroupType (S : Type) [Group S] (f : ℕ) : Prop :=
  LieModel S .PSp 3 2 (2 * f) ∨ LieModel S .PSL 6 2 f ∨ LieModel S .PSU 6 2 f ∨
    LieModel S .PSL 7 2 f ∨ LieModel S .PSU 7 2 f ∨ LieModel S .POmegaPlus 4 2 f ∨
    LieModel S .POmegaMinus 4 2 f

@[expose] def Sp6Overgroup (K : Type) [Group K] (τ : MulAut K) (f : ℕ) : Prop :=
  τ ∉ (MulAut.conj : K →* MulAut K).range ∧ Odd (Nat.card (center K)) ∧
    Sp6OvergroupType (K ⧸ center K) f ∧
    LieModel (fixedSubgroup (centerQuotientAut τ)) .PSp 3 2 f

@[expose] def CatSp6Alternating : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    (∃ n : ℕ, 5 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) →
    ∀ σ : MulAut S, orderOf σ = 2 → ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)),
      IsComponent D → LieModel D .PSp 3 2 f → False

@[expose] def CatSp6EvenInner : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    EvenLieType S → ∀ σ : MulAut S, orderOf σ = 2 → σ ∈ (MulAut.conj : S →* MulAut S).range →
    ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)), IsComponent D → LieModel D .PSp 3 2 f → False

@[expose] def CatSp6EvenOuter : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    EvenLieType S → ∀ σ : MulAut S, orderOf σ = 2 → σ ∉ (MulAut.conj : S →* MulAut S).range →
    ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)), IsComponent D → LieModel D .PSp 3 2 f →
      FixedCentralizerTwoFree σ D →
        Sp6OvergroupType S f ∧ LieModel (fixedSubgroup σ) .PSp 3 2 f

@[expose] def CatSp6OddLie : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    OddLieType S → ∀ σ : MulAut S, orderOf σ = 2 → ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)),
      IsComponent D → LieModel D .PSp 3 2 f → False

@[expose] def CatSp6Sporadic : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    NativeSporadic.SporadicRep S → ∀ σ : MulAut S, orderOf σ = 2 →
    ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)), IsComponent D → LieModel D .PSp 3 2 f →
      (σ ∈ (MulAut.conj : S →* MulAut S).range ∨ FixedCentralizerTwoFree σ D) → False

@[expose] def CatSp6Covers : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → ∀ τ : MulAut K, orderOf τ = 2 →
    ∀ (f : ℕ) (D : Subgroup (fixedSubgroup τ)), IsComponent D → LieModel D .PSp 3 2 f →
      orderOf (centerQuotientAut τ) = 2 ∧
        (τ ∈ (MulAut.conj : K →* MulAut K).range →
          centerQuotientAut τ ∈ (MulAut.conj : (K ⧸ center K) →* MulAut (K ⧸ center K)).range) ∧
        ∃ D' : Subgroup (fixedSubgroup (centerQuotientAut τ)), IsComponent D' ∧
          LieModel D' .PSp 3 2 f ∧
          (FixedCentralizerTwoFree τ D →
            Odd (Nat.card (center K)) ∧ FixedCentralizerTwoFree (centerQuotientAut τ) D')

@[expose] def Sp6CatalogueClauses : Prop :=
  CatSp6Alternating ∧ CatSp6EvenInner ∧ CatSp6EvenOuter ∧ CatSp6OddLie ∧ CatSp6Sporadic ∧
    CatSp6Covers

theorem sp6_simple_of_clauses (h : Sp6CatalogueClauses) {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) (hcat : Catalog S)
    {σ : MulAut S} (hσ : orderOf σ = 2) {f : ℕ} {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) (hD6 : LieModel D .PSp 3 2 f) :
    σ ∉ (MulAut.conj : S →* MulAut S).range ∧
      (FixedCentralizerTwoFree σ D →
        Sp6OvergroupType S f ∧ LieModel (fixedSubgroup σ) .PSp 3 2 f) := by
  obtain ⟨hAlt, hEI, hEO, hOdd, hSpor, -⟩ := h
  have hcases := (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat
  have hinner : σ ∉ (MulAut.conj : S →* MulAut S).range := by
    intro hin
    rcases hcases with hA | ho | he | hsp
    · exact hAlt S hS hna hA σ hσ f D hD hD6
    · exact hOdd S hS hna ho σ hσ f D hD hD6
    · exact hEI S hS hna he σ hσ hin f D hD hD6
    · exact hSpor S hS hna hsp σ hσ f D hD hD6 (.inl hin)
  refine ⟨hinner, fun hodd => ?_⟩
  rcases hcases with hA | ho | he | hsp
  · exact (hAlt S hS hna hA σ hσ f D hD hD6).elim
  · exact (hOdd S hS hna ho σ hσ f D hD hD6).elim
  · exact hEO S hS hna he σ hσ hinner f D hD hD6 hodd
  · exact (hSpor S hS hna hsp σ hσ f D hD hD6 (.inr hodd)).elim

theorem sp6_not_inner_of_clauses (h : Sp6CatalogueClauses) {K : Type} [Group K] [Finite K]
    (hK : IsQuasisimple K) (hcat : Catalog (K ⧸ center K)) (τ : MulAut K) (hτ : orderOf τ = 2)
    {f : ℕ} (D : Subgroup (fixedSubgroup τ)) (hD : IsComponent D)
    (hD6 : LieModel D .PSp 3 2 f) : τ ∉ (MulAut.conj : K →* MulAut K).range := by
  obtain ⟨hτ', hinn, D', hD', hD'6, -⟩ := h.2.2.2.2.2 K hK τ hτ f D hD hD6
  exact fun hin => (sp6_simple_of_clauses h hK.2.1 hK.2.2 hcat hτ' hD' hD'6).1 (hinn hin)

theorem sp6_overgroup_catalogue (h : Sp6CatalogueClauses) {K : Type} [Group K] [Finite K]
    (hK : IsQuasisimple K) (hcat : Catalog (K ⧸ center K)) (τ : MulAut K) (hτ : orderOf τ = 2)
    {f : ℕ} (D : Subgroup (fixedSubgroup τ)) (hD : IsComponent D)
    (hD6 : LieModel D .PSp 3 2 f) (hodd : FixedCentralizerTwoFree τ D) :
    Sp6Overgroup K τ f := by
  obtain ⟨hτ', hinn, D', hD', hD'6, hodd'⟩ := h.2.2.2.2.2 K hK τ hτ f D hD hD6
  obtain ⟨hout, hlist⟩ := sp6_simple_of_clauses h hK.2.1 hK.2.2 hcat hτ' hD' hD'6
  obtain ⟨hZ, hodd2⟩ := hodd' hodd
  obtain ⟨htype, hfix⟩ := hlist hodd2
  exact ⟨fun hin => hout (hinn hin), hZ, htype, hfix⟩

end CFSG.SeitzReduction.F4Pilot
