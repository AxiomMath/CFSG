module

public import CFSG.LocalAnalysis.AGLEmbedding.KFacts
public import CFSG.LocalAnalysis.ComponentClassification.Helpers

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def KFactBetaConclusion (K : Type) [Group K] [Finite K] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K, (T : Subgroup K) ≠ ⊥ →
    (IsCyclic (T : Subgroup K) ∨ GLBCore p 1 (T : Subgroup K) ≠ ⊤) →
    Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 ∨ RankOneLieAutFacts p K

@[expose] def KFactBetaAlt : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (n : ℕ), 5 ≤ n → n ≠ 6 →
    Nonempty (K ≃* alternatingGroup (Fin n)) → KFactBetaConclusion K

@[expose] def KFactBetaA6 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* alternatingGroup (Fin 6)) →
    KFactBetaConclusion K

@[expose] def KFactBetaLie : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    KFactBetaConclusion K

@[expose] def KFactBetaSpor : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ s : TauCeti.SporadicName, Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    KFactBetaConclusion K

theorem not_nonempty_mulEquiv_zmod {K : Type} [Group K] (hnonab : ∃ a b : K, a * b ≠ b * a)
    {p : ℕ} : ¬ Nonempty (K ≃* Multiplicative (ZMod p)) := by
  rintro ⟨e⟩
  obtain ⟨a, b, hab⟩ := hnonab
  exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))

theorem kFactBeta_of_families (halt : KFactBetaAlt) (h6 : KFactBetaA6) (hlie : KFactBetaLie)
    (hspor : KFactBetaSpor) : KFactBeta := by
  intro K _ _ hsimple hnonab hcat
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic p hp => exact (not_nonempty_mulEquiv_zmod hnonab ⟨e⟩).elim
  | alternating n hn =>
    by_cases h : n = 6
    · subst h
      exact h6 K ⟨e⟩
    · exact halt K n hn h ⟨e⟩
  | lie d => exact hlie K hsimple hnonab d ⟨e⟩
  | sporadic s => exact hspor K hsimple hnonab s ⟨e⟩

@[expose] def KFactAlphaConclusion (K : Type) [Group K] [Finite K] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → Subgroup.center K ≠ ⊥ → IsPGroup p (Subgroup.center K) →
    IsCyclic (Subgroup.center K) → ∀ T : Sylow p K,
      (KGenThree p K ∧ (3 ≤ Open.pRank p (⊤ : Subgroup K) ∨ KOutNormalSylow p K)) ∨
      Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 ∨
      (GLBCore p 3 (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank p (⊤ : Subgroup K)) ∨
      (KOutTwoGroup K ∧
        ((∃ A : Subgroup K, A ≤ (T : Subgroup K) ⊓ Subgroup.centralizer (T : Set K) ∧
            IsElemAbelian p A ∧ Nat.card A = p ^ 2) ∨
          ((∀ t ∈ (T : Subgroup K), t ^ p = 1) ∧ Open.pRank p (T : Subgroup K) ≤ 3) ∨
          (∃ A : Subgroup K, A ≤ (T : Subgroup K) ∧
            (T : Subgroup K) ≤ Subgroup.normalizer (A : Set K) ∧ IsElemAbelian p A ∧
            p ^ (p + 1) ≤ Nat.card A)))

@[expose] def KFactAlphaAlt : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K → ∀ n : ℕ, 5 ≤ n →
    Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) → KFactAlphaConclusion K

@[expose] def KFactAlphaLie : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K → ∀ d : TauCeti.ValidLieTypeIndex,
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) → KFactAlphaConclusion K

@[expose] def KFactAlphaSpor : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K → ∀ s : TauCeti.SporadicName,
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    KFactAlphaConclusion K

theorem kFactAlpha_of_families (halt : KFactAlphaAlt) (hlie : KFactAlphaLie)
    (hspor : KFactAlphaSpor) : KFactAlpha := by
  intro K _ _ hK hcat
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic p hp =>
    exact (not_nonempty_mulEquiv_zmod
      (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK) ⟨e⟩).elim
  | alternating n hn => exact halt K hK n hn ⟨e⟩
  | lie d => exact hlie K hK d ⟨e⟩
  | sporadic s => exact hspor K hK s ⟨e⟩

end CFSG.AGLEmbedding
