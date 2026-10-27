module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerSplit
import CFSG.LocalAnalysis.RankThreeTheoremC.Signalizers
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_of_proper_invariant_subgroups_le {p : ℕ} (hp : p.Prime) {A K M : Subgroup G}
    (hA : IsPGroup p A) (hAK : A ≤ normalizer (K : Set G)) (hK : ¬ p ∣ Nat.card K)
    (hnot : ∀ q : ℕ, q.Prime → q ≠ p → ¬ IsPGroup q K)
    (h : ∀ K' : Subgroup G, K' < K → A ≤ normalizer (K' : Set G) → K' ≤ M) : K ≤ M := by
  have hKpos : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hHpos : Nat.card ↥(K ⊓ M) ≠ 0 := Nat.card_pos.ne'
  have hdvd : Nat.card K ∣ Nat.card ↥(K ⊓ M) := by
    refine (Nat.factorization_prime_le_iff_dvd hKpos hHpos).1 fun q hq => ?_
    refine (hq.pow_dvd_iff_le_factorization hHpos).1 ?_
    by_cases hqK : q ∣ Nat.card K
    · have hqp : q ≠ p := fun h => hK (h ▸ hqK)
      have : Fact q.Prime := ⟨hq⟩
      obtain ⟨S, hS⟩ := CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow p q
        hp hq A K hA hAK ((Nat.Prime.coprime_iff_not_dvd hp).2 hK)
      have hSK : (S : Subgroup K).map K.subtype ≤ K := map_subtype_le _
      have hScard : Nat.card ((S : Subgroup K).map K.subtype) =
          q ^ (Nat.card K).factorization q := by
        rw [Subgroup.card_map_of_injective K.subtype_injective, S.card_eq_multiplicity]
      have hSq : IsPGroup q ((S : Subgroup K).map K.subtype) := IsPGroup.of_card hScard
      have hSlt : (S : Subgroup K).map K.subtype < K := by
        refine lt_of_le_of_ne hSK fun heq => hnot q hq hqp ?_
        rw [← heq]
        exact hSq
      rw [← hScard]
      exact Subgroup.card_dvd_of_le (le_inf hSK (h _ hSlt hS))
    · rw [Nat.factorization_eq_zero_of_not_dvd hqK, pow_zero]
      exact one_dvd _
  exact inf_eq_left.1 (Subgroup.eq_of_le_of_card_ge inf_le_left (Nat.le_of_dvd Nat.card_pos hdvd))

@[expose] def SignalizerNoncentralMinimal (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D : Subgroup G), ExtremalObstruction p P M D →
    (P : Subgroup G) ≤ normalizer (D : Set G) → ∀ z ∈ (center D).map D.subtype, z ≠ 1 →
      ∀ K : Subgroup G, Nat.Coprime p (Nat.card K) →
        (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) ≤ normalizer (K : Set G) →
        ¬ K ≤ centralizer ({z} : Set G) →
        ∀ q : ℕ, q.Prime → q ≠ p → IsPGroup q K →
        (∀ K' : Subgroup G, K' < K →
          (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) ≤ normalizer (K' : Set G) → K' ≤ M) →
        ¬ (P : Subgroup G) ≤ normalizer (K : Set G) → K ≤ M

theorem signalizerNoncentralPart_of_minimal (hS : Setting G)
    (hI : SignalizerCentralNonConstrained G) (h : SignalizerNoncentralMinimal G) :
    SignalizerNoncentralPart G := by
  intro p hp P M D hext hPD z hzZ hz1 K₀ hK₀ hAK₀ _
  have hprime := sigmaA_prime p hp
  have hD := (hext.exists_normal_plane hS hp hPD).1
  obtain ⟨hM, hDP, -, -⟩ := hext.obstruction
  have hP3 := (sylow_le_of_isCoreMaxLocal hS hp hM).2
  obtain ⟨E, hEP, hE, hEc⟩ := pRank_attained p (P : Subgroup G) (by omega)
  rw [hP3] at hEc
  have hA : IsPGroup p ((P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) : Subgroup G) :=
    P.isPGroup'.to_le inf_le_left
  suffices key : ∀ (n : ℕ) (K : Subgroup G), Nat.card K = n → Nat.Coprime p (Nat.card K) →
      (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) ≤ normalizer (K : Set G) → K ≤ M from
    key _ K₀ rfl hK₀ hAK₀
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K hKn hK hAK
    have hKp : ¬ p ∣ Nat.card K := (Nat.Prime.coprime_iff_not_dvd hprime).1 hK
    have hproper : ∀ K' : Subgroup G, K' < K →
        (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) ≤ normalizer (K' : Set G) → K' ≤ M :=
      fun K' hK' hAK' => ih (Nat.card K') (hKn ▸ Subgroup.card_lt_of_lt hK') K' rfl
        (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hK'.le) hK) hAK'
    by_cases hKz : K ≤ centralizer ({z} : Set G)
    ·
      have hDK : D ≤ normalizer (K : Set G) := (le_inf hDP le_sup_left).trans hAK
      by_cases hcon : CFSG.RankThreeCoreUniqueness.Helpers.HasPrimeConstraint
          (G := centralizer ({z} : Set G)) p
      · exact hext.le_of_le_centralizer_of_hasPrimeConstraint hS hp hPD hD hzZ hcon hK hDK hKz
      · exact hI p hp P M D hext hPD z hzZ hz1 hcon K hK hAK hKz
    · by_cases hPK : (P : Subgroup G) ≤ normalizer (K : Set G)
      ·
        exact le_of_elemAbelian_normalizes hS hp hM hEP hE hEc hKp (hEP.trans hPK)
      · by_cases hq : ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ IsPGroup q K
        · obtain ⟨q, hq, hqp, hqK⟩ := hq
          exact h p hp P M D hext hPD z hzZ hz1 K hK hAK hKz q hq hqp hqK hproper hPK
        · push Not at hq
          exact le_of_proper_invariant_subgroups_le hprime hA hAK hKp hq hproper

end CFSG.LocalAnalysis.RankThreeTheoremC
