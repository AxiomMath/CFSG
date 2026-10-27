module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.KFactI122FiveDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.FiveDiagSylowOrder
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.FiveDiagSylowExp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open
open FiveDiagAux

private theorem five_dvd_sq_sub_one_not_twentyfive {q : ℕ} (hq : 1 ≤ q) (h5 : 5 ∣ q + 1)
    (h25 : ¬ 25 ∣ q + 1) : 5 ∣ q ^ 2 - 1 ∧ ¬ 25 ∣ q ^ 2 - 1 := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  have hsq : (p + 1) ^ 2 - 1 = p * (p + 2) := by
    apply Nat.sub_eq_of_eq_add
    ring
  rw [hsq]
  refine ⟨Dvd.dvd.mul_left (by omega) _, fun h => h25 ?_⟩
  have hcop : Nat.Coprime (5 ^ 2) p := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_five]
    intro hp
    omega
  have h' : 25 ∣ (p + 2) * p := by rwa [mul_comm] at h
  have := (Nat.Coprime.dvd_of_dvd_mul_right hcop (by simpa using h' : 5 ^ 2 ∣ (p + 2) * p))
  simpa using this

private theorem pow_five_eq_one_of_sylow {K : Type} [Group K] [Finite K] (S : Sylow 5 K)
    (h : ∀ x : K, (∃ k : ℕ, x ^ 5 ^ k = 1) → x ^ 5 = 1) : ∀ s ∈ (S : Subgroup K), s ^ 5 = 1 := by
  intro s hs
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
  exact h s ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem fiveDiagSylow : FiveDiagSylow := by
  intro K _ _ _ _ _ hdiag S
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcardS : ∀ t : ℕ, 5 ^ t ∣ Nat.card K → 5 ^ t ≤ Nat.card S := by
    intro t ht
    rw [Sylow.card_eq_multiplicity S]
    exact Nat.pow_le_pow_right (by norm_num)
      ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five Nat.card_pos.ne').1 ht)
  rcases hdiag with ⟨n, ℓ, f, hmodel, hg⟩ | ⟨n, ℓ, f, hmodel, hg⟩
  ·
    have hn5 : 5 ∣ n := (Nat.dvd_gcd_iff.1 hg).1
    have hq5 : 5 ∣ ℓ ^ f - 1 := (Nat.dvd_gcd_iff.1 hg).2
    obtain ⟨h4, h6n, h6q⟩ := five_pow_dvd_card_psl hmodel hn5 hq5
    by_cases hn : n = 5
    · by_cases h25 : 25 ∣ ℓ ^ f - 1
      · exact Or.inl (hcardS 6 (h6q h25))
      · refine Or.inr ⟨hcardS 4 h4, ?_⟩
        subst hn
        obtain ⟨-, F, _, _, hF, ⟨φ⟩⟩ := hmodel
        have hF5 : 5 ∣ Nat.card F - 1 := by rw [hF]; exact hq5
        have hF25 : ¬ 25 ∣ Nat.card F - 1 := by rw [hF]; exact h25
        refine pow_five_eq_one_of_sylow S fun x ⟨k, hk⟩ => ?_
        have h1 : (φ x) ^ 5 ^ k = 1 := by rw [← map_pow, hk, map_one]
        have h2 := statedProj_pow_five_eq_one hF5 hF25 (le_refl (StatedSL 5 F)) (φ x) h1
        rw [← map_pow] at h2
        exact (map_eq_one_iff φ φ.injective).1 h2
    · exact Or.inl (hcardS 6 (h6n hn))
  ·
    have hn5 : 5 ∣ n := (Nat.dvd_gcd_iff.1 hg).1
    have hq5 : 5 ∣ ℓ ^ f + 1 := (Nat.dvd_gcd_iff.1 hg).2
    obtain ⟨h4, h6n, h6q⟩ := five_pow_dvd_card_psu hmodel hn5 hq5
    by_cases hn : n = 5
    · by_cases h25 : 25 ∣ ℓ ^ f + 1
      · exact Or.inl (hcardS 6 (h6q h25))
      · refine Or.inr ⟨hcardS 4 h4, ?_⟩
        subst hn
        obtain ⟨⟨hℓ, -⟩, F, _, _, hF, ⟨φ⟩⟩ := hmodel
        have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
        obtain ⟨hs5, hs25⟩ := five_dvd_sq_sub_one_not_twentyfive hq1 hq5 h25
        have hF5 : 5 ∣ Nat.card F - 1 := by rw [hF]; exact hs5
        have hF25 : ¬ 25 ∣ Nat.card F - 1 := by rw [hF]; exact hs25
        refine pow_five_eq_one_of_sylow S fun x ⟨k, hk⟩ => ?_
        have h1 : (φ x) ^ 5 ^ k = 1 := by rw [← map_pow, hk, map_one]
        have h2 := statedProj_pow_five_eq_one hF5 hF25
          (StatedAPI.statedSU_le_statedSL 5 (ℓ ^ f) F) (φ x) h1
        rw [← map_pow] at h2
        exact (map_eq_one_iff φ φ.injective).1 h2
    · exact Or.inl (hcardS 6 (h6n hn))

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
