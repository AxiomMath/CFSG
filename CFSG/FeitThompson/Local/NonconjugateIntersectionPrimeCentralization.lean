module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
import CFSG.FeitThompson.Local.NonconjugateIntersectionExcludesTauTwo
import CFSG.FeitThompson.Local.NonconjugateDerivedPrimeIntersectionCentral

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G]

theorem mem_sigmaPrimes_or_mem_tau3Primes [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) {L : Subgroup G} (hL : IsCoatom L)
    {p : ℕ} (hp : p.Prime) (hpL : p ∣ Nat.card ↥L) (h1 : p ∉ tau1Primes L)
    (h2 : p ∉ tauTwoPrimes L) : p ∈ sigmaPrimes L ∨ p ∈ tau3Primes L := by
  by_cases hσ : p ∈ sigmaPrimes L
  · exact Or.inl hσ
  refine Or.inr ?_
  have hα : p ∉ alphaPrimes ↥L := fun h =>
    hσ (alphaPrimes_subset_sigmaPrimes hna hodd hsolv hL h)
  have hlt : elementaryAbelianPRank p ↥L < 3 := by
    by_contra h
    exact hα (mem_alphaPrimes.2 ⟨hp, by omega⟩)
  have hge : 1 ≤ elementaryAbelianPRank p ↥L := (one_le_elementaryAbelianPRank_iff hp).2 hpL
  have hne2 : elementaryAbelianPRank p ↥L ≠ 2 := fun h =>
    h2 (mem_tauTwoPrimes_iff.2 ⟨hp, hσ, h⟩)
  have hrank : elementaryAbelianPRank p ↥L = 1 := by omega
  rw [mem_tau3Primes_iff]
  refine ⟨hp, hpL, hσ, hrank, ?_⟩
  by_contra hdvd
  exact h1 (mem_tau1Primes_iff.2 ⟨hp, hpL, hσ, hrank, hdvd⟩)

theorem commutator_eq_bot_of_notMem_tau1Primes [Finite G]
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FBG_sigma_prime_normalizer_narrow_rank_bound.{u})
    (h₃ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (hG : IsFBGAmbient G) {M L E : Subgroup G} {p : ℕ}
    (hsetup : IsNonconjugateSetup M L E p) (hp1 : p ∉ tau1Primes L)
    (hne : ⁅(sigmaCore M ⊓ L : Subgroup G), (M ⊓ L : Subgroup G)⁆ ≠ ⊥)
    {P : Subgroup G} (hPML : P ≤ M ⊓ L) (hPp : IsPGroup p ↥P) :
    ⁅P, (sigmaCore M ⊓ L : Subgroup G)⁆ = ⊥ := by
  have hsimple := hG.isSimpleGroup
  have hp2 : p ∉ tauTwoPrimes L :=
    notMem_tauTwoPrimes_of_commutator_ne_bot h₁ h₂ h₃ hG hsetup hne
  have hor := mem_sigmaPrimes_or_mem_tau3Primes hG.not_isMulCommutative hG.odd_natCard
    hG.isSolvable hsetup.isCoatom_L hsetup.prime hsetup.dvd_natCard_L hp1 hp2
  have hcent := FBG_nonconjugate_derived_prime_intersection_centralization h₁ G hG M L E p
    hsetup hor P hPML hPp
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcent

theorem FBG_nonconjugate_intersection_prime_centralization
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FBG_sigma_prime_normalizer_narrow_rank_bound.{u})
    (h₃ : Statements.FNI_outside_sigma_plane_sylow.{u}) :
    Statements.FBG_nonconjugate_intersection_prime_centralization.{u} := by
  intro G _ _ hG M L E p hsetup hp1 hne P hPML hPp
  exact commutator_eq_bot_of_notMem_tau1Primes h₁ h₂ h₃ hG hsetup hp1 hne hPML hPp

end

end CFSG.FeitThompson.Proofs
