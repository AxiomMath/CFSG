module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.KappaComplementStructure
import CFSG.FeitThompson.Local.NonabelianAmbientNormalHallFreeComplement

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson

universe u

variable {G : Type*} [Group G] [Finite G]

theorem notMem_kappaPrimes_of_mem_tauTwoPrimes {p : ℕ} {T : Subgroup G}
    (hp : p ∈ tauTwoPrimes T) : p ∉ kappaPrimes T :=
  notMem_kappaPrimes_of_elementaryAbelianPRank_eq_two (prime_of_mem_tauTwoPrimes hp)
    (elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes hp)

theorem dvd_natCard_of_mem_tauTwoPrimes_of_isLocalKappaSetup {p : ℕ} {T K U : Subgroup G}
    (h : IsLocalKappaSetup T K U) (hp : p ∈ tauTwoPrimes T) : p ∣ Nat.card ↥U := by
  have hprime : p.Prime := prime_of_mem_tauTwoPrimes hp
  have hsigma : ¬ p ∣ Nat.card ↥(sigmaCore T) := fun hd =>
    notMem_sigmaPrimes_of_mem_tauTwoPrimes hp
      (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore T) p
        (Nat.mem_primeFactors.2 ⟨hprime, hd, Nat.card_pos.ne'⟩))
  have hkappa : ¬ p ∣ Nat.card ↥K := by
    intro hd
    refine notMem_kappaPrimes_of_mem_tauTwoPrimes hp
      (isPiSubgroup_iff.1 h.hall_K.isPiSubgroup p ?_)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le_M_K).toEquiv]
    exact Nat.mem_primeFactors.2 ⟨hprime, hd, Nat.card_pos.ne'⟩
  have hT : p ∣ Nat.card ↥(sigmaCore T) * (Nat.card ↥U * Nat.card ↥K) := by
    rw [← h.semidirect_UK.natCard_eq_mul, ← h.semidirect_M.natCard_eq_mul]
    exact dvd_natCard_of_mem_tauTwoPrimes hp
  rcases (Nat.Prime.dvd_mul hprime).1 hT with hd | hd
  · exact absurd hd hsigma
  · rcases (Nat.Prime.dvd_mul hprime).1 hd with hd' | hd'
    · exact hd'
    · exact absurd hd' hkappa

theorem ne_bot_of_tauTwoPrimes_nonempty_of_isLocalKappaSetup {T K U : Subgroup G}
    (h : IsLocalKappaSetup T K U) (hτ : (tauTwoPrimes T).Nonempty) : U ≠ ⊥ := by
  obtain ⟨p, hp⟩ := hτ
  intro hU
  have hd := dvd_natCard_of_mem_tauTwoPrimes_of_isLocalKappaSetup h hp
  rw [hU, Subgroup.card_bot] at hd
  exact (prime_of_mem_tauTwoPrimes hp).one_lt.ne' (Nat.dvd_one.1 hd)

theorem FTS_tau_two_maximum_type_one_or_two
    (h₁ : Statements.FBG_five_type_local_classification.{u})
    (h₂ : Statements.FNI_kappa_local_pair.{u})
    (h₃ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₄ : Statements.FTS_kappa_residual_prime_overgroup_intersection.{u}) :
    Statements.FTS_tau_two_maximum_type_one_or_two.{u} := by
  intro G _ _ hG T hT hτ
  have hamb : IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨K, U, hKT, -, hKhall, hUT, hsdT, hsdUK, -, -⟩ :=
    Proofs.FBG_kappa_complement_structure.{u} h₂ h₃ h₄ G hamb T hT
  have hsetup : IsLocalKappaSetup T K U :=
    ⟨hT, hKT, hKhall, hUT, hsdUK.right_le_normalizer, hsdT, hsdUK⟩
  have hUne : U ≠ ⊥ := ne_bot_of_tauTwoPrimes_nonempty_of_isLocalKappaSetup hsetup hτ
  obtain ⟨hI, hII, -⟩ := (h₁ G hamb).2 T K U hsetup
  by_cases hK : K = ⊥
  · exact Or.inl (hI.2 hK)
  · exact Or.inr (hII.2 ⟨hK, hUne⟩)

end

end CFSG.FeitThompson.Proofs
