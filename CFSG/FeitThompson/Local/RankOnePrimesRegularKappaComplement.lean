module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.FreeActionKernelGrowthProperInvariant

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson.Prep03
open Subgroup

universe u

variable {G : Type u} [Group G]

theorem natCard_eq_mul_of_isSemidirect {X Y Z : Subgroup G} (h : IsSemidirect X Y Z) :
    Nat.card ↥X = Nat.card ↥Y * Nat.card ↥Z := by
  obtain ⟨-, hZ, hn, hsup, hinf⟩ := h
  rw [← hsup]
  exact natCard_sup_of_le_normalizer (hZ.trans hn) (disjoint_iff.2 hinf)

theorem mem_kappaPrimes_of_cent1_ne_bot [Finite G] {M : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hqM : q ∣ Nat.card ↥M) (hσ : q ∉ sigmaPrimes M)
    (hcyc : ∀ P : Sylow q ↥M, IsCyclic ↥(P : Subgroup ↥M))
    {x : G} (hxM : x ∈ M) (hxo : orderOf x = q) (hne : cent1 (sigmaCore M) x ≠ ⊥) :
    q ∈ kappaPrimes M := by
  have hfq := Fact.mk hq
  have hx'o : orderOf (⟨x, hxM⟩ : ↥M) = q := by rw [Subgroup.orderOf_mk]; exact hxo
  have hpg : IsPGroup q ↥(zpowers (⟨x, hxM⟩ : ↥M)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx'o, pow_one])
  obtain ⟨S, hS⟩ := hpg.exists_le_sylow
  have hx1 : x ≠ 1 := fun h1 => hq.ne_one (by rw [← hxo, h1, orderOf_one])
  rw [mem_kappaPrimes_iff]
  exact ⟨hq, hqM, hσ, S, (isCyclic_map_subtype_iff _).2 (hcyc S), x,
    Subgroup.mem_map_of_mem _ (hS (mem_zpowers _)), hx1, hne⟩

theorem FNI_kappa_complement_rank_one_prime_regularity
    (_h₁ : Statements.FBG_sigma_core_normal_hall.{u}) :
    Statements.FNI_kappa_complement_rank_one_prime_regularity.{u} := by
  intro G _ _ hG M E K U hsetup
  obtain ⟨-, -, hdecomp, hKE, hHallK, hUE, hdecompE⟩ := hsetup
  have hEM : E ≤ M := hdecomp.2.1
  have hKM : K ≤ M := hKE.trans hEM
  have hUM : U ≤ M := hUE.trans hEM
  have hcardM : Nat.card ↥M = Nat.card ↥(sigmaCore M) * Nat.card ↥E :=
    natCard_eq_mul_of_isSemidirect hdecomp
  have hcardE : Nat.card ↥E = Nat.card ↥U * Nat.card ↥K :=
    natCard_eq_mul_of_isSemidirect hdecompE
  have hrelK : K.relIndex M = Nat.card ↥(sigmaCore M) * Nat.card ↥U :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos
      (by rw [CFSG.FeitThompson.natCard_mul_relIndex hKM, hcardM, hcardE]; ring)
  have hrelU : U.relIndex E = Nat.card ↥K :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos
      (by rw [CFSG.FeitThompson.natCard_mul_relIndex hUE, hcardE])
  have hUκ : ∀ r ∈ (Nat.card ↥U).primeFactors, r ∉ kappaPrimes M := by
    intro r hr
    refine hHallK.2.2 r (Nat.mem_primeFactors.2 ⟨Nat.prime_of_mem_primeFactors hr, ?_, ?_⟩)
    · rw [hrelK]; exact Dvd.dvd.mul_left (Nat.dvd_of_mem_primeFactors hr) _
    · rw [hrelK]; exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
  refine ⟨?_, ⟨hUE, hUκ, ?_⟩, hdecompE.2.2.1⟩
  ·
    intro q hq x hxU hxo
    have hdata : q.Prime ∧ q ∣ Nat.card ↥M ∧ q ∉ sigmaPrimes M ∧
        elementaryAbelianPRank q ↥M = 1 := by
      rcases hq with h | h
      · obtain ⟨h1, h2, h3, h4, -⟩ := mem_tau1Primes_iff.1 h
        exact ⟨h1, h2, h3, h4⟩
      · obtain ⟨h1, h2, h3, h4, -⟩ := mem_tau3Primes_iff.1 h
        exact ⟨h1, h2, h3, h4⟩
    obtain ⟨hqp, hqM, hqσ, hqrank⟩ := hdata
    by_contra hne
    have hodd : Odd q := hG.odd_natCard.of_dvd_nat (hqM.trans (Subgroup.card_subgroup_dvd_card M))
    have hcyc : ∀ P : Sylow q ↥M, IsCyclic ↥(P : Subgroup ↥M) :=
      (forall_isCyclic_sylow_iff hqp hodd).2 hqrank.le
    exact hUκ q (Nat.mem_primeFactors.2
        ⟨hqp, hxo ▸ Subgroup.orderOf_dvd_natCard U hxU, Nat.card_pos.ne'⟩)
      (mem_kappaPrimes_of_cent1_ne_bot hqp hqM hqσ hcyc (hUM hxU) hxo hne)
  ·
    intro r hr
    rw [hrelU] at hr
    exact not_not.2 (hHallK.2.1 r hr)

end

end CFSG.FeitThompson.Proofs
