module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.HallCoreInSigmaCore

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson CFSG.FeitThompson

universe u

variable {G : Type*} [Group G] [Finite G] {L M : Subgroup G}

theorem not_dvd_natCard_hallCoreIn_of_dvd [IsSimpleGroup G]
    (hL : IsCoatom L) (hM : IsCoatom M) (hdisj : sigmaPrimes M ∩ sigmaPrimes L = ∅)
    {p : ℕ} (hp : p.Prime) (hpL : p ∣ Nat.card (hallCoreIn L)) :
    ¬ p ∣ Nat.card (hallCoreIn M) := by
  rw [natCard_hallCoreIn] at hpL
  intro hpM
  rw [natCard_hallCoreIn] at hpM
  have hmem : p ∈ sigmaPrimes M ∩ sigmaPrimes L :=
    ⟨mem_sigmaPrimes_of_dvd_natCard_hallCore hM hp hpM,
      mem_sigmaPrimes_of_dvd_natCard_hallCore hL hp hpL⟩
  rw [hdisj] at hmem
  exact hmem

theorem coprime_natCard_hallCoreIn [IsSimpleGroup G]
    (hL : IsCoatom L) (hM : IsCoatom M) (hdisj : sigmaPrimes M ∩ sigmaPrimes L = ∅) :
    Nat.Coprime (Nat.card (hallCoreIn L)) (Nat.card (hallCoreIn M)) := by
  by_contra hc
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hc
  exact not_dvd_natCard_hallCoreIn_of_dvd hL hM hdisj hp (hpd.trans (Nat.gcd_dvd_left _ _))
    (hpd.trans (Nat.gcd_dvd_right _ _))

omit [Finite G] in
theorem natCard_hallCoreIn_ne_of_ne_bot
    (hcop : Nat.Coprime (Nat.card (hallCoreIn L)) (Nat.card (hallCoreIn M)))
    (hLbot : hallCoreIn L ≠ ⊥) :
    Nat.card (hallCoreIn L) ≠ Nat.card (hallCoreIn M) := fun heq =>
  hLbot (Subgroup.card_eq_one.1 ((Nat.coprime_self _).1 (heq ▸ hcop)))

theorem FNI_nonconjugate_maxima_hall_cores_coprime
    (h₁ : Statements.FTS_sigma_prime_separation.{u}) :
    Statements.FNI_nonconjugate_maxima_hall_cores_coprime.{u} := by
  intro G _ _ hG L M hL hM hne
  have := hG.isSimpleGroup
  have hsep : sigmaPrimes M ∩ sigmaPrimes L = ∅ :=
    h₁ G ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
      M L hM hL fun g h => hne g h.symm
  have hcop := coprime_natCard_hallCoreIn hL hM hsep
  exact ⟨hcop, fun hLbot _ => natCard_hallCoreIn_ne_of_ne_bot hcop hLbot⟩

end

end CFSG.FeitThompson.Proofs
