module

public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
public import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements
import CFSG.LocalAnalysis.RankThreeTheoremC.Signalizers

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCoreIn_centralizer_le (hS : Setting G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M) {x : G}
    (h3 : 3 ≤ CFSG.Open.pRank p ((P : Subgroup G) ⊓ centralizer ({x} : Set G))) :
    CFSG.ABGTheoremB.pPrimeCoreIn p (centralizer ({x} : Set G)) ≤ M := by
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  have hP3 := (sylow_le_of_isCoreMaxLocal hS hp hM).2
  have hle3 : CFSG.Open.pRank p ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) ≤ 3 :=
    hP3 ▸ pRank_mono p hprime.one_lt inf_le_left
  obtain ⟨A, hA, hAe, hAc⟩ :=
    pRank_attained p ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) (by omega)
  rw [show CFSG.Open.pRank p ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) = 3 by omega] at hAc
  have : (CFSG.pPrimeCore p (centralizer ({x} : Set G))).Normal := CFSG.pPrimeCore_normal
  have hcop : ¬ p ∣ Nat.card (CFSG.ABGTheoremB.pPrimeCoreIn p (centralizer ({x} : Set G))) := by
    rw [CFSG.ABGTheoremB.pPrimeCoreIn, card_map_of_injective (centralizer _).subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd hprime).1 CFSG.pPrimeCore_coprime_card
  exact le_of_elemAbelian_normalizes hS hp hM (hA.trans inf_le_left) hAe hAc hcop
    ((hA.trans inf_le_right).trans (CFSG.ABGTheoremB.le_normalizer_map_subtype _ _))

theorem centralizer_le_of_two_dvd_card_pPrimeCoreIn (hS : Setting G) (hD1 : TheoremD1 G)
    {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G}
    (hM : IsCoreMaxLocal p P M) {x : G}
    (h3 : 3 ≤ CFSG.Open.pRank p ((P : Subgroup G) ⊓ centralizer ({x} : Set G)))
    (heven : 2 ∣ Nat.card (CFSG.ABGTheoremB.pPrimeCoreIn p (centralizer ({x} : Set G)))) :
    centralizer ({x} : Set G) ≤ M := by
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPM := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set Y : Subgroup G := CFSG.ABGTheoremB.pPrimeCoreIn p C with hY
  have : (CFSG.pPrimeCore p C).Normal := CFSG.pPrimeCore_normal
  have hYM : Y ≤ M := pPrimeCoreIn_centralizer_le hS hp hM h3
  have hCY : C ≤ normalizer (Y : Set G) := CFSG.ABGTheoremB.le_normalizer_map_subtype _ _
  have hYcop : Nat.Coprime p (Nat.card Y) := by
    rw [hY, CFSG.ABGTheoremB.pPrimeCoreIn, card_map_of_injective C.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  obtain ⟨T, hT⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 Y
  have hTne : T ≠ ⊥ := by
    intro hT1
    have hcard := hT.card_eq
    rw [hT1, card_bot] at hcard
    have hpos : 0 < (Nat.card Y).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' heven
    have : 2 ^ (Nat.card Y).factorization 2 ≠ 1 := (Nat.one_lt_two_pow hpos.ne').ne'
    exact this hcard.symm
  have hNT : normalizer (T : Set G) ≤ M :=
    normalizer_le_of_isSylowOf_two_of_le hD1 hp hM (inf_le_left.trans hPM)
      (P.isPGroup'.to_le inf_le_left) h3 hYM (inf_le_right.trans hCY) hYcop hT hTne
  exact (le_sup_normalizer_of_isSylowOf hCY hT).trans (sup_le hYM hNT)

theorem odd_card_pPrimeCoreIn_of_not_le (hS : Setting G) (hD1 : TheoremD1 G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {x : G} (h3 : 3 ≤ CFSG.Open.pRank p ((P : Subgroup G) ⊓ centralizer ({x} : Set G)))
    (hxM : ¬ centralizer ({x} : Set G) ≤ M) :
    ¬ 2 ∣ Nat.card (CFSG.ABGTheoremB.pPrimeCoreIn p (centralizer ({x} : Set G))) :=
  fun heven => hxM (centralizer_le_of_two_dvd_card_pPrimeCoreIn hS hD1 hp hM h3 heven)

end CFSG.LocalAnalysis.RankThreeTheoremC
