module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
import CFSG.RankThree.PartOne.K133B.NC5Cover
import CFSG.RankThree.PartOne.Mult.Alternating
import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow

public section

namespace CFSG.AGLEmbedding.KFactProofs.CoverFive

open CFSG.Open CFSG.Assembly.LowTwoRank TauCeti
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.RankThree.PartTwo.Sec4.Census (SporadicMultipliers sporadicMultiplierOrder)
open CFSG.RankThree.PartOne.N143 (PrimeCoverLieIndex primeCoverLie_of_griess)

theorem isQuasisimple_of_open {K : Type} [Group K] (hq : Open.IsQuasisimple K) :
    CFSG.IsQuasisimple K :=
  ⟨⟨hq.1⟩, hq.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq⟩

theorem dvd_card_center_of_isPGroup {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hZ : Subgroup.center K ≠ ⊥) (hZp : IsPGroup p (Subgroup.center K)) :
    p ∣ Nat.card (Subgroup.center K) := by
  have : Fact p.Prime := ⟨hp⟩
  have hnt : Nontrivial (Subgroup.center K) := (Subgroup.nontrivial_iff_ne_bot _).2 hZ
  obtain ⟨k, hk⟩ := hZp.exists_card_eq
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact absurd hk (Finite.one_lt_card).ne'
  · rw [hk]
    exact dvd_pow_self p (Nat.succ_ne_zero k)

theorem odd_card_center_of_isPGroup {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hZp : IsPGroup p (Subgroup.center K)) :
    Odd (Nat.card (Subgroup.center K)) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hZp.exists_card_eq
  rw [hk]
  exact (hp.odd_of_ne_two hp2).pow

theorem not_dvd_of_five_le {p m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 6 ∨ m = 12) : ¬ p ∣ m := by
  intro h
  have hle : p ≤ m := Nat.le_of_dvd (by omega) h
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> interval_cases p <;>
    first | omega | exact absurd hp (by norm_num)

theorem sporadicMultiplierOrder_cases (s : SporadicName) :
    sporadicMultiplierOrder s = 1 ∨ sporadicMultiplierOrder s = 2 ∨
      sporadicMultiplierOrder s = 3 ∨ sporadicMultiplierOrder s = 4 ∨
      sporadicMultiplierOrder s = 6 ∨ sporadicMultiplierOrder s = 12 := by
  cases s <;> simp [sporadicMultiplierOrder]

theorem not_dvd_card_center_sporadic (hSpor : SporadicMultipliers) {K : Type} [Group K]
    [Finite K] (hq : CFSG.IsQuasisimple K) {s : SporadicName}
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.sporadic s).Group) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) : ¬ p ∣ Nat.card (Subgroup.center K) := fun h => by
  have h1 := h.trans (CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq e)
  rw [hSpor.1 s] at h1
  exact not_dvd_of_five_le hp hp5 (sporadicMultiplierOrder_cases s) h1

theorem cover_five_classical (hGA : GriessMultipliersAllModels) (hSpor : SporadicMultipliers)
    {K : Type} [Group K] [Finite K] (hq : Open.IsQuasisimple K)
    (hcat : IsCatalogGroup (K ⧸ Subgroup.center K)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hZ : Subgroup.center K ≠ ⊥) (hZp : IsPGroup p (Subgroup.center K)) :
    (∃ n ℓ f : ℕ, StatedClassicalModel (K ⧸ Subgroup.center K) .PSL n ℓ f ∧ p ∣ n ∧
        p ∣ ℓ ^ f - 1) ∨
      ∃ n ℓ f : ℕ, StatedClassicalModel (K ⧸ Subgroup.center K) .PSU n ℓ f ∧ p ∣ n ∧
        p ∣ ℓ ^ f + 1 := by
  obtain ⟨i, ⟨e⟩⟩ := hcat
  have hq' : CFSG.IsQuasisimple K := isQuasisimple_of_open hq
  have hpZ : p ∣ Nat.card (Subgroup.center K) := dvd_card_center_of_isPGroup hp hZ hZp
  cases i with
  | cyclic r hr =>
    exfalso
    obtain ⟨a, b, hab⟩ := hq'.2.2
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm (G := Multiplicative (ZMod r)) _ _
  | alternating n hn =>
    exfalso
    have : Group.IsPerfect K := ⟨hq.1⟩
    exact CFSG.RankThree.PartOne.Mult.alternating_center_small_primes hn e hp (by omega) hpZ
  | sporadic s => exact absurd hpZ (not_dvd_card_center_sporadic hSpor hq' e hp hp5)
  | lie d =>
    obtain ⟨dd, hv⟩ := d
    have hidx : PrimeCoverLieIndex p dd := by
      by_cases h5 : p = 5
      · subst h5
        exact CFSG.RankThree.PartOne.K133B.primeCoverLie_five hGA ⟨dd, hv⟩ hq' e hpZ
      · have h7 : 7 ≤ p := by
          by_contra hlt
          obtain rfl : p = 6 := by omega
          exact absurd hp (by norm_num)
        exact primeCoverLie_of_griess hGA hp h7 ⟨dd, hv⟩ hq' e hpZ
    cases dd with
    | A r q =>
      obtain ⟨hpn, hpq⟩ := hidx
      refine Or.inl ⟨r + 1, q.p, q.exponent, ?_, hpn, ?_⟩
      · obtain ⟨hadm, hcl | ⟨h0, -⟩⟩ :=
          CFSG.RankThree.PartTwo.Sec4.Census.lieModel_typeA r q hv
        · obtain ⟨hadm', rest⟩ := hcl
          obtain ⟨k, hkf, hkfin, hk, ⟨e'⟩⟩ := rest
          exact ⟨hadm', k, hkf, hkfin, hk, ⟨e.trans e'⟩⟩
        · omega
      · simpa only [PrimePower.card_def] using hpq
    | twistedA r q =>
      obtain ⟨hpn, hpq⟩ := hidx
      refine Or.inr ⟨r + 1, q.p, q.exponent,
        CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e, hpn, ?_⟩
      simpa only [PrimePower.card_def] using hpq
    | B r q => exact hidx.elim
    | C r q => exact hidx.elim
    | D r q => exact hidx.elim
    | twistedD r q => exact hidx.elim
    | E6 q => exact hidx.elim
    | E7 q => exact hidx.elim
    | E8 q => exact hidx.elim
    | F4 q => exact hidx.elim
    | G2 q => exact hidx.elim
    | twistedE6 q => exact hidx.elim
    | trialityD4 q => exact hidx.elim
    | suzuki m => exact hidx.elim
    | reeG2 m => exact hidx.elim
    | reeF4 m => exact hidx.elim
    | tits => exact hidx.elim

end CFSG.AGLEmbedding.KFactProofs.CoverFive
