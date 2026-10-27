module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallFiKCKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverRankFiveCensus
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicMultD1
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAlphaFive
import CFSG.LocalAnalysis.AGLEmbedding.CoverRankLift
import CFSG.RankThree.PartOne.K159.CenterRank
import CFSG.RankThree.PartOne.K133B.NC5Cover
import CFSG.RankThree.PartOne.Mult.Alternating
import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAlphaFiveUni

public section

namespace CFSG.AGLEmbedding.SporadicMultD1

open CFSG.Open CFSG.Assembly.LowTwoRank TauCeti
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.RankThree.PartOne.N143 (PrimeCoverLieIndex primeCoverLie_of_griess)
open CFSG.AGLEmbedding.KFactProofs.CoverFive

theorem cover_five_classical_of_multD1 (hGA : GriessMultipliersAllModels)
    (hD : SporadicMultipliersD1) {K : Type} [Group K] [Finite K] (hq : Open.IsQuasisimple K)
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
  | sporadic s =>
    exact absurd (hpZ.trans (CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq' e))
      (hD.big s p hp hp5)
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

end CFSG.AGLEmbedding.SporadicMultD1

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.AGLEmbedding.KFactProofs.CoverFive

theorem kFactCoverRankFive_of_multD1 (hGA : GriessMultipliersAllModels)
    (hD : SporadicMultipliersD1) : KFactCoverRankFive := by
  intro K _ _ hq hcat p hp hp5 hZ hZp
  have hpZ : p ∣ Nat.card (Subgroup.center K) := dvd_card_center_of_isPGroup hp hZ hZp
  have hodd : Odd (Nat.card (Subgroup.center K)) :=
    odd_card_center_of_isPGroup hp (by omega) hZp
  have hrank : ∀ B : Subgroup K, (∀ b ∈ B, b ^ p = 1) → (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) →
      p ^ 4 ≤ Nat.card B → 4 ≤ Open.pRank p (⊤ : Subgroup K) :=
    fun B hBp hBc hBcard =>
      le_pRank_of_pow_le_card hp le_top ⟨⟨⟨fun a b => Subtype.ext (hBc a a.2 b b.2)⟩⟩, hBp⟩ hBcard
  rcases SporadicMultD1.cover_five_classical_of_multD1 hGA hD hq hcat hp hp5 hZ hZp with
    ⟨n, ℓ, f, hmod, hpn, hpq⟩ | ⟨n, ℓ, f, hmod, hpn, hpq⟩
  · obtain ⟨B, hBp, hBc, hBcard⟩ :=
      CFSG.RankThree.PartOne.K159.exists_elemAbelian_four_psl hp (by omega) hpZ hodd hmod hpn hpq
    exact hrank B hBp hBc hBcard
  · obtain ⟨B, hBp, hBc, hBcard⟩ :=
      CFSG.RankThree.PartOne.K159.exists_elemAbelian_four_psu hp (by omega) hpZ hodd hmod hpn hpq
    exact hrank B hBp hBc hBcard

open CFSG.RankThree.PartTwo.Sec4.Census CFSG.RankThree.PartOne.N143
  CFSG.AGLEmbedding.KFactProofs.AlphaFive
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

theorem kFactAlphaFive_of_multD1
    (hGA : GriessMultipliersAllModels) (hD : SporadicMultipliersD1) : KFactAlphaFive := by
  intro K _ _ hq hcat p hp hp5 hZne hZp _ T
  refine Or.inr (Or.inr ?_)
  have hperf : commutator K = ⊤ := hq.1
  have hq' : CFSG.IsQuasisimple K := isQuasisimple_of_open_five hq
  have hpZ : p ∣ Nat.card (Subgroup.center K) := dvd_card_center_of_isPGroup hp hZne hZp
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic q hq1 =>
    exfalso
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq
    exact hab (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))
  | alternating m hm =>
    exfalso
    have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq' e
    have h1 := hpZ.trans hdvd
    rw [(CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput m hm).2] at h1
    split_ifs at h1
    · exact not_dvd_of_dvd_twelve hp hp5 (by norm_num : 6 ∣ 12) h1
    · exact not_dvd_of_dvd_twelve hp hp5 (by norm_num : 2 ∣ 12) h1
  | sporadic s =>
    exfalso
    exact hD.big s p hp hp5 (hpZ.trans (CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq' e))
  | lie d =>
    have hPC : PrimeCoverLieIndex p d.1 := by
      by_cases h5 : p = 5
      · subst h5
        exact CFSG.RankThree.PartOne.K133B.primeCoverLie_five hGA d hq' e hpZ
      · have h7 : 7 ≤ p := by
          by_contra hlt
          obtain rfl : p = 6 := by omega
          exact absurd hp (by norm_num)
        exact primeCoverLie_of_griess hGA hp h7 d hq' e hpZ
    obtain ⟨d, hv⟩ := d
    cases d
    case A r q =>
      obtain ⟨hpr, hpq⟩ := hPC
      have hmod := (lieModel_typeA r q hv).2.resolve_right
        (fun h => absurd h.1 (Nat.succ_ne_zero r))
      obtain ⟨-, F, _, _, hF, ⟨e'⟩⟩ := hmod
      have hn : 5 ≤ r + 1 := hp5.trans (Nat.le_of_dvd (Nat.succ_pos r) hpr)
      refine glbCore_eq_top_of_statedSL hperf hp (by omega) hn ?_ (e.trans e') hpZ T
      rw [hF]
      simpa only [TauCeti.PrimePower.card_def] using hpq
    case twistedA r q =>
      obtain ⟨hpr, hpq⟩ := hPC
      obtain ⟨-, F, _, _, hF, ⟨e'⟩⟩ :=
        CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
      have hn : 5 ≤ r + 1 := hp5.trans (Nat.le_of_dvd (Nat.succ_pos r) hpr)
      have hU : UnitaryFieldData q.p q.exponent F :=
        ⟨q.prime_p, q.exponent_pos, by rw [hF, ← pow_mul, mul_comm]⟩
      exact glbCore_eq_top_of_statedSU hU hperf hp hp5 hn
        (by simpa only [TauCeti.PrimePower.card_def] using hpq) e' hpZ T
    all_goals exact False.elim hPC

end CFSG.AGLEmbedding
