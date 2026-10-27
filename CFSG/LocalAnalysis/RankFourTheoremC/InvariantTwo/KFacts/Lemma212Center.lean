module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.CenterCyclic
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212Inputs
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Subgroup CFSG.Open
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.GH74.Generic (card_ker_dvd_hopfMultiplier centralQuotientMap centralQuotientMap_ker
  centralQuotientMap_surjective)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (exists_lieModel)
open CFSG.RankThree.PartTwo.Sec4.Census (SporadicMultipliers)
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator (not_dvd_sporadicMultiplierOrder)
open CFSG.RankThree.PerfectCover (hopfMultiplier hopfMultiplierEquivGriess)

theorem not_dvd_twelve_of_five_le {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ∣ 12 := by
  intro hd
  have hle := Nat.le_of_dvd (by norm_num) hd
  interval_cases p <;> revert hp hd <;> decide

theorem genericOrders_fst_dvd_twelve (t : StatedLieTag) (n r f : ℕ) (h1 : t ≠ .PSL)
    (h2 : t ≠ .PSU) : (genericOrders t n r f).1 ∣ 12 := by
  cases t
  · exact absurd rfl h1
  · exact absurd rfl h2
  all_goals
    simp [genericOrders]
    try split_ifs
    all_goals first
      | exact (Nat.gcd_dvd_left _ _).trans (by norm_num)
      | norm_num

theorem eq_psl_or_psu_of_dvd_genericOrders {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (t : StatedLieTag) (n r f : ℕ) (h : p ∣ (genericOrders t n r f).1) :
    (t = .PSL ∧ p ∣ n ∧ p ∣ r ^ f - 1) ∨ (t = .PSU ∧ p ∣ n ∧ p ∣ r ^ f + 1) := by
  by_cases h1 : t = .PSL
  · subst h1
    have h' : p ∣ Nat.gcd n (r ^ f - 1) := h
    exact Or.inl ⟨rfl, (Nat.dvd_gcd_iff.1 h').1, (Nat.dvd_gcd_iff.1 h').2⟩
  by_cases h2 : t = .PSU
  · subst h2
    have h' : p ∣ Nat.gcd n (r ^ f + 1) := h
    exact Or.inr ⟨rfl, (Nat.dvd_gcd_iff.1 h').1, (Nat.dvd_gcd_iff.1 h').2⟩
  exact absurd (h.trans (genericOrders_fst_dvd_twelve t n r f h1 h2))
    (not_dvd_twelve_of_five_le hp hp5)

theorem p_dvd_genericOrders_of_lieModel (hGA : CFSG.Open.GriessAllModelsStatement) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {K X : Type} [Group K] [Finite K] [Group X]
    (hq : CFSG.Open.IsQuasisimple K) (e : K ⧸ Subgroup.center K ≃* X)
    {t : StatedLieTag} {n r f : ℕ} (hm : CFSG.Models.LieModel X t n r f)
    (hdvd : p ∣ Nat.card (center K)) : p ∣ (genericOrders t n r f).1 := by
  haveI hperf : Group.IsPerfect K := ⟨hq.1⟩
  have h1 := card_ker_dvd_hopfMultiplier hperf (centralQuotientMap e)
    (centralQuotientMap_surjective e) (centralQuotientMap_ker e).le
  rw [centralQuotientMap_ker e] at h1
  obtain ⟨-, ⟨g⟩⟩ := hGA X t n r f hm
  have hcard : Nat.card (hopfMultiplier X) =
      ((genericOrders t n r f).1 * (genericOrders t n r f).2) *
        ((exceptionalOrders t n r f).1 * (exceptionalOrders t n r f).2) := by
    rw [← Nat.card_congr (hopfMultiplierEquivGriess X).toEquiv, Nat.card_congr g.toEquiv,
      Nat.card_prod]
    unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
    simp only [Nat.card_prod, Nat.card_zmod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _)]
  have h2 := hdvd.trans h1
  rw [hcard] at h2
  have hno := not_dvd_multiplierOrders_of_five_le hp hp5 t n r f
  rcases hp.dvd_mul.1 h2 with h3 | h3
  · rcases hp.dvd_mul.1 h3 with h4 | h4
    · exact h4
    · exact absurd (dvd_mul_of_dvd_left h4 _) hno
  · exact absurd (dvd_mul_of_dvd_right h3 _) hno

theorem isLinearOrUnitaryAt_of_tables
    (hGA : CFSG.Open.GriessAllModelsStatement) (hSp : SporadicMultipliers) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hcat : CFSG.Open.IsCatalogGroup (K ⧸ Subgroup.center K))
    (hZ : Subgroup.center K ≠ ⊥) (hZp : IsPGroup p (Subgroup.center K)) :
    IsLinearOrUnitaryAt p (K ⧸ Subgroup.center K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hperf : Group.IsPerfect K := ⟨hq.1⟩
  haveI : Nontrivial (center K) := (Subgroup.nontrivial_iff_ne_bot _).2 hZ
  obtain ⟨m, hm, hmcard⟩ := hZp.nontrivial_iff_card.mp inferInstance
  have hdvd : p ∣ Nat.card (center K) := hmcard ▸ dvd_pow_self p hm.ne'
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic q hq' =>
    exfalso
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq
    have hc : ∀ x y : (TauCeti.CFSGIndex.cyclic q hq').Group, x * y = y * x :=
      fun x y => mul_comm x y
    exact hab (e.injective (by rw [map_mul, map_mul]; exact hc _ _))
  | alternating m hm =>
    exfalso
    have hd1 := card_ker_dvd_hopfMultiplier hperf (centralQuotientMap e)
      (centralQuotientMap_surjective e) (centralQuotientMap_ker e).le
    rw [centralQuotientMap_ker e,
      (CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput m hm).2] at hd1
    have h6 : Nat.card (Subgroup.center K) ∣ 12 := by
      split_ifs at hd1
      · exact hd1.trans (by norm_num)
      · exact hd1.trans (by norm_num)
    exact not_dvd_twelve_of_five_le hp hp5 (hdvd.trans h6)
  | lie d =>
    obtain ⟨t, n, r, f, hmodel⟩ := exists_lieModel d
    have hpa := p_dvd_genericOrders_of_lieModel hGA hp hp5 hq e hmodel hdvd
    rcases eq_psl_or_psu_of_dvd_genericOrders hp hp5 t n r f hpa with
      ⟨rfl, hn, hr⟩ | ⟨rfl, hn, hr⟩
    · obtain ⟨⟨-, -, hn2, -⟩, hcl⟩ := hmodel
      rcases hcl with ⟨-, K', hF, hFin, hcard, ⟨e'⟩⟩ | ⟨h0, -⟩
      · exact Or.inl ⟨n, K', hF, hFin, hn, by rw [hcard]; exact hr, ⟨e.trans e'⟩⟩
      · omega
    · obtain ⟨⟨-, -, hn2, -⟩, hcl⟩ := hmodel
      rcases hcl with ⟨-, K', hF, hFin, hcard, ⟨e'⟩⟩ | ⟨h0, -⟩
      · exact Or.inr ⟨n, r ^ f, K', hF, hFin, hcard, hn, hr, ⟨e.trans e'⟩⟩
      · omega
  | sporadic s =>
    exfalso
    have hd1 := card_ker_dvd_hopfMultiplier hperf (centralQuotientMap e)
      (centralQuotientMap_surjective e) (centralQuotientMap_ker e).le
    rw [centralQuotientMap_ker e, hSp.1 s] at hd1
    exact not_dvd_sporadicMultiplierOrder hp hp5 s (hdvd.trans hd1)

end CFSG.LocalAnalysis.RankFourTheoremC
