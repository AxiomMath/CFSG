module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import CFSG.GH74.Exceptional.UnitaryFourTwo

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.Exceptional
  CFSG.Sporadic.Schreier

theorem card_mulAut_of_lieModel_psu42 {K : Type} [Group K]
    (h : Blueprint.LieModel K .PSU 4 2 1) :
    Nat.card (MulAut K) = 51840 ∧ Nat.card K = 25920 := by
  obtain ⟨e⟩ := equiv_of_lieModel (lieModel_PSp_two_three_of_lieModel_PSU_four_two h)
  obtain ⟨M, -, hA⟩ := exists_model e
  have hA' : Nat.card QA45.originalSubgroup = 51840 :=
    (QA45.orderCertificate_eq_card QA45_ok).symm.trans QA45_valid.2
  have hP' : Nat.card QP45.originalSubgroup = 25920 :=
    (QP45.orderCertificate_eq_card QP45_ok).symm.trans QP45_valid.2
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr M.Φ.toEquiv, ← hA']
    exact Nat.card_congr (MulEquiv.subgroupCongr hA).toEquiv
  · rw [Nat.card_congr e.toEquiv, hP']

theorem not_commutative_of_lieModel_psu42 {K : Type} [Group K]
    (h : Blueprint.LieModel K .PSU 4 2 1) : ∃ a b : K, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  obtain ⟨e⟩ := equiv_of_lieModel (lieModel_PSp_two_three_of_lieModel_PSU_four_two h)
  obtain ⟨h1, h2, -⟩ := x45_facts
  have hx : orderOf x45 = 2 := (orderIs_iff _ (by norm_num)).1 h1
  have hy : orderOf y45 = 5 := (orderIs_iff _ (by norm_num)).1 h2
  have hPcomm : ∀ p q : QP45.originalSubgroup, p * q = q * p := fun p q => by
    have := congrArg e (hcomm (e.symm p) (e.symm q))
    simpa using this
  have hexp : ∀ g ∈ QP45.originalSubgroup, g ^ 10 = 1 := by
    intro g hg
    rw [QP45_closure] at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx' =>
      rcases hx' with rfl | rfl
      · rw [show 10 = 2 * 5 by norm_num, pow_mul, ← hx, pow_orderOf_eq_one, one_pow]
      · rw [show 10 = 5 * 2 by norm_num, pow_mul, ← hy, pow_orderOf_eq_one, one_pow]
    | one => exact one_pow _
    | mul a b ha hb iha ihb =>
      have hcab : a * b = b * a := by
        have := hPcomm ⟨a, QP45_closure ▸ ha⟩ ⟨b, QP45_closure ▸ hb⟩
        exact congrArg Subtype.val this
      rw [(show Commute a b from hcab).mul_pow, iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  have hcard := (card_mulAut_of_lieModel_psu42 h).2
  have h3 : 3 ∣ Nat.card K := by rw [hcard]; norm_num
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := QP45.originalSubgroup) 3
    (by rw [← Nat.card_congr e.toEquiv]; exact h3)
  have h10 : (g : Equiv.Perm (Fin 45)) ^ 10 = 1 := hexp g g.2
  have : orderOf g ∣ 10 := orderOf_dvd_of_pow_eq_one (Subtype.ext h10)
  rw [hg] at this
  omega

end CFSG.EvenSporadicStandard.M22Std
