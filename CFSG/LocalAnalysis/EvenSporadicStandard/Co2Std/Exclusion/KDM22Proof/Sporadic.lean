module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTable
import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1SporFix

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion.KDM22Proof

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatFC (SporadicInnerRow SporadicOuterRow sporadic_comp_rows)
open CFSG.ComponentClassification.GS82PumpInputs.SporFix (card_fixedSubgroup_m22
  card_fixedSubgroup_m23 card_fixedSubgroup_m24)

private lemma false_of_card_not_dvd {S : Type} [Group S] {σ : MulAut S} {m : ℕ}
    (hS : Nat.card S = m) (hm : ¬ 443520 ∣ m)
    (hdvd : 443520 ∣ Nat.card (fixedSubgroup σ)) : False :=
  hm (hS ▸ hdvd.trans (Subgroup.card_subgroup_dvd_card (fixedSubgroup σ)))

section Certificates


theorem false_of_sporadic
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) {s : TauCeti.SporadicName}
    (e : S ≃* CFSG.Blueprint.NativeSporadic.Carrier s) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : CFSG.IsComponent D)
    (hcard : Nat.card (D ⧸ Subgroup.center D) = 443520)
    (hdvd : 443520 ∣ Nat.card (fixedSubgroup σ)) : False := by
  obtain ⟨hin, hout⟩ := sporadic_comp_rows hS hna e hσ hD
  have hrow : SporadicInnerRow s (Nat.card (D ⧸ Subgroup.center D)) ∨
      SporadicOuterRow s (Nat.card (D ⧸ Subgroup.center D)) := by
    by_cases h : σ ∈ (MulAut.conj : S →* MulAut S).range
    · exact Or.inl (hin h)
    · exact Or.inr (hout h)
  rw [hcard] at hrow
  cases s
  case M11 =>
    exact false_of_card_not_dvd
      ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M11) (by norm_num) hdvd
  case M12 =>
    exact false_of_card_not_dvd
      ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M12) (by norm_num) hdvd
  case M22 =>
    rcases card_fixedSubgroup_m22 e hσ with h | h | h <;>
      rw [h] at hdvd <;> norm_num at hdvd
  case M23 =>
    have h := card_fixedSubgroup_m23 e hσ
    rw [h] at hdvd
    norm_num at hdvd
  case M24 =>
    rcases card_fixedSubgroup_m24 e hσ with h | h <;>
      rw [h] at hdvd <;> norm_num at hdvd
  case J1 =>
    exact false_of_card_not_dvd
      ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J1.card_J1) (by norm_num) hdvd
  case J2 =>
    exact false_of_card_not_dvd
      ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J2.card_J2) (by norm_num) hdvd
  case J3 =>
    exact false_of_card_not_dvd
      ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J3.card_J3) (by norm_num) hdvd
  all_goals norm_num [SporadicInnerRow, SporadicOuterRow] at hrow

end Certificates

end CFSG.EvenSporadicStandard.Co2Std.Exclusion.KDM22Proof
