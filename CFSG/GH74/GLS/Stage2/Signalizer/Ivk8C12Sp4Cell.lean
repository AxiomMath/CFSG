module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12Sp4
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12Sp4Surv
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12Four
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4Kind

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped MatrixGroups

theorem not_kfa_psp4 {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hM : LieModel Y .PSp 2 p f) (hq : ¬ (p = 3 ∧ f = 1)) : ¬ KindFactorAll Kind.ly Y := by
  intro h
  have hdvd4 := pow_four_dvd_card_of_psp4 hp hp2 hM
  have h11 : (p ^ f) ^ 4 ∣ Nat.factorial 11 :=
    hdvd4.trans (KindFactorAll.card_dvd h (Or.inr rfl))
  exact hq (prime_pow_four_dvd_factorial hp hp2 hf h11)

theorem cellAbs_Sp4 : CellAbs FSp4 := by
  intro A _ _ zb Sb Vb J hfr hJ hnc hF
  obtain ⟨p, f, hp, hf, hp2, hM⟩ := hF
  exfalso
  by_cases hq : p = 3 ∧ f = 1
  · obtain ⟨rfl, rfl⟩ := hq
    obtain ⟨hs, hcfg⟩ := hfr.sylCfg hJ hnc
    exact not_sylCfgOf_Sp43 hs (not_isSolvable_quot_of_quasisimple hJ.1) hM hcfg
  · obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := CFSG.GH74.GLS.Stage2.Final.lieModel_psp_unpack hM
    have hnk : ¬ KindFactorAll Kind.ly (↥J ⧸ center ↥J) := not_kfa_psp4 hp hp2 hf hM hq
    obtain ⟨hZ, -, -⟩ := hfr.reduce hJ hnk
    let eJ : (↥J ⧸ center ↥J) ≃* ↥J :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    let e' : (↥J ⧸ center ↥J) ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 F) := e
    let ι : CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 F) →* A :=
      J.subtype.comp (e'.symm.trans eJ).toMonoidHom
    have hι : Function.Injective ι :=
      (Subgroup.subtype_injective _).comp (e'.symm.trans eJ).injective
    have : Fact p.Prime := ⟨hp⟩
    have : CharP F p := by
      have := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
    have hK2 : ringChar F ≠ 2 := by rwa [ringChar.eq F p]
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hK2
    have hFodd : Odd (Nat.card F) := by
      rw [hcard]
      exact (hp.odd_of_ne_two hp2).pow
    have hne3 : p ^ f ≠ 3 := by
      intro h3
      apply hq
      have hp3 : p = 3 :=
        (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (h3 ▸ dvd_pow_self p (by omega))
      subst hp3
      exact ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 3)
        (show 3 ^ f = 3 ^ 1 by rw [h3, pow_one])⟩
    have h5 : 5 ≤ Nat.card F := by
      rw [hcard]
      have h2' : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
      have hodd' := Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow : Odd (p ^ f))
      omega
    exact false_of_four hfr ι hι hFodd h5 xa_sq xs_sq (xa_ne_one h2) xs_ne_one xs_ne_xa
      xa_xs_comm dP (fun g hg => dP_eq_one hg) dP_mul_xa dP_mul_xs

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
