module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Open
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult
public import CFSG.GH74.Generic.GKFBridge
public import CFSG.Adapters.TauCetiExceptional.ReeCatalog
import CFSG.LocalAnalysis.SectionRank.QTK.CoverBTable

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank

theorem eq_bot_of_two_group_of_dvd {Z : Type} [Group Z] [Finite Z] (h2 : IsPGroup 2 Z) {m : ℕ}
    (hm : Odd m) (hd : Nat.card Z ∣ m) : Nat.card Z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simpa using hn
  · exfalso
    have h2m : 2 ∣ m := by
      have : 2 ∣ Nat.card Z := by rw [hn]; exact dvd_pow_self 2 (by omega)
      exact this.trans hd
    exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h2m)

theorem card_generic_exceptional' (t : StatedLieTag) (n p f : ℕ) :
    Nat.card (generic t n p f × exceptional t n p f) =
      ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) :=
  CFSG.SectionRank.QTK.CoverB.card_generic_exceptional t n p f

theorem card_center_dvd_table (hGA : CFSG.Open.GriessAllModelsStatement)
    {L : Type} [Group L] [Finite L] (hL : CFSG.IsQuasisimple L) {t : StatedLieTag} {n p f : ℕ}
    (hm : Models.LieModel (L ⧸ center L) t n p f)
    (hne : ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
      ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) ≠ 0) :
    Nat.card (center L) ∣ ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
      ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  obtain ⟨-, ⟨e⟩⟩ := hGA _ t n p f hm
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (L ⧸ center L)) =
      ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
    rw [Nat.card_congr e.toEquiv, card_generic_exceptional']
  have : Finite (CFSG.Open.griessHopfMultiplier (L ⧸ center L)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hne)
  have h1 := card_center_dvd_hopf hL (MulEquiv.refl (L ⧸ center L))
  rwa [hcard] at h1

theorem g2ThreeMult_of_milestone
    (hGA : CFSG.Open.GriessAllModelsStatement) : G2ThreeMult := by
  intro L _ _ hL hZ2 hm
  have hmodels : Models.LieModel (L ⧸ center L) .G2 0 3 1 :=
    CFSG.GH74.Generic.models_of_blueprint_exceptional CFSG.TauCetiBridge.typewiseBridges
      Nat.prime_three (by norm_num) (Or.inl rfl) hm
  have hg : genericOrders .G2 0 3 1 = (1, 1) := rfl
  have he : exceptionalOrders .G2 0 3 1 = (3, 1) := rfl
  have hdvd := card_center_dvd_table hGA hL hmodels (by rw [hg, he]; norm_num)
  rw [hg, he] at hdvd
  have h1 := eq_bot_of_two_group_of_dvd hZ2 (m := 3) (by decide) (by simpa using hdvd)
  exact Subgroup.card_eq_one.mp h1

theorem d4Mult_of_milestone
    (hGA : CFSG.Open.GriessAllModelsStatement) : D4Mult := by
  intro L _ _ hL hZ2 p f hp hf hp2 hm
  have hmodels : Models.LieModel (L ⧸ center L) .trialityD4 0 p f :=
    CFSG.GH74.Generic.models_of_blueprint_exceptional CFSG.TauCetiBridge.typewiseBridges
      hp hp2 (Or.inr (Or.inl rfl)) hm
  have hg : genericOrders .trialityD4 0 p f = (1, 1) := rfl
  have he : exceptionalOrders .trialityD4 0 p f = (1, 1) := rfl
  have hdvd := card_center_dvd_table hGA hL hmodels (by rw [hg, he]; norm_num)
  rw [hg, he] at hdvd
  have h1 := eq_bot_of_two_group_of_dvd hZ2 (m := 1) (by decide) (by simpa using hdvd)
  exact Subgroup.card_eq_one.mp h1

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
