module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSchur
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87MultMilestone

public section

namespace CFSG.OddStandard.L2Ree

open Subgroup CFSG CFSG.Open CFSG.Blueprint CFSG.ComponentClassification

section PNeTwo


theorem p_ne_two_of_l2 {Q : Type} [Group Q] (hodd : OddLieType Q) {p f : ℕ}
    (hm : LieModel Q .PSL 2 p f) (h5 : ¬ Nonempty (Q ≃* alternatingGroup (Fin 5))) : p ≠ 2 := by
  intro hp2
  subst hp2
  have h := CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType_of_ne_Tits hm
    (by decide) hodd
  rcases h with ⟨-, -, hf⟩ | ⟨-, hn, -⟩ | ⟨ht, -, -⟩
  · have hm222 : LieModel Q .PSL 2 2 2 := by rwa [hf] at hm
    exact h5 (CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model Q hm222)
  · exact absurd hn (by decide)
  · exact absurd ht (by decide)

end PNeTwo

theorem odd_center_of_l2 (hGA : TBLit.GriessMultipliersOdd)
    (hGC : TBLit.GriessMultipliersCentralCovers) {L : Type} [Group L] [Finite L]
    (hq : IsQuasisimple L) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : LieModel (L ⧸ center L) .PSL 2 p f)
    (hM : Odd (Nat.card (center L)) ∨
      ordProj[2] (Nat.card (center L)) ≠
        ordProj[2] (Nat.card (griessHopfMultiplier (L ⧸ center L)))) :
    Odd (Nat.card (center L)) := by
  rcases hM with h | h
  · exact h
  · have hm2 := HarrisLit.ordProj_card_griessHopfMultiplier_psl_two hGA hp hp2 hm
    rw [hm2] at h
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨S⟩ : Nonempty (Sylow 2 (center L)) := inferInstance
    have hle : Nat.card S ≤ 2 :=
      HarrisLit.card_sylow_two_center_le_two_of_psl_two hGA hGC hq hp hp2 hm S
    have hcard : Nat.card S = 2 ^ (Nat.card (center L)).factorization 2 :=
      Sylow.card_eq_multiplicity S
    have hk0 : (Nat.card (center L)).factorization 2 = 0 := by
      by_contra hk
      have hk1 : 1 ≤ (Nat.card (center L)).factorization 2 := Nat.one_le_iff_ne_zero.mpr hk
      have hle' : 2 ^ (Nat.card (center L)).factorization 2 ≤ 2 := by
        rw [← hcard]; exact hle
      have h2le : 2 ≤ 2 ^ (Nat.card (center L)).factorization 2 := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ _ := Nat.pow_le_pow_right (by norm_num) hk1
      exact h (le_antisymm hle' h2le)
    have hndvd : ¬ 2 ∣ Nat.card (center L) := by
      rw [Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne', hk0]
      omega
    exact Nat.not_even_iff_odd.mp (fun he => hndvd (even_iff_two_dvd.mp he))

theorem ree_center_trivial (hGA : GriessAllModelsStatement) (hB : TauCetiBridge.TypewiseBridges)
    {L : Type} [Group L] [Finite L] (hq : IsQuasisimple L) {f : ℕ}
    (hm : LieModel (L ⧸ center L) .twistedG2 0 3 f) : center L = ⊥ := by
  have hm' : CFSG.Models.LieModel (L ⧸ center L) .twistedG2 0 3 f :=
    CFSG.GH74.Generic.models_of_blueprint_exceptional hB Nat.prime_three (by norm_num)
      (Or.inr (Or.inr rfl)) hm
  have hne : ((Multiplier.genericOrders .twistedG2 0 3 f).1 *
        (Multiplier.genericOrders .twistedG2 0 3 f).2) *
      ((Multiplier.exceptionalOrders .twistedG2 0 3 f).1 *
        (Multiplier.exceptionalOrders .twistedG2 0 3 f).2) ≠ 0 := by
    simp [Multiplier.genericOrders, Multiplier.exceptionalOrders]
  have hdvd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_table hGA hq hm' hne
  have hprod : ((Multiplier.genericOrders .twistedG2 0 3 f).1 *
        (Multiplier.genericOrders .twistedG2 0 3 f).2) *
      ((Multiplier.exceptionalOrders .twistedG2 0 3 f).1 *
        (Multiplier.exceptionalOrders .twistedG2 0 3 f).2) = 1 := by
    simp [Multiplier.genericOrders, Multiplier.exceptionalOrders]
  rw [hprod] at hdvd
  exact (center L).eq_bot_of_card_eq (Nat.dvd_one.mp hdvd)

end CFSG.OddStandard.L2Ree
