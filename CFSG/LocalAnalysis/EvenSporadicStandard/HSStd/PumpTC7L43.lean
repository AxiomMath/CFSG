module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1LAut
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Out
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Emb

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpTC7

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.HarrisLit.P1.L43 CFSG.Blueprint

theorem card_GL_four_three : Nat.card (GL (Fin 4) (ZMod 3)) = 24261120 := by
  rw [Matrix.card_GL_field, ZMod.card]
  decide

theorem not_seven_dvd_card_mulAut_l43 : ¬ 7 ∣ Nat.card (MulAut (projectiveSL 4 (ZMod 3))) := by
  set D := (conjAut 4 (ZMod 3)).range with hD
  have hδδ : dualAut 4 (ZMod 3) * dualAut 4 (ZMod 3) = 1 :=
    (standard_automorphism_transport (K := ZMod 3) (n := 4)).2.2.2.1
  have hidx : D.index ∣ 2 := by
    rw [Subgroup.index_dvd_two_iff']
    refine ⟨dualAut 4 (ZMod 3), fun b => ?_⟩
    obtain ⟨A, ε, hε, rfl⟩ := exists_aut_form b
    interval_cases ε
    · exact Or.inr ⟨A, by rw [pow_zero, mul_one]⟩
    · refine Or.inl ⟨Matrix.GeneralLinearGroup.inverseTranspose A, ?_⟩
      rw [pow_one, ← mul_assoc, dualAut_mul_conjAut, mul_assoc, hδδ, mul_one]
  have hDcard : Nat.card D ∣ Nat.card (GL (Fin 4) (ZMod 3)) := Subgroup.card_range_dvd _
  have hAut : Nat.card (MulAut (projectiveSL 4 (ZMod 3))) = D.index * Nat.card D := by
    rw [mul_comm, Subgroup.card_mul_index]
  intro h7
  have h : 7 ∣ 2 * Nat.card (GL (Fin 4) (ZMod 3)) :=
    h7.trans (hAut ▸ Nat.mul_dvd_mul hidx hDcard)
  rw [card_GL_four_three] at h
  omega

theorem not_seven_dvd_card_of_l43 {Γ : Type} [Group Γ] [Finite Γ] (N : Subgroup Γ) [N.Normal]
    (hC : centralizer (N : Set Γ) = ⊥) (hN : LieModel ↥N .PSL 4 3 1) : ¬ 7 ∣ Nat.card Γ := by
  obtain ⟨K, hK, hfin, hcard, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hN
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hcard, pow_one]
  let e' : ↥N ≃* projectiveSL 4 (ZMod 3) := e.trans
    (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr
      (ZMod.ringEquivOfPrime K Nat.prime_three hc).symm)
  intro h7
  exact not_seven_dvd_card_mulAut_l43
    (h7.trans (card_dvd_of_injective' (conjEmb N e') (conjEmb_injective N e' hC)))

end CFSG.EvenSporadicStandard.HSStd.PumpTC7
