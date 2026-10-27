module

public import CFSG.HardMathSupport.MathTwE6.MonsterThreeBComponents
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BM2Census
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvHat
public import CFSG.HardMathSupport.Solomon.Proving.ONanAutSylow3
public import CFSG.HardMathSupport.Solomon.Coordinator.ONGroup
public import CFSG.HardMathSupport.Solomon.Coordinator.SporOrders
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
public import CFSG.HardMathSupport.Solomon.Proving.AutSixBalance

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.B3B

open CFSG.Open CFSG.Monster.Generated CFSG.AGLEmbedding.Norton.MON5_7

set_option linter.unusedSectionVars false


theorem hUM_holds : ∀ s : Gmat, orderOf s = 3 →
    ¬ CFSG.HardMathSupport.Timmesfeld.SporadicBalance.InvertedByTwoA s →
    ∀ K : Subgroup Gmat, IsComponentOf K (Subgroup.centralizer ({s} : Set Gmat)) →
      CFSG.HardMathSupport.Solomon.Coordinator.IsHatSix ↥K ∨
        CFSG.HardMathSupport.Solomon.LocalBalance.IsHatON ↥K → False := by
  intro s hs hi K hK hhat
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  obtain ⟨c, hc⟩ := isConj_iff.1 (CFSG.HardMathSupport.Dickson.Sec6.BM2.m3bClass_holds s hs hi)
  refine bmInv_false_of_hat_of_mulEquiv (MulAut.conj c) hK hhat ?_
  rw [MulAut.conj_apply, hc]
  intro J hJ hJhat
  have hJw : IsComponentOf J
      (Subgroup.centralizer ((Subgroup.zpowers tbw : Subgroup Gmat) : Set Gmat)) := by
    have e : Subgroup.centralizer ((Subgroup.zpowers tbw : Subgroup Gmat) : Set Gmat) =
        Subgroup.centralizer ({tbw} : Set Gmat) := by
      ext g
      rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        exact (h tbw (Subgroup.mem_zpowers tbw)).symm
      · intro h a ha
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        exact ((Commute.zpow_left h.symm k)).eq
    rw [e]
    exact hJ
  have hperf : commutator ↥J = ⊤ := by
    rcases hJhat with h | h
    · exact h.1
    · exact h.1
  have hinj := CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot_injective_of_perfect hperf
  have h1 : Nat.card (MulAut ↥J) ∣ Nat.card (MulAut (↥J ⧸ Subgroup.center ↥J)) :=
    Subgroup.card_dvd_of_injective _ hinj
  rcases hJhat with ⟨-, -, ⟨e⟩⟩ | ⟨-, -, ⟨e⟩⟩
  ·
    have hcardA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    have hidx : (Subgroup.center ↥J).index = 360 := by
      rw [Subgroup.index, ← hcardA6]
      exact Nat.card_congr e.toEquiv
    have hdvd := CFSG.HardMathSupport.MathTwE6.M3BIrr.components_dvd_card_mulAut_of_certificates J
      hJw (by rw [hidx]; norm_num)
    have h2 : Nat.card (MulAut (↥J ⧸ Subgroup.center ↥J)) = 1440 := by
      rw [← CFSG.HardMathSupport.Solomon.Proving.AutSixBalance.card_mulAut_alt6]
      exact Nat.card_congr (MulAut.congr e).toEquiv
    rw [h2] at h1
    have := hdvd.trans h1
    revert this
    decide
  ·
    have hsimp := CFSG.HardMathSupport.Solomon.Coordinator.inputONGroup_holds.1
    have hord : Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group =
        460815505920 :=
      (CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
        TauCeti.SporadicName.ONan).trans rfl
    have hidx : (Subgroup.center ↥J).index = 460815505920 := by
      rw [Subgroup.index, ← hord]
      exact Nat.card_congr e.toEquiv
    have hdvd := CFSG.HardMathSupport.MathTwE6.M3BIrr.components_dvd_card_mulAut_of_certificates J
      hJw (by rw [hidx]; norm_num)
    obtain ⟨m, hm, hm3⟩ := CFSG.HardMathSupport.Solomon.Proving.onan_card_mulAut_three_part
      CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
      CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds hsimp
      (↥J ⧸ Subgroup.center ↥J) ⟨e⟩
    rw [hm] at h1
    have h3 : 3 ^ 12 ∣ 3 ^ 4 * m := hdvd.trans h1
    have h4 : 3 ^ 8 ∣ m := by
      rw [show (3 : ℕ) ^ 12 = 3 ^ 4 * 3 ^ 8 by norm_num] at h3
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3
    exact hm3 ((dvd_pow_self 3 (by norm_num)).trans h4)

end CFSG.HardMathSupport.Solomon.Coordinator.B3B
