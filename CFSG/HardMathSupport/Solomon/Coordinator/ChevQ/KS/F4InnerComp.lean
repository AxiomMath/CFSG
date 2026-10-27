module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4StdModel
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4SU3Rank
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.F4EightOPrime

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

theorem f4EightClass_holds : KSF4Out.F4EightClass :=
  KSF4Std.f4EightClass_of_core_iso f4EightOPrimeCore_holds
    (fun _ _ _ hY hL => F4InnerExAux.center_bot_and_equiv hY hL)

theorem f4OutStatement_holds : KSF4Rank.F4OutStatement := by
  intro Y _ _ hY hL
  obtain ⟨hZ, F, _, _, ⟨Θ, hΘ⟩, -⟩ := F4InnerExAux.chevalley_data hY hL
  exact ⟨hZ, Θ, hΘ⟩

theorem f4TwoNoNineteen_holds : KSF4Rank.F4TwoNoNineteen := by
  intro F _ _ hs hq hL
  classical
  obtain ⟨d, hdF, ⟨eL⟩⟩ := hL
  obtain ⟨d1, hv⟩ := d
  have hq2 : ∃ q : TauCeti.PrimePower, d1 = TauCeti.LieTypeIndex.F4 q ∧ IsTwoPow q 1 := by
    cases d1 with
    | F4 q => exact ⟨q, rfl, hdF⟩
    | _ => simp [Bal209F4Aux.IsF4TwoIndex] at hdF
  obtain ⟨q, rfl, hq2', hqe⟩ := hq2
  have hZ : Subgroup.center F = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center F) with h | h
    · exact h
    · exfalso
      haveI := hs.toNontrivial
      have hcomm : ⁅(⊤ : Subgroup F), (⊤ : Subgroup F)⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro g _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        have hy : y ∈ Subgroup.center F := h ▸ Subgroup.mem_top y
        exact (Subgroup.mem_center_iff.1 hy g).symm
      rw [← _root_.commutator_def, hq.1] at hcomm
      exact top_ne_bot hcomm
  have hK'card : Nat.card (GaloisField 2 1) = q.card := by
    rw [GaloisField.card 2 1 (by norm_num), TauCeti.PrimePower.card_def, hq2', hqe]
  obtain ⟨eB⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesEven).f4 q hv hq2' (GaloisField 2 1)
    hK'card
  let eKq : F ≃* F ⧸ Subgroup.center F :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  let e : F ≃* adjointGroup Tag.F4 (GaloisField 2 1) :=
    eKq.trans (eL.trans (eB.symm.trans (F4FixedAux.adjointEquiv Tag.F4 (GaloisField 2 1))))
  rw [Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4,
    GaloisField.card 2 1 (by norm_num)]
  norm_num [CFSG.Open.ordF4]

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
