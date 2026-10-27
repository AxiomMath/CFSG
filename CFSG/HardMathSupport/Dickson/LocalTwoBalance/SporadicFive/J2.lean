module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10Red
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveJ2
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalTwoFrontier
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicFive.J2HeAux.PlaneWitness

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.RankThree.PartOne

theorem sporadicTwoBalanceFive_J2 :
    SporadicTwoBalanceFive .J2 := by
  intro S _ _ hS hnab ⟨e⟩
  obtain ⟨bJ⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  let θ : S ≃* ↥j2P := e.trans (bJ.symm.trans j2PermEquiv)
  have hM := j2_autModel
  have hcen : Subgroup.center S = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab
  have hout : Nat.card (Outer S) ≤ 2 := by
    rw [Nat.card_congr (equivalence θ).toEquiv]
    exact j2_outer_card_le
  obtain ⟨S₀, hS₀⟩ := j2FiveQ_sylow
  have hcard : Nat.card S₀ = 5 ^ 2 := by
    show Nat.card (S₀ : Subgroup ↥j2P) = 5 ^ 2
    rw [hS₀, Nat.card_congr (Subgroup.subgroupOfEquivOfLe j2FiveQ_le_P).toEquiv, card_j2FiveQ]
    norm_num
  let d₀ : ↥j2P := ⟨j2FiveLine 0, j2FiveQ_le_P (j2FiveLine_mem_Q 0)⟩
  have hd₀S : d₀ ∈ S₀ := by
    show d₀ ∈ (S₀ : Subgroup ↥j2P)
    rw [hS₀]
    exact Subgroup.mem_subgroupOf.2 (j2FiveLine_mem_Q 0)
  have hd₀1 : d₀ ≠ 1 := fun h => j2FiveLine_ne_one 0 (congrArg Subtype.val h)
  have hΦ₀ : CFSG.Open.GLAPPrimeCoreOf 5
      (Subgroup.centralizer ({(d₀ : Equiv.Perm (Fin 315))} : Set (Equiv.Perm (Fin 315))) ⊓ j2R) =
        ⊥ :=
    gLAPPrimeCoreOf_j2FiveC_eq_bot 0
  have hwit : ∀ E : Subgroup ↥j2P, CFSG.Open.IsElemAbelian 5 E → Nat.card E = 5 ^ 2 →
      ∃ d ∈ E, d ≠ 1 ∧ CFSG.Open.GLAPPrimeCoreOf 5
        (Subgroup.centralizer ({(d : Equiv.Perm (Fin 315))} : Set (Equiv.Perm (Fin 315))) ⊓ j2R) =
          ⊥ :=
    fun E hE hEc => CFSG.HardMathSupport.Dickson.LocalTwoBalance.J2HeAux.exists_plane_witness_sq
      Nat.prime_five S₀ hcard hd₀S hd₀1
      (fun d => CFSG.Open.GLAPPrimeCoreOf 5
        (Subgroup.centralizer ({(d : Equiv.Perm (Fin 315))} : Set (Equiv.Perm (Fin 315))) ⊓ j2R) =
          ⊥)
      (fun g d hd => CFSG.HardMathSupport.Dickson.LocalTwoBalance.J2HeAux.gLAPPrimeCoreOf_centralizer_conj
        5 (hM.le g.2) hd)
      hΦ₀ E hE hEc
  exact CFSG.HardMathSupport.Timmesfeld.Coordinator.isLocallyBalancedAbs_two_of_autModel
    Nat.prime_five (by norm_num) hM θ hcen hout hwit

end CFSG.HardMathSupport.Dickson.LocalTwoBalance
