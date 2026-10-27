module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10Red
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalTwoFrontier
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicFive.J2HeAux.PlaneWitness

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.Sporadic.HeldB CFSG.RankThree.PartOne

theorem sporadicTwoBalanceFive_He :
    SporadicTwoBalanceFive .He := by
  intro S _ _ hS hnab ⟨e⟩
  obtain ⟨bH⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  let θ : S ≃* ↥heP := e.trans (bH.symm.trans heEquivP)
  have hM := heAutModel
  have hcen : Subgroup.center S = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab
  have hout : Nat.card (Outer S) ≤ 2 := by
    rw [Nat.card_congr (equivalence θ).toEquiv]
    exact (ctbh_full_automorphism_permutation_model).2.2.2.2.1.le
  obtain ⟨S₀, hS₀⟩ := heFiveQ_sylow
  have hcard : Nat.card S₀ = 5 ^ 2 := by
    show Nat.card (S₀ : Subgroup ↥heP) = 5 ^ 2
    rw [hS₀, Nat.card_congr (Subgroup.subgroupOfEquivOfLe heFiveQ_le_P).toEquiv, card_heFiveQ]
    norm_num
  obtain ⟨-, ⟨hlines, -⟩, -⟩ := R3E_He_full_five_centralizer_structures
  have hz : Subgroup.zpowers (heFiveLine 0) ∈
      Set.range (fun j : Fin 6 => Subgroup.zpowers (heFiveLine j)) := ⟨0, rfl⟩
  rw [← hlines] at hz
  obtain ⟨hzQ, hz5⟩ := hz
  have hmemQ : heFiveLine 0 ∈ heFiveQ := Subgroup.zpowers_le.1 hzQ
  have ho : orderOf (heFiveLine 0) = 5 := by
    rw [← Nat.card_zpowers]
    exact hz5
  have hd₀1' : heFiveLine 0 ≠ 1 := fun h => by
    rw [h, orderOf_one] at ho
    norm_num at ho
  let d₀ : ↥heP := ⟨heFiveLine 0, heFiveQ_le_P hmemQ⟩
  have hd₀S : d₀ ∈ S₀ := by
    show d₀ ∈ (S₀ : Subgroup ↥heP)
    rw [hS₀]
    exact Subgroup.mem_subgroupOf.2 hmemQ
  have hd₀1 : d₀ ≠ 1 := fun h => hd₀1' (congrArg Subtype.val h)
  have hΦ₀ : CFSG.Open.GLAPPrimeCoreOf 5
      (Subgroup.centralizer ({(d₀ : Equiv.Perm (Fin 8330))} : Set (Equiv.Perm (Fin 8330))) ⊓
        heAutGroup) = ⊥ :=
    gLAPPrimeCoreOf_heFiveRecord_eq_bot
  have hwit : ∀ E : Subgroup ↥heP, CFSG.Open.IsElemAbelian 5 E → Nat.card E = 5 ^ 2 →
      ∃ d ∈ E, d ≠ 1 ∧ CFSG.Open.GLAPPrimeCoreOf 5
        (Subgroup.centralizer ({(d : Equiv.Perm (Fin 8330))} : Set (Equiv.Perm (Fin 8330))) ⊓
          heAutGroup) = ⊥ :=
    fun E hE hEc => CFSG.HardMathSupport.Dickson.LocalTwoBalance.J2HeAux.exists_plane_witness_sq
      Nat.prime_five S₀ hcard hd₀S hd₀1
      (fun d => CFSG.Open.GLAPPrimeCoreOf 5
        (Subgroup.centralizer ({(d : Equiv.Perm (Fin 8330))} : Set (Equiv.Perm (Fin 8330))) ⊓
          heAutGroup) = ⊥)
      (fun g d hd => CFSG.HardMathSupport.Dickson.LocalTwoBalance.J2HeAux.gLAPPrimeCoreOf_centralizer_conj
        5 (hM.le g.2) hd)
      hΦ₀ E hE hEc
  exact CFSG.HardMathSupport.Timmesfeld.Coordinator.isLocallyBalancedAbs_two_of_autModel
    Nat.prime_five (by norm_num) hM θ hcen hout hwit

end CFSG.HardMathSupport.Dickson.LocalTwoBalance
