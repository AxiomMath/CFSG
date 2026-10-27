module

public import CFSG.RankThree.PartOne.SPOR.Final
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.RecordExtra
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThreeKill

public section

namespace CFSG.HardMathSupport.Dickson.I271

open Subgroup CFSG.Open CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.PartTwo.Sec4 CFSG.Blueprint CFSG.Sporadic.Co2Cert

theorem co2Five_noSig
    (hAut : Co2AllInner) :
    ∀ Ê : Subgroup (MulAut ↥co2P), IsElemAbelian 5 Ê → Nat.card Ê = 5 ^ 2 → NoSig 5 Ê := by
  obtain ⟨⟨hQP, hsyl, hQcard, -⟩, ⟨hlines, -⟩, htrans, -, hC0, hC0c, hAC, hAn, hAc, hAe, hAcc,
    hAcl, hC1, hC1c, -⟩ := R3E_Co2_full_five_centralizer_structures
  have hOK : ∀ r : Fin 2,
      PrimePowOK 5 (Nat.card (co2P ⊓ centralizer ({co2FiveLine (co2FiveRepLine r)} :
        Set (Equiv.Perm (Fin 2300))) : Subgroup (Equiv.Perm (Fin 2300)))) := by
    intro r
    fin_cases r
    · show PrimePowOK 5 (Nat.card (co2P ⊓ centralizer ({co2FiveLine 0} :
        Set (Equiv.Perm (Fin 2300))) : Subgroup (Equiv.Perm (Fin 2300))))
      rw [inf_comm, ← hC0, hC0c]
      exact primePowOK_five_3000
    · show PrimePowOK 5 (Nat.card (co2P ⊓ centralizer ({co2FiveLine 1} :
        Set (Equiv.Perm (Fin 2300))) : Subgroup (Equiv.Perm (Fin 2300))))
      rw [inf_comm, ← hC1, hC1c]
      exact primePowOK_five_600
  have hz : co2FiveLine 0 ∈ co2FiveQ ∧ orderOf (co2FiveLine 0) = 5 := by
    have hmem : zpowers (co2FiveLine 0) ∈
        {H : Subgroup (Equiv.Perm (Fin 2300)) | H ≤ co2FiveQ ∧ Nat.card H = 5} := by
      rw [hlines]
      exact ⟨0, rfl⟩
    exact ⟨hmem.1 (Subgroup.mem_zpowers _), by rw [← Nat.card_zpowers]; exact hmem.2⟩
  have hAexp : ∀ x ∈ co2FiveA, x ^ 5 = 1 := fun x hx => by
    have := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : co2FiveA)
    rw [hAe] at this
    exact congrArg Subtype.val this
  have hCz : co2P ⊓ centralizer ({co2FiveLine 0} : Set (Equiv.Perm (Fin 2300))) =
      co2FiveC0 := by rw [hC0, inf_comm]
  have hm := co2_autModel hAut
  refine noSig_planes_of_record_extra hm (le_trans le_rfl (Nat.le_mul_of_pos_left _ (by norm_num)))
    Nat.prime_five (by norm_num) (Q := co2FiveQ) (by rw [hQcard]; norm_num) hQP hsyl hlines
    (fun j => ⟨co2FiveRepLine (co2FiveRecordOf j), ⟨_, (htrans j).1, (htrans j).2⟩,
      hOK _⟩)
    (A := co2FiveA) (hAC.trans (hC0.le.trans inf_le_right)) (by rw [hAc]; norm_num) hAexp
    (z := co2FiveLine 0) (hm.le (hQP hz.1)) ?_ ?_ ?_ ?_ ?_
  · intro h1
    rw [h1, orderOf_one] at hz
    exact absurd hz.2 (by norm_num)
  · intro q hq
    have : q ∈ co2FiveC0 := hAC hq
    rw [hC0] at this
    exact this.1
  · intro c hc q hq
    rw [hCz] at hc
    have := hAn.conj_mem ⟨q, hAC hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨c, hc⟩
    exact Subgroup.mem_subgroupOf.1 this
  · rw [hCz]
    exact hAcl
  · rw [hCz]
    exact hAcc

theorem sporPlaneKill_Co2_five
    (hOut : SporadicOuterLeTwo) : SporPlaneKill .Co2 5 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
  have b₀ : NativeSporadic.Carrier .Co2 ≃* Spor .Co2 := b
  have eC : NativeSporadic.Carrier .Co2 ≃* co2P := co2PermEquiv
  exact sporPlaneKill_of_noSig_model hOut Nat.prime_five (by norm_num) (by decide)
    (eC.symm.trans b₀)
    (fun R Y hR hR9 hY3 hRY => co2Five_noSig CFSG.RankThree.PartOne.SPOR.co2AllInner_holds R hR hR9 Y
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hY3) hRY) b₀ offPair_Co2


theorem sporPair_Co2_five
    (hOut : SporadicOuterLeTwo) : SporPair .Co2 5 :=
  sporPair_of_planeKill (sporPlaneKill_Co2_five hOut)

end CFSG.HardMathSupport.Dickson.I271
