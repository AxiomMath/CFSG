module

public import CFSG.RankThree.PartOne.KS.Co3
public import CFSG.Sporadic.SmallOddCore.Co3Aut
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.RecordExtra
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThreeKill

public section

namespace CFSG.HardMathSupport.Dickson.I271

open Subgroup CFSG.Open CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.PartTwo.Sec4 CFSG.Blueprint CFSG.Sporadic.Schreier.Co3

theorem co3Five_noSig
    (hAut : Co3AllInner) :
    ∀ Ê : Subgroup (MulAut ↥co3P), IsElemAbelian 5 Ê → Nat.card Ê = 5 ^ 2 → NoSig 5 Ê := by
  obtain ⟨⟨hQP, hsyl, hQcard, -⟩, ⟨hlines, -⟩, htrans, -, -, hC0, hC0c, -, -, -, -, -, hC25,
    hC25c, hAC, hAn, hAc, hAe, hAcc, hAcl⟩ := R3E_Co3_full_five_centralizer_structures
  have hOK : ∀ i : Fin 31, i = 0 ∨ i = 25 →
      PrimePowOK 5 (Nat.card (co3P ⊓ centralizer ({co3FiveLine i} :
        Set (Equiv.Perm (Fin 276))) : Subgroup (Equiv.Perm (Fin 276)))) := by
    intro i hi
    rcases hi with rfl | rfl
    · rw [inf_comm, ← hC0, hC0c]
      exact primePowOK_five_300
    · rw [inf_comm, ← hC25, hC25c]
      exact primePowOK_five_1500
  have hrecmem : ∀ j : Fin 31, co3FiveRecordOf j = 0 ∨ co3FiveRecordOf j = 25 := by
    intro j
    unfold co3FiveRecordOf
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hz : co3FiveLine 25 ∈ co3FiveQ ∧ orderOf (co3FiveLine 25) = 5 := by
    have hmem : zpowers (co3FiveLine 25) ∈
        {H : Subgroup (Equiv.Perm (Fin 276)) | H ≤ co3FiveQ ∧ Nat.card H = 5} := by
      rw [hlines]
      exact ⟨25, rfl⟩
    exact ⟨hmem.1 (Subgroup.mem_zpowers _), by rw [← Nat.card_zpowers]; exact hmem.2⟩
  have hAexp : ∀ x ∈ co3FiveA, x ^ 5 = 1 := fun x hx => by
    have := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : co3FiveA)
    rw [hAe] at this
    exact congrArg Subtype.val this
  have hCz : co3P ⊓ centralizer ({co3FiveLine 25} : Set (Equiv.Perm (Fin 276))) =
      co3FiveC25 := by rw [hC25, inf_comm]
  have hm := co3_autModel hAut
  refine noSig_planes_of_record_extra hm (le_trans le_rfl (Nat.le_mul_of_pos_left _ (by norm_num)))
    Nat.prime_five (by norm_num) (Q := co3FiveQ) (by rw [hQcard]; norm_num) hQP hsyl hlines
    (fun j => ⟨co3FiveRecordOf j, ⟨_, (htrans j).1, (htrans j).2⟩, hOK _ (hrecmem j)⟩)
    (A := co3FiveA) (hAC.trans (hC25.le.trans inf_le_right)) (by rw [hAc]; norm_num) hAexp
    (z := co3FiveLine 25) (hm.le (hQP hz.1)) ?_ ?_ ?_ ?_ ?_
  · intro h1
    rw [h1, orderOf_one] at hz
    exact absurd hz.2 (by norm_num)
  · intro q hq
    have : q ∈ co3FiveC25 := hAC hq
    rw [hC25] at this
    exact this.1
  · intro c hc q hq
    rw [hCz] at hc
    have := hAn.conj_mem ⟨q, hAC hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨c, hc⟩
    exact Subgroup.mem_subgroupOf.1 this
  · rw [hCz]
    exact hAcl
  · rw [hCz]
    exact hAcc

theorem sporPlaneKill_Co3_five
    (hOut : SporadicOuterLeTwo) : SporPlaneKill .Co3 5 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
  have b₀ : NativeSporadic.Carrier .Co3 ≃* Spor .Co3 := b
  have eC : NativeSporadic.Carrier .Co3 ≃* co3P := co3PermEquiv
  exact sporPlaneKill_of_noSig_model hOut Nat.prime_five (by norm_num) (by decide)
    (eC.symm.trans b₀)
    (fun R Y hR hR9 hY3 hRY => co3Five_noSig CFSG.Sporadic.SmallOddCore.co3P_allInner R hR hR9 Y
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hY3) hRY) b₀ offPair_Co3


theorem sporPair_Co3_five
    (hOut : SporadicOuterLeTwo) : SporPair .Co3 5 :=
  sporPair_of_planeKill (sporPlaneKill_Co3_five hOut)

end CFSG.HardMathSupport.Dickson.I271
