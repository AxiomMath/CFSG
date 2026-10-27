module

public import CFSG.RankThree.PartOne.KS.Ru
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.RecordExtra
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThreeKill

public section

namespace CFSG.HardMathSupport.Dickson.I271

open Subgroup CFSG.Open CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.PartTwo.Sec4 CFSG.Blueprint CFSG.Sporadic.RuSchreier

theorem ruFive_noSig :
    ∀ Ê : Subgroup (MulAut ↥ruP), IsElemAbelian 5 Ê → Nat.card Ê = 5 ^ 2 → NoSig 5 Ê := by
  obtain ⟨⟨hQP, hsyl, hQcard, -⟩, ⟨hlines, -⟩, htrans, hrecmem, -, ⟨hC0, hC0c⟩, ⟨hC1, hC1c⟩,
    ⟨hAC, hAn, hAP, hAc, hAe, hAcc, hAcl⟩, -⟩ := R3E_Ru_full_five_centralizer_structures
  have hOK : ∀ i : Fin 31, (i : ℕ) ∈ ({0, 1} : Finset ℕ) →
      PrimePowOK 5 (Nat.card (ruP ⊓ centralizer ({ruFiveLine i} :
        Set (Equiv.Perm (Fin 4060))) : Subgroup (Equiv.Perm (Fin 4060)))) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h0 | h1
    · have : i = 0 := Fin.ext h0
      subst this
      rw [inf_comm, ← hC0, hC0c]
      exact primePowOK_five_1000
    · have : i = 1 := Fin.ext h1
      subst this
      rw [inf_comm, ← hC1, hC1c]
      exact primePowOK_five_300
  have hz : ruFiveLine 0 ∈ ruFiveQ ∧ orderOf (ruFiveLine 0) = 5 := by
    have hmem : zpowers (ruFiveLine 0) ∈
        {H : Subgroup (Equiv.Perm (Fin 4060)) | H ≤ ruFiveQ ∧ Nat.card H = 5} := by
      rw [hlines]
      exact ⟨0, rfl⟩
    exact ⟨hmem.1 (Subgroup.mem_zpowers _), by rw [← Nat.card_zpowers]; exact hmem.2⟩
  have hAexp : ∀ x ∈ ruFiveA0, x ^ 5 = 1 := fun x hx => by
    have := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : ruFiveA0)
    rw [hAe] at this
    exact congrArg Subtype.val this
  have hCz : ruP ⊓ centralizer ({ruFiveLine 0} : Set (Equiv.Perm (Fin 4060))) = ruFiveC0 := by
    rw [hC0, inf_comm]
  have hm := ru_autModel
  refine noSig_planes_of_record_extra hm (le_trans le_rfl (Nat.le_mul_of_pos_left _ (by norm_num)))
    Nat.prime_five (by norm_num) (Q := ruFiveQ) (by rw [hQcard]; norm_num) hQP hsyl hlines
    (fun j => ⟨ruFiveRecordOf j, ⟨_, (htrans j).1, (htrans j).2⟩, hOK _ (hrecmem j)⟩)
    (A := ruFiveA0) hAP (by rw [hAc]; norm_num) hAexp
    (z := ruFiveLine 0) (hm.le (hQP hz.1)) ?_ ?_ ?_ ?_ ?_
  · intro h1
    rw [h1, orderOf_one] at hz
    exact absurd hz.2 (by norm_num)
  · intro q hq
    have : q ∈ ruFiveC0 := hAC hq
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

theorem sporPlaneKill_Ru_five
    (hOut : SporadicOuterLeTwo) : SporPlaneKill .Ru 5 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  have bP : ruP ≃* Spor .Ru := ruEquivP.symm.trans b
  have b₀ : NativeSporadic.Carrier .Ru ≃* Spor .Ru := b
  exact sporPlaneKill_of_noSig_model hOut Nat.prime_five (by norm_num) (by decide) bP
    (fun R Y hR hR9 hY3 hRY => ruFive_noSig R hR hR9 Y
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hY3) hRY) b₀ offPair_Ru


theorem sporPair_Ru_five
    (hOut : SporadicOuterLeTwo) : SporPair .Ru 5 :=
  sporPair_of_planeKill (sporPlaneKill_Ru_five hOut)

end CFSG.HardMathSupport.Dickson.I271
