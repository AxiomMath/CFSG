module

public import CFSG.RankThree.PartOne.KS.HSMcL
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.RecordExtra
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThreeKill

public section

namespace CFSG.HardMathSupport.Dickson.I271

open Subgroup CFSG.Open CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.PartTwo.Sec4 CFSG.Blueprint

theorem mclFive_noSig :
    ∀ Ê : Subgroup (MulAut ↥mcl275P), IsElemAbelian 5 Ê → Nat.card Ê = 5 ^ 2 → NoSig 5 Ê := by
  obtain ⟨⟨hQP, hsyl, hQcard, -⟩, ⟨hlines, -⟩, htrans, hrecmem, -, ⟨hC0, hC0c⟩, ⟨hC1, hC1c⟩,
    -, ⟨hA1C, hA1n, hA1P, hA1c, hA1e, hAcard, hAcent⟩⟩ :=
    R3E_McL_full_five_centralizer_structures
  have hOK : ∀ i : Fin 31, (i : ℕ) ∈ ({0, 1} : Finset ℕ) →
      PrimePowOK 5 (Nat.card (mcl275R ⊓ centralizer ({mcl275FiveLine i} :
        Set (Equiv.Perm (Fin 275))) : Subgroup (Equiv.Perm (Fin 275)))) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h0 | h1
    · have : i = 0 := Fin.ext h0
      subst this
      rw [inf_comm, ← hC0, hC0c]
      exact primePowOK_five_50
    · have : i = 1 := Fin.ext h1
      subst this
      rw [inf_comm, ← hC1, hC1c]
      exact primePowOK_five_1500
  have hz : mcl275FiveLine 1 ∈ mcl275FiveQ ∧ orderOf (mcl275FiveLine 1) = 5 := by
    have hmem : zpowers (mcl275FiveLine 1) ∈
        {H : Subgroup (Equiv.Perm (Fin 275)) | H ≤ mcl275FiveQ ∧ Nat.card H = 5} := by
      rw [hlines]
      exact ⟨1, rfl⟩
    exact ⟨hmem.1 (Subgroup.mem_zpowers _), by rw [← Nat.card_zpowers]; exact hmem.2⟩
  have hAexp : ∀ x ∈ mcl275FiveA1, x ^ 5 = 1 := fun x hx => by
    have := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : mcl275FiveA1)
    rw [hA1e] at this
    exact congrArg Subtype.val this
  have hCz : mcl275R ⊓ centralizer ({mcl275FiveLine 1} : Set (Equiv.Perm (Fin 275))) =
      mcl275FiveC1 := by rw [hC1, inf_comm]
  refine noSig_planes_of_record_extra CFSG.RankThree.PartOne.mcl_autModel
    CFSG.RankThree.PartOne.mcl_card_le Nat.prime_five (by norm_num)
    (Q := mcl275FiveQ) (by rw [hQcard]; norm_num) hQP hsyl hlines
    (fun j => ⟨mcl275FiveRecordOf j, ⟨_, (htrans j).1, (htrans j).2⟩, hOK _ (hrecmem j)⟩)
    (A := mcl275FiveA1) hA1P (by rw [hA1c]; norm_num) hAexp
    (z := mcl275FiveLine 1) (CFSG.RankThree.PartOne.mcl_autModel.le (hQP hz.1)) ?_ ?_ ?_ ?_ ?_
  · intro h1
    rw [h1, orderOf_one] at hz
    exact absurd hz.2 (by norm_num)
  · intro q hq
    have : q ∈ mcl275FiveC1 := hA1C hq
    rw [hC1] at this
    exact this.1
  · intro c hc q hq
    rw [hCz] at hc
    have := hA1n.conj_mem ⟨q, hA1C hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨c, hc⟩
    exact Subgroup.mem_subgroupOf.1 this
  · rw [hCz]
    exact hAcent
  · rw [hCz]
    exact hAcard

theorem sporPlaneKill_McL_five
    (hOut : SporadicOuterLeTwo) : SporPlaneKill .McL 5 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  have b₀ : NativeSporadic.Carrier .McL ≃* Spor .McL := b
  have eM : NativeSporadic.Carrier .McL ≃* mcl275P := mcl275Equiv
  exact sporPlaneKill_of_noSig_model hOut Nat.prime_five (by norm_num) (by decide)
    (eM.symm.trans b₀)
    (fun R Y hR hR9 hY3 hRY => mclFive_noSig R hR hR9 Y
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hY3) hRY) b₀ offPair_McL


theorem sporPair_McL_five
    (hOut : SporadicOuterLeTwo) : SporPair .McL 5 :=
  sporPair_of_planeKill (sporPlaneKill_McL_five hOut)

end CFSG.HardMathSupport.Dickson.I271
