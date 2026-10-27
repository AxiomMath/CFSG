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

theorem hsFive_noSig :
    ∀ Ê : Subgroup (MulAut ↥hs100P), IsElemAbelian 5 Ê → Nat.card Ê = 5 ^ 2 → NoSig 5 Ê := by
  obtain ⟨⟨hQP, hsyl, hQcard, -⟩, ⟨hlines, -⟩, htrans, hrecmem, -, ⟨hC0, hC0c⟩, ⟨hC2, hC2c⟩,
    ⟨hC23, hC23c⟩, -, ⟨hA23C, hA23n, hA23P, hA23c, hA23e, hAcard, hAcent⟩, -⟩ :=
    R3E_HS_full_five_centralizer_structures
  have hOK : ∀ i : Fin 31, (i : ℕ) ∈ ({0, 2, 23} : Finset ℕ) →
      PrimePowOK 5 (Nat.card (hs100R ⊓ centralizer ({hs100FiveLine i} :
        Set (Equiv.Perm (Fin 100))) : Subgroup (Equiv.Perm (Fin 100)))) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h0 | h2 | h23
    · have : i = 0 := Fin.ext h0
      subst this
      rw [inf_comm, ← hC0, hC0c]
      exact primePowOK_five_50
    · have : i = 2 := Fin.ext h2
      subst this
      rw [inf_comm, ← hC2, hC2c]
      exact primePowOK_five_600
    · have : i = 23 := Fin.ext h23
      subst this
      rw [inf_comm, ← hC23, hC23c]
      exact primePowOK_five_1000
  have hz : hs100FiveLine 23 ∈ hs100FiveQ ∧ orderOf (hs100FiveLine 23) = 5 := by
    have hmem : zpowers (hs100FiveLine 23) ∈
        {H : Subgroup (Equiv.Perm (Fin 100)) | H ≤ hs100FiveQ ∧ Nat.card H = 5} := by
      rw [hlines]
      exact ⟨23, rfl⟩
    exact ⟨hmem.1 (Subgroup.mem_zpowers _), by rw [← Nat.card_zpowers]; exact hmem.2⟩
  have hAexp : ∀ x ∈ hs100FiveA23, x ^ 5 = 1 := fun x hx => by
    have := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : hs100FiveA23)
    rw [hA23e] at this
    exact congrArg Subtype.val this
  have hCz : hs100R ⊓ centralizer ({hs100FiveLine 23} : Set (Equiv.Perm (Fin 100))) =
      hs100FiveC23 := by rw [hC23, inf_comm]
  refine noSig_planes_of_record_extra CFSG.RankThree.PartOne.hs_autModel CFSG.RankThree.PartOne.hs_card_le Nat.prime_five (by norm_num)
    (Q := hs100FiveQ) (by rw [hQcard]; norm_num) hQP hsyl hlines
    (fun j => ⟨hs100FiveRecordOf j, ⟨_, (htrans j).1, (htrans j).2⟩, hOK _ (hrecmem j)⟩)
    (A := hs100FiveA23) hA23P (by rw [hA23c]; norm_num) hAexp
    (z := hs100FiveLine 23) (CFSG.RankThree.PartOne.hs_autModel.le (hQP hz.1)) ?_ ?_ ?_ ?_ ?_
  · intro h1
    rw [h1, orderOf_one] at hz
    exact absurd hz.2 (by norm_num)
  · intro q hq
    have : q ∈ hs100FiveC23 := hA23C hq
    rw [hC23] at this
    exact this.1
  · intro c hc q hq
    rw [hCz] at hc
    have := hA23n.conj_mem ⟨q, hA23C hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨c, hc⟩
    exact Subgroup.mem_subgroupOf.1 this
  · rw [hCz]
    exact hAcent
  · rw [hCz]
    exact hAcard

theorem sporPlaneKill_HS_five
    (hOut : SporadicOuterLeTwo) : SporPlaneKill .HS 5 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  have b₀ : NativeSporadic.Carrier .HS ≃* Spor .HS := b
  have eH : NativeSporadic.Carrier .HS ≃* hs100P := hs100Equiv
  exact sporPlaneKill_of_noSig_model hOut Nat.prime_five (by norm_num) (by decide)
    (eH.symm.trans b₀)
    (fun R Y hR hR9 hY3 hRY => hsFive_noSig R hR hR9 Y
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hY3) hRY) b₀ offPair_HS


theorem sporPair_HS_five
    (hOut : SporadicOuterLeTwo) : SporPair .HS 5 :=
  sporPair_of_planeKill (sporPlaneKill_HS_five hOut)

end CFSG.HardMathSupport.Dickson.I271
