module

public import CFSG.RankThree.PartOne.KS.HeSevenCentralizers
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.RecordExtra
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.PrimePowSeven
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThreeKill
public import Certificates.Certificate17300

public section

namespace CFSG.HardMathSupport.Dickson.I271

open Subgroup CFSG.Open CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.PartTwo.Sec4 CFSG.Blueprint CFSG.Sporadic.HeldB

theorem heSeven_noSig :
    ∀ Ê : Subgroup (MulAut ↥heP), IsElemAbelian 7 Ê → Nat.card Ê = 7 ^ 2 → NoSig 7 Ê := by
  obtain ⟨⟨hQP, hsyl, hQcard, -⟩, ⟨hlines, -⟩, htrans, hrecmem, -, ⟨hC0, hC0c⟩, ⟨hC1, hC1c⟩,
    ⟨hC2, hC2c⟩, ⟨hA0C, hA0n, hA0P, hA0c, hA0e, hAcard, hAcent⟩, -, -⟩ :=
    R3E_He_full_seven_centralizer_structures
  have hmem2 : CFSG.Monster.B.Co2.permOfArr 8330 heSevenC1Gens[2]! ∈
      permsA 8330 heSevenC1Gens :=
    mem_permsA (gs := heSevenC1Gens) (k := 2) (by simp [heSevenC1Gens])
  have hw : ∃ c ∈ heSevenC1, orderOf c = 4 :=
    ⟨CFSG.Monster.B.Co2.permOfArr 8330 heSevenC1Gens[2]!,
      Subgroup.subset_closure hmem2,
      orderOf_permOfArr_of_orderFourOK Certificates.certificate17300⟩
  have hOK : ∀ i : Fin 57, (i : ℕ) ∈ ({0, 1, 2} : Finset ℕ) →
      RankOK 7 (heAutGroup ⊓ centralizer ({heSevenLine i} :
        Set (Equiv.Perm (Fin 8330))) : Subgroup (Equiv.Perm (Fin 8330))) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h0 | h1 | h2
    · have : i = 0 := Fin.ext h0
      subst this
      rw [inf_comm, ← hC0]
      exact rankOK_of_primePowOK (by rw [hC0c]; exact primePowOK_seven_2058)
    · have : i = 1 := Fin.ext h1
      subst this
      rw [inf_comm, ← hC1]
      exact rankOK_of_two_witness hC1c primePowTwo_seven_1176 hw
    · have : i = 2 := Fin.ext h2
      subst this
      rw [inf_comm, ← hC2]
      exact rankOK_of_primePowOK (by rw [hC2c]; exact primePowOK_seven_98)
  have hz : heSevenLine 0 ∈ heSevenQ ∧ orderOf (heSevenLine 0) = 7 := by
    have hmem : zpowers (heSevenLine 0) ∈
        {H : Subgroup (Equiv.Perm (Fin 8330)) | H ≤ heSevenQ ∧ Nat.card H = 7} := by
      rw [hlines]
      exact ⟨0, rfl⟩
    exact ⟨hmem.1 (Subgroup.mem_zpowers _), by rw [← Nat.card_zpowers]; exact hmem.2⟩
  have hAexp : ∀ x ∈ heSevenA0, x ^ 7 = 1 := fun x hx => by
    have := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : heSevenA0)
    rw [hA0e] at this
    exact congrArg Subtype.val this
  have hCz : heAutGroup ⊓ centralizer ({heSevenLine 0} : Set (Equiv.Perm (Fin 8330))) =
      heSevenC0 := by rw [hC0, inf_comm]
  refine noSig_planes_of_record_extra_rank heAutModel heAutGroup_card_le (by norm_num)
    (by norm_num) (Q := heSevenQ) (by rw [hQcard]; norm_num) hQP hsyl hlines
    (fun j => ⟨heSevenRecordOf j, ⟨_, (htrans j).1, (htrans j).2⟩, hOK _ (hrecmem j)⟩)
    (A := heSevenA0) hA0P (by rw [hA0c]; norm_num) hAexp
    (z := heSevenLine 0) (heAutModel.le (hQP hz.1)) ?_ ?_ ?_ ?_ ?_
  · intro h1
    rw [h1, orderOf_one] at hz
    exact absurd hz.2 (by norm_num)
  · intro q hq
    have : q ∈ heSevenC0 := hA0C hq
    rw [hC0] at this
    exact this.1
  · intro c hc q hq
    rw [hCz] at hc
    have := hA0n.conj_mem ⟨q, hA0C hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨c, hc⟩
    exact Subgroup.mem_subgroupOf.1 this
  · rw [hCz]
    exact hAcent
  · rw [hCz]
    exact hAcard


theorem sporPlaneKill_He_seven
    (hOut : SporadicOuterLeTwo) : SporPlaneKill .He 7 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have b₀ : NativeSporadic.Carrier .He ≃* Spor .He := b
  have eH : NativeSporadic.Carrier .He ≃* heP := heEquivP
  exact sporPlaneKill_of_noSig_model hOut (by norm_num) (by norm_num) (by decide)
    (eH.symm.trans b₀)
    (fun R Y hR hR9 hY3 hRY => heSeven_noSig R hR hR9 Y
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hY3) hRY) b₀ offPair_He

theorem sporPair_He_seven
    (hOut : SporadicOuterLeTwo) : SporPair .He 7 :=
  sporPair_of_planeKill (sporPlaneKill_He_seven hOut)

end CFSG.HardMathSupport.Dickson.I271
