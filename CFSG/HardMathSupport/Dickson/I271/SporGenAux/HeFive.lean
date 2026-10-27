module

public import CFSG.RankThree.PartOne.KS.HeFiveCentralizers
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.LinesGood
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThreeKill
public import Certificates.Certificate17301

public section

namespace CFSG.HardMathSupport.Dickson.I271

open Subgroup CFSG.Open CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.PartTwo.Sec4 CFSG.Blueprint CFSG.Sporadic.HeldB CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu

theorem heFive_pow_five
    {U : Equiv.Perm (Fin 8330)} (hU : U ∈ heFiveC0)
    (h0 : U * permOfArr 8330 heFiveQGens[0]! = permOfArr 8330 heFiveQGens[0]! * U)
    (h1 : U * permOfArr 8330 heFiveQGens[1]! = permOfArr 8330 heFiveQGens[1]! * U) :
    U ^ 5 = 1 := by
  have hcent : enumOK 8330 heFiveC0Gens heFiveKeys heFiveC0Cert = true :=
    centOKP_enum heFive_case0_check.2.1
  obtain ⟨i, hi, hrep⟩ := enumOK_exists_rep heFiveKeys_lt hcent hU
  have hcheck := allLt_spec Certificates.certificate17301 hi
  have hQv : ∀ l < heFiveQGens.size, validA 8330 heFiveQGens[l]! = true := fun l hl =>
    enumOK_gens_valid (linesOKG_parts heFive_lines_ok).1 hl
  have hq0 := rep_of_validA (hQv 0 (by simp [heFiveQGens]))
  have hq1 := rep_of_validA (hQv 1 (by simp [heFiveQGens]))
  by_cases hc : (commA 8330 heFiveC0Cert.pts[i]! heFiveQGens[0]! &&
      commA 8330 heFiveC0Cert.pts[i]! heFiveQGens[1]!) = true
  · rw [Bool.and_eq_true] at hc
    have hpow : eqA 8330 (powArr 8330 heFiveC0Cert.pts[i]! 5) (idA 8330) = true := by
      simpa [hc.1, hc.2] using hcheck
    exact (eqA_iff (rep_powArr hrep 5) rep_idA).1 hpow
  · exfalso
    apply hc
    rw [Bool.and_eq_true]
    exact ⟨(commA_iff hrep hq0).2 h0, (commA_iff hrep hq1).2 h1⟩

theorem heFive_noSig :
    ∀ Ê : Subgroup (MulAut ↥heP), IsElemAbelian 5 Ê → Nat.card Ê = 5 ^ 2 → NoSig 5 Ê := by
  obtain ⟨⟨hQP, hsyl, hQcard, -⟩, ⟨hlines, -⟩, htrans, hrec, ⟨hC0, hC0c⟩, -⟩ :=
    R3E_He_full_five_centralizer_structures
  have hOK0 : RankOK 5 (heAutGroup ⊓ centralizer ({heFiveLine 0} :
      Set (Equiv.Perm (Fin 8330))) : Subgroup (Equiv.Perm (Fin 8330))) := by
    rw [inf_comm, ← hC0]
    exact rankOK_of_primePowOK (by rw [hC0c]; exact primePowOK_five_600)
  have hz : heFiveLine 0 ∈ heFiveQ := by
    have hmem : zpowers (heFiveLine 0) ∈
        {H : Subgroup (Equiv.Perm (Fin 8330)) | H ≤ heFiveQ ∧ Nat.card H = 5} := by
      rw [hlines]
      exact ⟨0, rfl⟩
    exact hmem.1 (Subgroup.mem_zpowers _)
  refine noSig_planes_of_autModel_rank heAutModel heAutGroup_card_le Nat.prime_five (by norm_num)
    hsyl ?_
    (rankOK_of_lines Nat.prime_five heAutModel.le hsyl hlines (xs := fun j => heFiveLine j)
      (fun j => ⟨heFiveRecordOf j, ⟨_, (htrans j).1, (htrans j).2⟩, by rw [hrec j]; exact hOK0⟩))
  ·
    intro E hEQ hEel hEcard
    have hEQ' : E = heFiveQ :=
      Subgroup.eq_of_le_of_card_ge hEQ (by rw [hEcard, hQcard]; norm_num)
    subst hEQ'
    intro u hu hcop
    have huC0 : u ∈ heFiveC0 := by
      rw [hC0]
      exact ⟨Subgroup.mem_centralizer_iff.2 fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Subgroup.mem_centralizer_iff.1 hu.2 _ hz, hu.1⟩
    have hg : ∀ l, l < 2 → permOfArr 8330 heFiveQGens[l]! ∈ heFiveQ := fun l hl =>
      Subgroup.subset_closure (mem_permsA (gs := heFiveQGens) (k := l) (by simp [heFiveQGens]; omega))
    have hu5 : u ^ 5 = 1 :=
      heFive_pow_five huC0 (Subgroup.mem_centralizer_iff.1 hu.2 _ (hg 0 (by norm_num))).symm
        (Subgroup.mem_centralizer_iff.1 hu.2 _ (hg 1 (by norm_num))).symm
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hu5))


theorem sporPlaneKill_He_five
    (hOut : SporadicOuterLeTwo) : SporPlaneKill .He 5 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have b₀ : NativeSporadic.Carrier .He ≃* Spor .He := b
  have eH : NativeSporadic.Carrier .He ≃* heP := heEquivP
  exact sporPlaneKill_of_noSig_model hOut Nat.prime_five (by norm_num) (by decide)
    (eH.symm.trans b₀)
    (fun R Y hR hR9 hY3 hRY => heFive_noSig R hR hR9 Y
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hY3) hRY) b₀ offPair_He

theorem sporPair_He_five
    (hOut : SporadicOuterLeTwo) : SporPair .He 5 :=
  sporPair_of_planeKill (sporPlaneKill_He_five hOut)

end CFSG.HardMathSupport.Dickson.I271
