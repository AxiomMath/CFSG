module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThree
public import Certificates.Certificate12617

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census219

open scoped commutatorElement
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.AGLEmbeddingD2.Wilson.ThetaSpor CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He
  CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier Subgroup Equiv

theorem heTc_parts :
    tcOK 8330 7 heBase heThreeBA heTcD (heTcCQ ()) (heTcCK ()) (heTcCS ()) = true ∧
    lettersOK 2 heTcU0 = true ∧ lettersOK 2 heTcV0 = true ∧ lettersOK 2 heTcU1 = true ∧
    lettersOK 2 heTcV1 = true ∧ lettersOK 2 heTcK0 = true ∧ lettersOK 2 heTcK1 = true ∧
    lettersOK 2 heTcR1 = true ∧ lettersOK 2 heTcR2 = true ∧ lettersOK 2 heTcR3 = true ∧
    lettersOK 2 heTcR4 = true ∧ lettersOK 2 heTcR5 = true ∧ lettersOK 2 heTcR6 = true ∧
    lettersOK 2 heTcS1 = true ∧ lettersOK 2 heTcS2 = true ∧
    enumOK 8330 heSylA heBase (heTcCY ()) = true ∧ (heTcCY ()).pts.size = 27 ∧
    allLt (heTcCY ()).pts.size
      (fun k => eqA 8330 (powArr 8330 (heTcCY ()).pts[k]! 3) (idA 8330)) = true := by
  have h := Certificates.certificate12617
  simp only [heTcOK, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  exact h

theorem heBase_lt : ∀ p ∈ heBase, p < 8330 := by decide

@[expose] noncomputable def heTcQ : Subgroup (Perm (Fin 8330)) := closure (permsA 8330 heTcD.gQ)

theorem heTc_spec :
    permOfArr 8330 heThreeBA ∈ heTcQ ∧ CFSG.IsQuasisimple ↥heTcQ ∧
      CFSG.RankThree.PartTwo.Sec4.IsTripleCover ↥heTcQ (alternatingGroup (Fin 7)) :=
  tcOK_spec heBase_lt (by norm_num) heTc_parts.1

theorem card_heTcQ : Nat.card heTcQ = 7560 := by
  have h := (tcOK_parts heTc_parts.1).1
  rw [heTcQ, (enumOK_spec heBase_lt h).2.1, (tcOK_parts heTc_parts.1).2.1]
  decide

@[expose] noncomputable def heSylS : Subgroup (Perm (Fin 8330)) := closure (permsA 8330 heSylA)

theorem heSyl_exp {q : Perm (Fin 8330)} (hq : q ∈ heSylS) :
    q ^ 3 = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hSe, -, hpow⟩ := heTc_parts
  obtain ⟨k, hk, hkg⟩ := enumOK_exists_rep heBase_lt hSe hq
  exact (eqA_iff (rep_powArr hkg 3) rep_idA).1 (allLt_spec hpow hk)

theorem card_heSylS : Nat.card heSylS = 27 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hSe, hsz, -⟩ := heTc_parts
  rw [heSylS, (enumOK_spec heBase_lt hSe).2.1, hsz]

section Centralizer

set_option linter.unusedSectionVars false


theorem bOf_eq : bOf heThreeWordsA = permOfArr 8330 heThreeBA :=
  (CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_bOf bigDataA)).symm

theorem comm_mem_heP {a b : Perm (Fin 8330)} (ha : a ∈ heP) (hb : b ∈ heP) : ⁅a, b⁆ ∈ heP := by
  rw [commutatorElement_def]
  exact heP.mul_mem (heP.mul_mem (heP.mul_mem ha hb) (heP.inv_mem ha)) (heP.inv_mem hb)

theorem heTcD_cu0 : heTcD.cu[0]! = heThreeArr heTcU0 := by simp [heTcD]
theorem heTcD_cu1 : heTcD.cu[1]! = heThreeArr heTcU1 := by simp [heTcD]
theorem heTcD_cv0 : heTcD.cv[0]! = heThreeArr heTcV0 := by simp [heTcD]
theorem heTcD_cv1 : heTcD.cv[1]! = heThreeArr heTcV1 := by simp [heTcD]

theorem heTcD_gQ0 : heTcD.gQ[0]! = commutatorA 8330 (heThreeArr heTcU0) (heThreeArr heTcV0) := by
  simp [heTcD]
theorem heTcD_gQ1 : heTcD.gQ[1]! = commutatorA 8330 (heThreeArr heTcU1) (heThreeArr heTcV1) := by
  simp [heTcD]

theorem heTcQ_le_heP : heTcQ ≤ heP := by
  obtain ⟨hQ, hl1, hl2, hl3, hl4, -⟩ := heTc_parts
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcc, -⟩ := tcOK_parts hQ
  rw [heTcQ, closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk2 : k < 2 := hk
  have hv := allLt_spec hcc hk
  simp only [Bool.and_eq_true] at hv
  obtain ⟨⟨⟨⟨hu, hv'⟩, -⟩, -⟩, -⟩ := hv
  interval_cases k
  · rw [heTcD_cu0] at hu
    rw [heTcD_cv0] at hv'
    have h1 := rep_commutatorA (n := 8330) (g := heThreeArr heTcU0) (h := heThreeArr heTcV0) hu hv'
    have e1 := CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_heThreeP (w := heTcU0) hl1)
    have e2 := CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_heThreeP (w := heTcV0) hl2)
    beta_reduce
    rw [heTcD_gQ0, CFSG.RankThree.Native.permOfArr_eq_of_rep h1, e1, e2]
    exact comm_mem_heP (heThreeP_mem _) (heThreeP_mem _)
  · rw [heTcD_cu1] at hu
    rw [heTcD_cv1] at hv'
    have h1 := rep_commutatorA (n := 8330) (g := heThreeArr heTcU1) (h := heThreeArr heTcV1) hu hv'
    have e1 := CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_heThreeP (w := heTcU1) hl3)
    have e2 := CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_heThreeP (w := heTcV1) hl4)
    beta_reduce
    rw [heTcD_gQ1, CFSG.RankThree.Native.permOfArr_eq_of_rep h1, e1, e2]
    exact comm_mem_heP (heThreeP_mem _) (heThreeP_mem _)

theorem heTcQ_comm {y : Perm (Fin 8330)} (hy : y ∈ heTcQ) :
    Commute y (permOfArr 8330 heThreeBA) := by
  obtain ⟨hQ, -⟩ := heTc_parts
  obtain ⟨-, -, hxv, -, -, hxcomm, -⟩ := tcOK_parts hQ
  have hrx : Rep 8330 heThreeBA (permOfArr 8330 heThreeBA) := rep_of_validA hxv
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    exact (commA_iff (rep_of_validA (enumOK_gens_valid (tcOK_parts hQ).1 hi)) hrx).1
      (allLt_spec hxcomm hi)
  | one => exact Commute.one_left _
  | mul y z _ _ hy hz => exact hy.mul_left hz
  | inv y _ hy => exact hy.inv_left

theorem heTcQ_eq : heTcQ = centralizerIn heP (bOf heThreeWordsA) := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro y hy
    refine (mem_centralizerIn).2 ⟨heTcQ_le_heP hy, ?_⟩
    rw [bOf_eq]
    exact (heTcQ_comm hy).eq
  · rw [card_cent_A, card_heTcQ]

theorem heSylA_0 : heSylA[0]! = heThreeArr heTcS1 := by simp [heSylA]
theorem heSylA_1 : heSylA[1]! = heThreeArr heTcS2 := by simp [heSylA]

theorem heSylS_le_heP : heSylS ≤ heP := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hs1, hs2, -⟩ := heTc_parts
  rw [heSylS, closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk2 : k < 2 := hk
  interval_cases k
  · beta_reduce
    rw [heSylA_0, CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_heThreeP hs1)]
    exact heThreeP_mem _
  · beta_reduce
    rw [heSylA_1, CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_heThreeP hs2)]
    exact heThreeP_mem _

end Centralizer

end CFSG.AGLEmbeddingD2.Wilson.Census219
