module

public import Certificates.Data.Kernel.OpsF2KMcertQ
public import CFSG.Certificates.Kernel.OpsF2KQSound
import CFSG.Certificates.Kernel.Misc.F2BfsRec2Sound

public section

namespace CFSG.KC.OpsF2K

open CFSG.KC.M1F2 CFSG.KLie.CT CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
open CFSG.KC.Misc.G24 (mulF2)
open CFSG.KC.F2BfsRec (mulF2_eq_mulF)

theorem mcertK_of_Q {d A B : Nat} {C : MCert} (h : mcertQ d A B C = true) :
    mcertK d A B C = true := by
  simp only [mcertQ, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hs, hexp⟩, hn⟩, hprog⟩, hf⟩ := h
  obtain ⟨hR, hbd⟩ := runQ_eq (n := C.nregs) hs hexp
  rw [hR] at hf
  simp only [mcertK, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨hs, hexp⟩, hn⟩, hprog⟩, ?_⟩
  rw [List.all_eq_true] at hf ⊢
  exact fun f hf' => factK_of_Q hbd f (hf f hf')

open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks.Native in
theorem e8Q_eq (d A B : Nat) (D : E8Data) : e8Q d A B D = e8K d A B D := by
  cases hs : seedsOK d A B
  · simp only [e8Q, e8K, hs, Bool.false_and]
  cases he : D.prog.all expOK
  · simp only [e8Q, e8K, hs, he, Bool.true_and, Bool.false_and]
  obtain ⟨hR, hbd⟩ := runQ_eq (n := D.nregs) hs he
  cases ho : decide (D.oh < 65536)
  · simp only [e8Q, e8K, ho, Bool.and_false, Bool.false_and]
  have ho' : D.oh < 2 ^ 16 := by
    have := of_decide_eq_true ho
    omega
  have ho1 : D.oh - 1 < 2 ^ 16 := by omega
  have h2 : 2 < 2 ^ 16 := by omega
  simp only [e8Q, e8K, hR, commQ_eq, conjQ_eq, mulF2_eq_mulF, pqK_getR hbd ho',
    pqK_getR hbd ho1, pqK_getR hbd h2]

open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks.Native in
theorem e8K_of_Q {d A B : Nat} {D : E8Data} (h : e8Q d A B D = true) : e8K d A B D = true := by
  rwa [← e8Q_eq]

end CFSG.KC.OpsF2K

end
