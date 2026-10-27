module

public import Certificates.Data.Kernel.OpsW4C
public import Certificates.Data.Kernel.OpsW4N
public import CFSG.Certificates.Kernel.OpsRenLSound

public section

namespace CFSG.KC.OpsW4N

open CFSG.SectionRank.Native CFSG.KC.LQT CFSG.KC.OpsLayK

theorem w4L_of_chunks {c : Lay} {A B : Nat} {D : Data} {inv : Nat} {cs : List RChunk}
    {S : Nat → List Nat}
    (hpre : (progOK D.nregs D.prog && D.outs.all (decide <| · < D.nregs) &&
      decide (inv < D.nregs) && D.tests.all (decide <| · < c.d)) = true)
    (hren : renOK (D.outs ++ [inv]) D.prog cs = true) (h0 : S 0 = [A, B])
    (hch : ∀ i < cs.length, chunkV c (cs.getD i (0, [], [])) (S i) (S (i + 1)) = true)
    (hfin : w4FinL c ((S cs.length).take D.outs.length) (getR c (S cs.length) D.outs.length)
      D.tests = true) :
    w4L c A B D inv = true := by
  have hp := hpre
  simp only [Bool.and_eq_true] at hp
  obtain ⟨hn, hlt⟩ := Snd.progOK_spec hp.1.1.1
  have e := renOK_sound hn hlt hren h0 hch
  rw [List.map_append, List.map_singleton] at e
  have ex : D.outs.map (getR c (Snd.runL c D.prog (initR c A B D.nregs))) =
      (S cs.length).take D.outs.length := by
    rw [← e]
    simp
  have eT : getR c (Snd.runL c D.prog (initR c A B D.nregs)) inv =
      getR c (S cs.length) D.outs.length := by
    rw [← e]
    simp [getR, List.getD_eq_getElem?_getD]
  unfold w4L
  rw [Snd.runC_eq, hpre, Bool.true_and]
  dsimp only
  rw [ex, eT]
  exact hfin

end CFSG.KC.OpsW4N

end
