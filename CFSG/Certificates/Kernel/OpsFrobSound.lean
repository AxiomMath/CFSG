module

public import Certificates.Data.Kernel.OpsFrob
public import CFSG.Certificates.Kernel.OpsV4Sound
import CFSG.Certificates.Kernel.OpsKSound

public section

namespace CFSG.KC.OpsFrob

open CFSG.SectionRank.Native CFSG.KC.OpsK CFSG.KC.LQT CFSG.KC.OpsLayK CFSG.KC.OpsV4

theorem frobCheck_of_sim {M V₀ V : Type} [Inhabited M] {O₀ : Ops M V₀} {O : Ops Nat V}
    (S : Sim O₀ O) {D : FrobData} (hp : D.prog.all (Op.lt D.nregs) = true)
    (ha : D.ra < D.nregs) (ht : D.rt < D.nregs) {a t : Nat}
    (hA : S.R (O₀.regsOf D.seedA D.seedB D.nregs D.prog)[D.ra]! a)
    (hT : S.R (O₀.regsOf D.seedA D.seedB D.nregs D.prog)[D.rt]! t)
    (hE : ∀ e, e ≤ 7 → S.E e) (htest : S.T D.test)
    (h : frobG O S.pw D.test a t = true) : O₀.frobCheck D = true := by
  unfold frobG at h
  rw [forceB_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have hc : ∀ i, i ≤ 7 → S.R (O₀.conjSeven (O₀.regsOf D.seedA D.seedB D.nregs D.prog)[D.ra]!
      (O₀.regsOf D.seedA D.seedB D.nregs D.prog)[D.rt]! i) (conj7G O S.pw a t i) := fun i hi =>
    S.mul (S.mul (S.pow hT (hE i hi)) hA) (S.pow hT (hE (7 - i) (Nat.sub_le 7 i)))
  unfold Ops.frobCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨hp, ha⟩, ht⟩, S.eq (S.mul hA hA) S.one h1⟩, S.eq (S.pow hT (hE 7 le_rfl)) S.one h2⟩,
    S.commOK hA (hc 1 (by omega)) h3⟩, S.commOK hA (hc 2 (by omega)) h4⟩,
    S.eq (hc 3 (by omega)) (S.mul (hc 1 (by omega)) hA) h5⟩,
    S.vne (S.vmul (S.unit htest) hA) (S.unit htest) h6⟩

theorem frobCheck_of_L {c : Lay} {d A B : Nat} {LA LB : List Char} {D : FrobData}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : D.seedA = String.ofList LA) (hsB : D.seedB = String.ofList LB)
    (h : frobL c A B D = true) : (ops3 d).frobCheck D = true := by
  subst hd
  unfold frobL at h
  rw [Snd.runC_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hprog, ha⟩, ht⟩, htest⟩, hrun⟩ := h
  obtain ⟨_, hlt⟩ := Snd.progOK_spec hprog
  have hL := Snd.lcorr_regs hc hp hA hB hsA hsB hprog
  have hlen := Snd.runL_initR_length c D.prog A B D.nregs
  exact frobCheck_of_sim (Sim.ofL3 c hc hp) hlt ha ht (hL.2 _ (by rw [hlen]; exact ha))
    (hL.2 _ (by rw [hlen]; exact ht)) (fun e he => (by omega : e < 65536)) htest hrun

end CFSG.KC.OpsFrob

end
