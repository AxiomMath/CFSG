module

public import CFSG.Certificates.Kernel.Spor.PtCheck

public section

namespace CFSG.KS.PtC

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def commPt (n w a b : Nat) : Bool :=
  allN n (fun i => Nat.beq (rd w a (rd w b i)) (rd w b (rd w a i)))

@[expose] noncomputable def preT (n w a b : Nat) : Bool :=
  (((List.range n).filter fun x => !Nat.beq (rd w b x) x).take 8).all fun x =>
    !decide (x < n) || Nat.beq (rd w a (rd w b x)) (rd w b (rd w a x))

theorem beq_pcomp_comm {n w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (a b : Nat) :
    Nat.beq (pcomp n w (mask w) a b) (pcomp n w (mask w) b a) = commPt n w a b :=
  beq_pcomp_pcomp hn hw a b b a

theorem commPt_pre (n w a b : Nat) (L : List Nat) :
    commPt n w a b = ((L.all fun x => !decide (x < n) ||
      Nat.beq (rd w a (rd w b x)) (rd w b (rd w a x))) && commPt n w a b) := by
  symm
  cases h : commPt n w a b
  · exact Bool.and_false _
  · rw [Bool.and_true, List.all_eq_true]
    intro x _
    unfold commPt at h
    rw [Raw.Orb.allN_iff] at h
    by_cases hx : x < n
    · rw [h x hx, Bool.or_true]
    · simp [hx]

theorem commPt_eq_preT (n w a b : Nat) : commPt n w a b = (preT n w a b && commPt n w a b) :=
  commPt_pre n w a b _

theorem preT_of {n w a b : Nat} (h : commPt n w a b = true) : preT n w a b = true := by
  have e := commPt_eq_preT n w a b
  rw [h, Bool.and_true] at e
  exact e.symm

theorem beq_pcomp_comm_pre {n w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (a b : Nat) :
    Nat.beq (pcomp n w (mask w) a b) (pcomp n w (mask w) b a) =
      (preT n w a b && commPt n w a b) :=
  (beq_pcomp_comm hn hw a b).trans (commPt_eq_preT n w a b)

end CFSG.KS.PtC

end
