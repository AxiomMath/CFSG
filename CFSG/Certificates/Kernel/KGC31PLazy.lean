module

public import Certificates.Data.Kernel.KGC31PSplit
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.KGC31P

open CFSG.KC.Enum CFSG.KS

variable {n w : Nat}

theorem pgL_eq (hn : n < 2 ^ 32) (g t y : Nat) :
    pgL n w g t y = pg w (mask w) (pc n w g t) y := by
  unfold pgL
  cases h : Nat.blt y n
  · rfl
  · rw [cond_true, pc, PF.pg_pcomp hn (Eq.mp Nat.blt_eq h)]

theorem pgL2_eq (hn : n < 2 ^ 32) (a g t y : Nat) :
    pgL2 n w a g t y = pg w (mask w) (pc n w a (pc n w g t)) y := by
  unfold pgL2
  cases h : Nat.blt y n
  · rfl
  · rw [cond_true, pgL_eq hn]
    unfold pc
    rw [PF.pg_pcomp (p := a) hn (Eq.mp Nat.blt_eq h)]

theorem beq_pc_pc (hw : 0 < w) (hn : n < 2 ^ 32) (a b c d : Nat) :
    Nat.beq (pc n w a b) (pc n w c d) =
      allN n (fun i => Nat.beq (pg w (mask w) a (pg w (mask w) b i))
        (pg w (mask w) c (pg w (mask w) d i))) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, Raw.Orb.allN_iff]
  constructor
  · intro h i hi
    have e := congrArg (fun X => pg w (mask w) X i) h
    simp only [pc, PF.pg_pcomp hn hi] at e
    rw [e]
    exact Nat.beq_refl _
  · intro h
    unfold pc
    apply PF.eq_of_fld hw (PF.fld_pcomp (w := w) a b hn)
    refine PF.fld_congr (PF.fld_pcomp (w := w) c d hn) fun i => ?_
    by_cases hi : i < n
    · simp only [hi, if_true]
      exact (Nat.eq_of_beq_eq_true (h i hi)).symm
    · simp [hi]

theorem pcommL_eq (hw : 0 < w) (hn : n < 2 ^ 32) (gs : List Nat) (g t : Nat) :
    pcommL n w gs g t = pcommAll n w gs (pc n w g t) := by
  unfold pcommL pcommAll
  congr 1
  funext h
  rw [beq_pc_pc hw hn]
  simp only [pgL_eq hn]

theorem countP_all_eq_L {P : Nat → Bool} {fL : Nat → Nat → Bool}
    (hf : ∀ g t, fL g t = P (pc n w g t)) (Ls : List (List Nat)) (g : Nat) (hne : Ls ≠ []) :
    (pfilterProducts n w (fun _ => true) Ls g []).countP P = pcountL n w fL Ls g := by
  rw [pfilter_countP, List.countP_nil, Nat.zero_add]
  exact (pcountL_eq n w (f := fun x => true && P x) (fun g t => by rw [hf, Bool.true_and]) Ls g
    hne).symm

theorem pord2_pt (hsz : n < 16777216 ∧ n + 1 < 2 ^ w) {x : Nat} (h : pord n w 2 x = true) :
    allN n (fun i => Nat.beq (pg w (mask w) x (pg w (mask w) x i)) i) = true := by
  have hn : n < 2 ^ 32 := by omega
  unfold pord at h
  rw [Bool.and_eq_true] at h
  have e2 : ppw n w x 2 = pc n w x (pc n w x (pidn n w)) := rfl
  have e := Nat.eq_of_beq_eq_true h.1
  rw [e2] at e
  rw [Raw.Orb.allN_iff]
  intro i hi
  have e' := congrArg (fun X => pg w (mask w) X i) e
  simp only [pc, PF.pg_pcomp hn hi, PF.pg_pidn hsz.1 hsz.2 hi] at e'
  rw [e']
  exact Nat.beq_refl _

end CFSG.KC.KGC31P

end
