module

public import Certificates.Data.Kernel.TcK
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.TcNative
public import CFSG.Certificates.Kernel.B3S3KSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.TcK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K
open CFSG.AGLEmbeddingD2.Wilson.Census219 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
  CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.Certificates.Native

theorem memK_spec {N : Nat} {T : Nat → Nat} {A : Nat} (h : memK N T A = true) :
    ∃ i < N, A = T i := by
  unfold memK at h
  induction N with
  | zero => exact absurd h Bool.false_ne_true
  | succ N ih =>
    change CFSG.KLie.CT.orB (Nat.beq A (T N)) (CFSG.KLie.CT.anyN N fun i => Nat.beq A (T i)) =
      true at h
    unfold CFSG.KLie.CT.orB at h
    cases hb : Nat.beq A (T N)
    · rw [hb] at h
      obtain ⟨i, hi, e⟩ := ih h
      exact ⟨i, by omega, e⟩
    · exact ⟨N, by omega, Nat.eq_of_beq_eq_true hb⟩

theorem eqA_refl' (n : Nat) (t : Array Nat) : eqA n t t = true := by
  unfold eqA
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro i _
  exact beq_self_eq_true _

theorem any_of_memK {n w N A : Nat} {c : ArrCert} {T : Nat → Nat} (hs : c.pts.size = N)
    (hp : ∀ i < N, c.pts[i]! = unpack n w (T i)) (h : memK N T A = true) :
    c.pts.toList.any (eqA n (unpack n w A)) = true := by
  obtain ⟨i, hi, e⟩ := memK_spec h
  rw [List.any_eq_true]
  refine ⟨c.pts[i]!, ?_, ?_⟩
  · rw [getElem!_pos c.pts i (by omega)]
    exact Array.getElem_mem_toList _
  · rw [hp i hi, ← e]
    exact eqA_refl' _ _

theorem memK_eq {n w N A : Nat} {c : ArrCert} {T : Nat → Nat} (hw : szOK n w = true)
    (hs : c.pts.size = N) (hp : ∀ i < N, c.pts[i]! = unpack n w (T i))
    (hT : ∀ i < N, permB n w (T i) = true) (hA : permB n w A = true) :
    c.pts.toList.any (eqA n (unpack n w A)) = memK N T A := by
  rw [toList_of hs hp, List.any_map]
  unfold memK
  rw [CFSG.KC.BfsPin.anyN_eq]
  exact any_range_congr fun i hi => eqA_unpack' hw hA (hT i hi)

theorem tcOK_of_K {n w m ngQ ngK NQ NK NS X : Nat} {ps : List Nat} {x : Array Nat} {D : TcData}
    {cQ cK cS : ArrCert} {GQ CU CV GK R TQ TK : Nat → Nat} {sig : Nat → Nat → Nat}
    (hw : szOK n w = true) (hx : x = unpack n w X)
    (hQ : BindA n w D.gQ ngQ GQ) (hU : BindA n w D.cu ngQ CU) (hV : BindA n w D.cv ngQ CV)
    (hKb : BindA n w D.gK ngK GK) (hR : BindA n w D.reps m R)
    (hsz : D.sig.size = ngQ) (hsig : ∀ i < ngQ, ∀ j < m, (D.sig[i]!)[j]! = sig i j)
    (heQ : enumOK n D.gQ ps cQ = true) (hsQ : cQ.pts.size = NQ)
    (hpQ : ∀ i < NQ, cQ.pts[i]! = unpack n w (TQ i)) (hTQ : ∀ i < NQ, permB n w (TQ i) = true)
    (heK : enumOK n D.gK ps cK = true) (hsK : cK.pts.size = NK)
    (hpK : ∀ i < NK, cK.pts[i]! = unpack n w (TK i)) (hTK : ∀ i < NK, permB n w (TK i) = true)
    (heS : enumOK m D.sig (List.range m) cS = true) (hsS : cS.pts.size = NS)
    (h : tcRestK n w m X ngQ GQ CU CV ngK GK R sig NQ TQ NK TK NS = true) :
    tcOK n m ps x D cQ cK cS = true := by
  subst hx
  unfold tcRestK at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩, c14⟩ := h
  have hGQ : ∀ i < ngQ, permB n w (GQ i) = true := fun i hi =>
    (Bool.and_eq_true_iff.1 (Orb.allN_iff.1 c5 i hi)).1
  have hRp : ∀ j < m, permB n w (R j) = true := fun j hj =>
    (Bool.and_eq_true_iff.1 (Orb.allN_iff.1 c10 j hj)).1
  have g2 : (cQ.pts.size == 3 * (m.factorial / 2)) = true :=
    beq_iff_eq.2 (hsQ.trans (Nat.eq_of_beq_eq_true c1))
  have g3 : validA n (unpack n w X) = true := validA_of c2
  have g4 : eqA n (powArr n (unpack n w X) 3) (idA n) = true := by
    rw [powEq_id hw c2 3]
    exact c3
  have g5 : eqA n (unpack n w X) (idA n) = false := by
    rw [eqA_id hw c2]
    exact c4
  have g6 : allLt D.gQ.size (fun i => commA n D.gQ[i]! (unpack n w X)) = true := by
    rw [CFSG.Monster.B.Co2.allLt_iff, hQ.1]
    intro i hi
    rw [hQ.2 i hi]
    show eqA n (compA n (unpack n w (GQ i)) (unpack n w X))
      (compA n (unpack n w X) (unpack n w (GQ i))) = true
    rw [comp_unpack' hw (hGQ i hi) c2, comp_unpack' hw c2 (hGQ i hi),
      eqA_unpack' hw (permB_pcomp hw (hGQ i hi) c2) (permB_pcomp hw c2 (hGQ i hi))]
    exact (Bool.and_eq_true_iff.1 (Orb.allN_iff.1 c5 i hi)).2
  have g7 : cQ.pts.toList.any (eqA n (unpack n w X)) = true := any_of_memK hsQ hpQ c6
  have g9 : (cK.pts.size * m == cQ.pts.size) = true := beq_iff_eq.2 (by
    rw [hsK, hsQ]
    exact Nat.eq_of_beq_eq_true c7)
  have g10 : cK.pts.toList.any (eqA n (unpack n w X)) = true := any_of_memK hsK hpK c8
  have g11 : allLt D.gK.size (fun l => cQ.pts.toList.any (eqA n D.gK[l]!)) = true := by
    rw [CFSG.Monster.B.Co2.allLt_iff, hKb.1]
    intro l hl
    rw [hKb.2 l hl]
    exact any_of_memK hsQ hpQ (Orb.allN_iff.1 c9 l hl)
  have g12 : (D.reps.size == m) = true := beq_iff_eq.2 hR.1
  have g13 : allLt m (fun j => validA n D.reps[j]! &&
      cQ.pts.toList.any (eqA n D.reps[j]!)) = true := by
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j hj
    rw [hR.2 j hj, validA_of (hRp j hj), memK_eq hw hsQ hpQ hTQ (hRp j hj), Bool.true_and]
    exact (Bool.and_eq_true_iff.1 (Orb.allN_iff.1 c10 j hj)).2
  have g14 : allLt m (fun j => allLt m (fun k => (j == k) ||
      !(cK.pts.toList.any (eqA n (compA n (invCand n D.reps[j]!) D.reps[k]!))))) = true := by
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j hj
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro k hk
    have hc := permB_pcomp hw (permB_pinvS hw (hRp j hj)) (hRp k hk)
    rw [hR.2 j hj, hR.2 k hk, CFSG.KC.BfsPin.invCand_PP (pp_of_permB hw (hRp j hj)),
      comp_unpack' hw (permB_pinvS hw (hRp j hj)) (hRp k hk), memK_eq hw hsK hpK hTK hc]
    have d := Orb.allN_iff.1 (Orb.allN_iff.1 c11 j hj) k hk
    rw [Bool.or_eq_true] at d ⊢
    rcases d with d | d
    · left
      rw [Nat.eq_of_beq_eq_true d]
      exact beq_self_eq_true k
    · exact Or.inr d
  have g15 : (D.cu.size == D.gQ.size) = true := beq_iff_eq.2 (hU.1.trans hQ.1.symm)
  have g16 : (D.cv.size == D.gQ.size) = true := beq_iff_eq.2 (hV.1.trans hQ.1.symm)
  have g17 : allLt D.gQ.size (fun i => validA n D.cu[i]! && validA n D.cv[i]! &&
      cQ.pts.toList.any (eqA n D.cu[i]!) && cQ.pts.toList.any (eqA n D.cv[i]!) &&
      eqA n D.gQ[i]! (commutatorA n D.cu[i]! D.cv[i]!)) = true := by
    rw [CFSG.Monster.B.Co2.allLt_iff, hQ.1]
    intro i hi
    have e := Orb.allN_iff.1 c12 i hi
    simp only [Bool.and_eq_true] at e
    obtain ⟨⟨⟨⟨u1, v1⟩, u2⟩, v2⟩, e5⟩ := e
    have iu := permB_pinvS hw u1
    have iv' := permB_pinvS hw v1
    rw [hU.2 i hi, hV.2 i hi, hQ.2 i hi, validA_of u1, validA_of v1, any_of_memK hsQ hpQ u2,
      any_of_memK hsQ hpQ v2]
    unfold commutatorA
    rw [CFSG.KC.BfsPin.invCand_PP (pp_of_permB hw u1),
      CFSG.KC.BfsPin.invCand_PP (pp_of_permB hw v1), comp_unpack' hw u1 v1,
      comp_unpack' hw iu iv', comp_unpack' hw (permB_pcomp hw u1 v1) (permB_pcomp hw iu iv'),
      eqA_unpack' hw (hGQ i hi) (permB_pcomp hw (permB_pcomp hw u1 v1) (permB_pcomp hw iu iv')),
      Bool.true_and, Bool.true_and, Bool.true_and, Bool.true_and]
    exact e5
  have g18 : (D.sig.size == D.gQ.size) = true := beq_iff_eq.2 (hsz.trans hQ.1.symm)
  have g19 : allLt D.gQ.size (fun i => allLt m (fun j => decide ((D.sig[i]!)[j]! < m) &&
      cK.pts.toList.any (eqA n (compA n (invCand n D.reps[(D.sig[i]!)[j]!]!)
        (compA n D.gQ[i]! D.reps[j]!))))) = true := by
    rw [CFSG.Monster.B.Co2.allLt_iff, hQ.1]
    intro i hi
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j hj
    obtain ⟨s1, s2⟩ := Bool.and_eq_true_iff.1 (Orb.allN_iff.1 (Orb.allN_iff.1 c13 i hi) j hj)
    have hs : sig i j < m := by
      rw [Nat.blt_eq] at s1
      exact s1
    have hRs := hRp _ hs
    have hc := permB_pcomp hw (permB_pinvS hw hRs) (permB_pcomp hw (hGQ i hi) (hRp j hj))
    rw [hsig i hi j hj, hR.2 _ hs, hR.2 j hj, hQ.2 i hi,
      CFSG.KC.BfsPin.invCand_PP (pp_of_permB hw hRs), comp_unpack' hw (hGQ i hi) (hRp j hj),
      comp_unpack' hw (permB_pinvS hw hRs) (permB_pcomp hw (hGQ i hi) (hRp j hj)),
      memK_eq hw hsK hpK hTK hc, decide_eq_true hs, Bool.true_and]
    exact s2
  have g21 : (cS.pts.size == m.factorial / 2) = true :=
    beq_iff_eq.2 (hsS.trans (Nat.eq_of_beq_eq_true c14))
  unfold tcOK
  rw [heQ, g2, g3, g4, g5, g6, g7, heK, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19,
    heS, g21] <;> rfl

end CFSG.KC.TcK

end
