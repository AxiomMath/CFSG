module

public import CFSG.Certificates.Kernel.CTIBqCore

public section

namespace CFSG.KC.CTIBq

open CFSG.KLie.CT CFSG.EvenSmallLie.TwoE6 CFSG.Monster.B.CTIB.Native CFSG.Monster.B.Bin

@[expose] def genImgsG (q1 q2 : List Nat) (s1 s2 l : Nat) : Array Nat :=
  ((List.range 22).map fun i =>
    signedImg (if l = 0 then q1 else q2) (if l = 0 then s1 else s2) i).toArray

@[expose] def genInvG (G : Array Nat) (q1 q2 : List Nat) (s1 s2 : Nat) : Array Nat :=
  autPow G (genImgsG q1 q2 s1 s2 1) 47

@[expose] def letterImgsG (q1 q2 : List Nat) (s1 s2 : Nat) (gi : Array Nat) (l : Int) : Array Nat :=
  if l = 1 ∨ l = -1 then genImgsG q1 q2 s1 s2 0 else if l = 2 then genImgsG q1 q2 s1 s2 1 else gi

@[expose] def wordAutG (G : Array Nat) (q1 q2 : List Nat) (s1 s2 : Nat) (gi : Array Nat)
    (w : List Int) : Array Nat :=
  w.foldl (fun A l => autComp G A (letterImgsG q1 q2 s1 s2 gi l)) id23

@[expose] def qinvG (G : Array Nat) (d : Nat) : Nat := qmul G (qmul G d d) d

@[expose] def innerImgsG (G : Array Nat) (d : Nat) : Array Nat :=
  ((List.range 22).map fun i => qmul G (qmul G (qinvG G d) (2 ^ i)) d).toArray

@[expose] def frameG (G : Array Nat) : Bool :=
  qmul G 1 6 == 7 && qmul G 6 1 == 7 && qmul G 1 7 == 6 && qmul G 7 1 == 6

@[expose] def oddWitG (G : Array Nat) (q1 q2 : List Nat) (s1 s2 c y : Nat) (wa : List Int)
    (ea ma : Nat) (wb : List Int) (eb mb n e : Nat) : Bool :=
  let gi := genInvG G q1 q2 s1 s2
  let A := wordAutG G q1 q2 s1 s2 gi wa
  let B := wordAutG G q1 q2 s1 s2 gi wb
  let Ae := autPow G A ea
  let Be := autPow G B eb
  let Aa := autPow G Ae (ma + 1)
  let Bb := autPow G Be (mb + 1)
  let S := autComp G (autComp G (autComp G (autComp G (autComp G Aa Bb)
    (autPow G Aa (ma - 1))) (innerImgsG G n)) Aa) (innerImgsG G (qinvG G n))
  wa.all isLetterB && wb.all isLetterB && ma % 2 == 1 && mb % 2 == 1 &&
    autPow G Ae ma == id23 && autPow G Be mb == id23 &&
    autApply G A c == c && autApply G A y == y &&
    autApply G B c == c && autApply G B y == y &&
    qmul G n c == qmul G c n && qmul G n y == qmul G y n &&
    autComp G S S == innerImgsG G y &&
    qmul G e c == qmul G c e && qmul G (qmul G (qinvG G e) y) e == qmul G y (2 ^ 22)

theorem soundFrame (gL a6 a8 q1 q2 : List Nat) (GR A6 A8 Q1 Q2 : Nat)
    (hb : bindsL GR gL A6 a6 A8 a8 Q1 q1 Q2 q2 = true) (hk : frameCheck GR = true) :
    frameG gL.toArray = true := by
  obtain ⟨⟨hg, hGR⟩, -⟩ := bindsL_spec hb
  have q : ∀ a b, a < 2 ^ 23 → b < 2 ^ 23 → qmulK (tbOf GR) a b = qmul gL.toArray a b :=
    fun a b ha hb => qmulK_eq hg hGR ha hb
  simp only [frameCheck, Aux.strictB_eq, frameK, Aux.andB_eq, Bool.and_eq_true, Nat.beq_eq, and_assoc] at hk
  simp (disch := decide) only [q] at hk
  simp only [frameG, Bool.and_eq_true, beq_iff_eq, and_assoc]
  exact hk

private theorem eqAut {P Q : Nat} {X Y : Array Nat} (hX : PkAut P X) (hY : PkAut Q Y) (h : P = Q) :
    X = Y := by
  subst h
  exact Bd_inj hX hY

private theorem wordOK_letters (w : List Nat) (h : wordOK w = true) :
    (w.map decL).all isLetterB = true := by
  induction w with
  | nil => rfl
  | cons l t ih =>
    have e : wordOK (l :: t) = andB (Nat.blt l 3) (wordOK t) := rfl
    rw [e, Aux.andB_eq, Bool.and_eq_true, Aux.blt_eq, decide_eq_true_eq] at h
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true]
    refine ⟨?_, ih h.2⟩
    have := h.1
    by_cases a : l = 0
    · subst a; decide
    · by_cases b : l = 1
      · subst b; decide
      · have : l = 2 := by omega
        subst this; decide

theorem soundOdd (gL a6 a8 q1 q2 : List Nat) (GR A6 A8 Q1 Q2 s1 s2 c y ea ma eb mb n e : Nat)
    (wa wb : List Nat) (hb : bindsL GR gL A6 a6 A8 a8 Q1 q1 Q2 q2 = true)
    (hs : s1 < 2 ^ 22 ∧ s2 < 2 ^ 22) (hcy : c < 2 ^ 23 ∧ y < 2 ^ 23 ∧ n < 2 ^ 23 ∧ e < 2 ^ 23)
    (hm : 1 ≤ ma) (hk : oddCheck GR Q1 Q2 s1 s2 c y wa ea ma wb eb mb n e = true) :
    oddWitG gL.toArray q1 q2 s1 s2 c y (wa.map decL) ea ma (wb.map decL) eb mb n e = true := by
  obtain ⟨⟨hg, hGR⟩, -, -, ⟨hq1, hQ1⟩, ⟨hq2, hQ2⟩⟩ := bindsL_spec hb
  obtain ⟨hc, hy, hn, he⟩ := hcy
  have hG0 : PkAut (sgnImg Q1 s1) (genImgsG q1 q2 s1 s2 0) := by
    simpa [genImgsG] using Bd_sgnImg hg hGR (s := s1) hq1 hQ1
  have hG1 : PkAut (sgnImg Q2 s2) (genImgsG q1 q2 s1 s2 1) := by
    simpa [genImgsG] using Bd_sgnImg hg hGR (s := s2) hq2 hQ2
  have hGI : PkAut (autPowK (tbOf GR) (sgnImg Q2 s2) 47) (genInvG gL.toArray q1 q2 s1 s2) :=
    Bd_autPowK hg hGR hG1 47
  have hW : ∀ w : List Nat, PkAut (wordAutK (tbOf GR) (sgnImg Q1 s1) (sgnImg Q2 s2)
      (autPowK (tbOf GR) (sgnImg Q2 s2) 47) w)
      (wordAutG gL.toArray q1 q2 s1 s2 (genInvG gL.toArray q1 q2 s1 s2) (w.map decL)) := by
    intro w
    have := Bd_wordAutK hg hGR hG0 hG1 hGI w
    refine Eq.subst (motive := fun X => PkAut _ X) ?_ this
    unfold wordAutG
    rw [List.foldl_map]
    congr 1
    funext X l
    by_cases a : l = 0
    · simp [letterImgsG, decL, a]
    · by_cases b : l = 1
      · simp [letterImgsG, decL, b]
      · simp [letterImgsG, decL, a, b]
  have hA := hW wa
  have hB := hW wb
  have hAe := Bd_autPowK hg hGR hA ea
  have hBe := Bd_autPowK hg hGR hB eb
  have hAa := Bd_autPowK hg hGR hAe (ma + 1)
  have hBb := Bd_autPowK hg hGR hBe (mb + 1)
  have hAm := Bd_autPowK hg hGR hAa (ma - 1)
  have hIn := Bd_innerK hg hGR hn
  have hIq : PkAut (innerK (tbOf GR) (qinvK (tbOf GR) n)) (innerImgsG gL.toArray (qinvG gL.toArray n)) := by
    rw [qinvK_eq hg hGR hn]
    exact Bd_innerK hg hGR (qmul_lt _ _)
  have hIy := Bd_innerK hg hGR hy
  have hS := Bd_autCompK hg hGR (Bd_autCompK hg hGR (Bd_autCompK hg hGR
    (Bd_autCompK hg hGR (Bd_autCompK hg hGR hAa hBb) hAm) hIn) hAa) hIq
  unfold oddCheck oddK at hk
  simp only [Aux.strictB_eq, Aux.andB_eq, Bool.and_eq_true, Nat.beq_eq, and_assoc] at hk
  obtain ⟨hwa, hwb, hma, hmb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hk
  have h2p : (4194304 : Nat) = 2 ^ 22 := by decide
  have h22 : (2 : Nat) ^ 22 < 2 ^ 23 := by decide
  simp only [oddWitG, Bool.and_eq_true, beq_iff_eq, and_assoc]
  refine ⟨wordOK_letters wa hwa, wordOK_letters wb hwb, hma, hmb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact eqAut (Bd_autPowK hg hGR hAe ma) Bd_ID23 h1
  · exact eqAut (Bd_autPowK hg hGR hBe mb) Bd_ID23 h2
  · rwa [Bd_autApplyK hg hGR hA hc] at h3
  · rwa [Bd_autApplyK hg hGR hA hy] at h4
  · rwa [Bd_autApplyK hg hGR hB hc] at h5
  · rwa [Bd_autApplyK hg hGR hB hy] at h6
  · rwa [qmulK_eq hg hGR hn hc, qmulK_eq hg hGR hc hn] at h7
  · rwa [qmulK_eq hg hGR hn hy, qmulK_eq hg hGR hy hn] at h8
  · exact eqAut (Bd_autCompK hg hGR hS hS) hIy h9
  · rwa [qmulK_eq hg hGR he hc, qmulK_eq hg hGR hc he] at h10
  · rw [h2p] at h11
    rw [qinvK_eq hg hGR he, qmulK_eq hg hGR (qmul_lt _ _) hy, qmulK_eq hg hGR (qmul_lt _ _) he,
      qmulK_eq hg hGR hy h22] at h11
    exact h11

end CFSG.KC.CTIBq

end
