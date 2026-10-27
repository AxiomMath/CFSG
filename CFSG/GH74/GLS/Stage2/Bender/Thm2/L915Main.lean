module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Step11
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Step12
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Step13
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Step14
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Step15
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Tail
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IG512Proof
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Axb
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Cited
public import CFSG.GH74.GLS.Stage2.Signalizer.L199
public import CFSG.GH74.GLS.Stage2.Local.IVK33C

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

namespace L915

theorem lemma9_15_of_hyps (h19 : B_signalizer_19_9) (h512 : IG_5_12) (h118 : IG_11_8)
    (hplane : OddNoncyclicPlane) (h33 : IVK_3_3_lift) (h916 : Lemma9_16) (h911 : Prop9_11) :
    Lemma9_15 := by
  intro G _ _ z k S M p hC Q hQ
  left
  by_contra hno
  push Not at hno
  obtain ⟨X, hXQ, hX0, hXz, hXN⟩ := hno
  obtain ⟨X', hmin⟩ := exists_minBad9 hQ ⟨X, hXQ, hX0, hXz, hXN⟩
  have h94 : Prop9_4 := prop9_4_of h19 h512
  have h911c : Prop9_11c := prop9_11c_of h512 h911
  have h611 : Step9_11 := step9_11_of h94 h916 h118
  have h612 : Step9_12 := step9_12_of h611 h911c hplane
  have h613 : Step9_13 := step9_13_of h94 h916 h611 h612 h911c hplane
  have h614 : Step9_14 := step9_14_of h94 h916 h611 h612 h613
  have h615 : Step9_15 := step9_15_of h94 h916 h612 h613 h911c hplane
  have h2 := h612 G z k S M p hC Q X' hmin
  have hcard := (h614 G z k S M p hC Q X' hmin).1
  have h3 := h615 G z k S M p hC Q X' hmin
  exact tail9_of h33 G z k S M p hC Q hQ h2 hcard h3.1 h3.2.1 h3.2.2

end L915

theorem lemma9_15_of (h916 : Lemma9_16) (h911 : Prop9_11) : Lemma9_15 :=
  L915.lemma9_15_of_hyps CFSG.GH74.GLS.Stage2.Signalizer.L199.ig_19_9 ig_5_12_thm ig_11_8_thm
    oddNoncyclicPlane_thm ivk33 h916 h911

end CFSG.GH74.GLS.Stage2.Bender.Thm2
