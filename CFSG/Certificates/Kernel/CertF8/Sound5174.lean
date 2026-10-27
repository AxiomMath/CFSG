module

public import CFSG.Certificates.Kernel.CertF8.Sound9557
public import Certificates.Data.Kernel.CertF8.C5174
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeG28CenterInputs

public section

namespace CFSG.KC.CertF8.G9557

open CFSG.Quasithin CFSG.KC.G28 CFSG.KC.CertF8.T3G CFSG.RankThree.PartTwo.Sec4.Item434G28
  CFSG.AGLEmbedding.KFactProofs.G28 CFSG.LocalAnalysis.RankThreeTheoremC.TenNineOneThree

theorem facts_of_chkP {uw zw ow : List ℕ} {gw : List (List ℕ)} {bs : List ℕ}
    (hP : chkP uw zw ow gw bs = true) : Facts (wordCode uw) (wordCode zw) (wordCode ow) := by
  simp only [chkP, letB_eq, Bool.and_eq_true] at hP
  obtain ⟨⟨⟨⟨hrel, hfu⟩, hfz⟩, hfo⟩, hdist, -⟩ := hP
  rw [← codeP_wordCode uw, ← codeP_wordCode zw, ← codeP_wordCode ow] at hrel hdist
  rw [← codeP_wordCode uw] at hfu
  rw [← codeP_wordCode zw] at hfz
  rw [← codeP_wordCode ow] at hfo
  have vU := valid_wordCode uw
  have vZ := valid_wordCode zw
  have vO := valid_wordCode ow
  have hd : ∀ i < 243, ∀ j < i, (t3List (wordCode uw) (wordCode zw) (wordCode ow))[i]! ≠
      (t3List (wordCode uw) (wordCode zw) (wordCode ow))[j]! := by
    simp only [distinctT, List.all_eq_true, List.mem_range, letB_eq, Bool.not_eq_true'] at hdist
    intro i hi j hj e
    have := hdist i hi j hj
    rw [fldT_t3 vU vZ vO hi, fldT_t3 vU vZ vO (by omega), e, Nat.beq_refl] at this
    exact absurd this (by decide)
  exact {
    vU := vU, vZ := vZ, vO := vO, R := relsG_of vU vZ vO hrel
    inj := fun i hi j hj e => by
      rcases lt_trichotomy i j with h | h | h
      · exact absurd e.symm (hd j hj i h)
      · exact h
      · exact absurd e (hd i hi j h)
    fU := by
      rw [frobCode_wordCode]
      exact eq_of_beq_codeP (valid_wordCode _) (valid_powCode vU 7) (codeP_wordCode _)
        (codeP_powCode vU 7) hfu
    fZ := by
      rw [frobCode_wordCode]
      exact eq_of_beq_codeP (valid_wordCode _) (valid_powCode vZ 7) (codeP_wordCode _)
        (codeP_powCode vZ 7) hfz
    fO := by
      rw [frobCode_wordCode]
      exact eq_of_beq_codeP (valid_wordCode _) vO (codeP_wordCode _) rfl hfo }

section Facts

variable {U Z O : Array ℕ} (F : Facts U Z O)
include F

theorem commL {n m : ℕ} (hn : n < 243) (hm : m < 243) :
    commCode (t3List U Z O)[n]! (t3List U Z O)[m]! = Nat.beq (pm n m) (pm m n) := by
  rw [commCode, mulL F hn hm, mulL F hm hn, beqL F (pm_lt _ _) (pm_lt _ _)]

theorem center_of (h : cen5174K 0 81 162 = true) : ((List.range 243).all fun n =>
    !(commCode (t3List U Z O)[n]! U && commCode (t3List U Z O)[n]! Z &&
      commCode (t3List U Z O)[n]! O) ||
    (t3List U Z O)[n]! == idCode || (t3List U Z O)[n]! == powCode U 3 ||
    (t3List U Z O)[n]! == mulCode (powCode U 3) (powCode U 3)) = true := by
  simp only [cen5174K, List.all_eq_true, List.mem_range] at h ⊢
  intro n hn
  have cU := commL F hn (m := 27) (by norm_num)
  have cZ := commL F hn (m := 3) (by norm_num)
  have cO := commL F hn (m := 1) (by norm_num)
  rw [← eU27 F] at cU
  rw [← eZ3 F] at cZ
  rw [← eO1 F] at cO
  rw [cU, cZ, cO, ezz F, ezc F, idL F hn, beqL F hn (by norm_num), beqL F hn (by norm_num)]
  exact h n hn

end Facts

theorem sound5174 {gw : List (List ℕ)} {bs : List ℕ} (hP : chkP tUW tZW tOW gw bs = true)
    (h : cen5174K 0 81 162 = true) : g28CenterTXCheck = true :=
  center_of (facts_of_chkP hP) h

end CFSG.KC.CertF8.G9557

end
