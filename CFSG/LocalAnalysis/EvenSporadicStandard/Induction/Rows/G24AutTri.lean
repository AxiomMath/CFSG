module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24AutBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundA5
public import Certificates.Certificate27206

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.G24Aut

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co1Block
  CFSG.EvenSporadicStandard.Induction.AutBound
open Subgroup

section Tri


theorem tri_nonsolvable {s : Array ℕ} {S : PP} (hs : Rep nn s S) {i : ℕ}
    (h : triCheck s i = true) : ¬ Group.IsSolvable ↥(twoBD ⊓ centralizer ({S} : Set PP)) := by
  unfold triCheck at h
  obtain ⟨h, c10⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, c9⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, c8⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, c7⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, c6⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, c5⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, c4⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, c3⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨c1, c2⟩ := Eq.mp (Bool.and_eq_true _ _) h
  have ha := rep_permOfArr c3
  have hb := rep_permOfArr c4
  have haS : S * permOfArr nn (triA i) = permOfArr nn (triA i) * S :=
    ((eqA_iff (rep_compA ha.1 hs) (rep_compA hs ha.1)).1 c5).symm
  have hbS : S * permOfArr nn (triB i) = permOfArr nn (triB i) * S :=
    ((eqA_iff (rep_compA hb.1 hs) (rep_compA hs hb.1)).1 c6).symm
  have hm : Nat.Coprime (triM i) 6 := by
    rcases Eq.mp (Bool.or_eq_true _ _) c9 with h5 | h7
    · rw [beq_iff_eq.1 h5]
      norm_num
    · rw [beq_iff_eq.1 h7]
      norm_num
  refine not_isSolvable_of_triangle (twoBD ⊓ centralizer ({S} : Set PP)) hm
    (mem_inf.2 ⟨mem_of_inD ha.1 c1, mem_centralizer_singleton_iff.2 haS.symm⟩)
    (mem_inf.2 ⟨mem_of_inD hb.1 c2, mem_centralizer_singleton_iff.2 hbS.symm⟩) ?_ ?_ ?_
  · exact ((ordIs_iff ha.1 2).1 c7).2
  · exact ((ordIs_iff hb.1 3).1 c8).2
  · exact ((ordIs_iff (rep_compA ha.1 hb.1) _).1 c10).2

theorem g24_tri {tA o : PP} (htA : Rep nn tAa tA)
    (ho : Rep nn oa o) :
    ¬ Group.IsSolvable ↥(twoBD ⊓ centralizer ({tA} : Set PP)) ∧
      ¬ Group.IsSolvable ↥(twoBD ⊓ centralizer ({xBar} : Set PP)) ∧
      ¬ Group.IsSolvable ↥(twoBD ⊓ centralizer ({o} : Set PP)) := by
  have h := Certificates.certificate27206
  unfold trianglesOK at h
  obtain ⟨h, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h0, h1⟩ := Eq.mp (Bool.and_eq_true _ _) h
  exact ⟨tri_nonsolvable htA h0, tri_nonsolvable rep_xa h1, tri_nonsolvable ho h2⟩

end Tri

end CFSG.EvenSporadicStandard.G24Aut
