module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24FreeFrame
public import Certificates.Certificate17570

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabFi24

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Fi24.Native
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
open CFSG.HardMathSupport.Dickson.I271.Fi24Free.Native
open CFSG.Sporadic.Fi24 (R J JR jR tR cls lvl gs letters)

attribute [local instance] CFSG.Sporadic.Fi24.rAction

set_option linter.unusedSectionVars false


theorem cA_eq : cA = poC0 := by
  apply Fin.ext
  have e : poW0 = frWc0 := rfl
  rw [cA_val, poC0, e, smul_val_of_rep (rep_wordTab frWc0 frWc0_lt)]
  rfl

theorem cB_eq : cB = poC1 := by
  apply Fin.ext
  have e : poW1 = frWc1 := rfl
  rw [cB_val, poC1, e, smul_val_of_rep (rep_wordTab frWc1 frWc1_lt)]
  rfl

theorem frH0_eq : frH0 = poH := rfl

theorem pt0_eq : pt0 = poP0 := rfl

theorem pt1_eq : pt1 = poP1 := rfl

theorem xJ_smul_eq (a : Fin 306936) : xJ • a = poX • a := by
  rw [← CFSG.Sporadic.Fi24.jR_smul, xJ, map_mul, jR_s0, jR_u2, cA_eq, cB_eq, pt0_eq, pt1_eq, poX]

theorem poLam_of_mem {a : Fin 306936} (ha : a.val ∈ frLam ctx cA.val cB.val) : PoLam a := by
  have e1 : clsPt ctx 0 305530 = (cls pt0 • pt1).val := clsPt_eq_smul pt0 pt1
  have e2 : clsPt ctx cA.val cB.val = (cls cA • cB).val := clsPt_eq_smul cA cB
  unfold frLam at ha
  rw [e1, e2] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  unfold PoLam
  rw [← cA_eq, ← cB_eq, ← pt0_eq, ← pt1_eq]
  rcases ha with h | h | h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h)))))

abbrev BfsFacts : Prop := Fi24PairOrbitFacts

theorem bfs_facts : BfsFacts := Certificates.certificate17570

theorem h0_cA (hB : BfsFacts) : wordElt frH0 • cA = pt0 := by
  rw [cA_eq, frH0_eq, pt0_eq]
  exact hB.h_c0

theorem h0_cB (hB : BfsFacts) : wordElt frH0 • cB = pt1 := by
  rw [cB_eq, frH0_eq, pt1_eq]
  exact hB.h_c1

theorem orbit_card_ge (hB : BfsFacts) :
    3499200 ≤ Nat.card (MulAction.orbit (lvl 2) ((cA, cB) : Fin 306936 × Fin 306936)) := by
  rw [cA_eq, cB_eq]
  exact hB.orbit_card_ge

theorem chirality (hB : BfsFacts) {a : Fin 306936} (ha : a.val ∈ frLam ctx cA.val cB.val)
    {k : J} (hk : k ∈ lvl 2) : ¬(k • cA = wordElt frH0 • a ∧ k • cB = wordElt frH0 • (xJ • a)) := by
  have hl := poLam_of_mem ha
  rw [xJ_smul_eq, cA_eq, cB_eq, frH0_eq]
  exact hB.chirality a hl k hk

end CFSG.HardMathSupport.Dickson.I271.TabFi24
