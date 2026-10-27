module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Q0Planes
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Q0

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open Equiv CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

noncomputable def planeLetterElt (l : ℕ) : Q3 :=
  if l = 0 then aElt else if l = 1 then bElt
  else if h : l < 13 then epsElt ⟨l - 2, by omega⟩ else objElt (planeLetterRegs.getD l 0)

noncomputable def planeWordElt (w : List ℤ) : Q3 := wordG (letterPerm planeLetterElt 16) w

noncomputable def planeGen (s : ℕ) : Q3 :=
  planeWordElt (planeGenWord (planeDWords ()) (planeUWord ()) (planeVWord ()) s)

noncomputable def planeU : Q3 := planeWordElt (planeUWord ())

noncomputable def planeV : Q3 := planeWordElt (planeVWord ())

theorem planeLetterRegs_getD_lt {l : ℕ} (hl : l < 16) : planeLetterRegs.getD l 0 < 59 := by
  interval_cases l <;> decide

theorem planeLetters_getElem (tabs : Array Table) {l : ℕ} (hl : l < 16) :
    (planeLetters tabs)[l]! = tabs[planeLetterRegs.getD l 0]! := by
  interval_cases l <;> rfl

theorem planeLetterElt_zero : planeLetterElt 0 = aElt := by
  simp [planeLetterElt]

theorem planeLetterElt_one : planeLetterElt 1 = bElt := by
  simp [planeLetterElt]

theorem planeLetterElt_two_add {j : ℕ} (hj : j < 11) : planeLetterElt (2 + j) = epsElt ⟨j, hj⟩ := by
  have h1 : 2 + j ≠ 0 := by omega
  have h2 : 2 + j ≠ 1 := by omega
  have h3 : 2 + j < 13 := by omega
  simp only [planeLetterElt, if_neg h1, if_neg h2, dif_pos h3]
  congr 2
  omega

theorem planeWordElt_nil : planeWordElt [] = 1 := by
  simp [planeWordElt, wordG]

theorem planeWordElt_cons (l : ℤ) (w : List ℤ) :
    planeWordElt (l :: w) = letterPerm planeLetterElt 16 l * planeWordElt w := by
  simp [planeWordElt, wordG]

theorem planeWordElt_single (l : ℤ) : planeWordElt [l] = letterPerm planeLetterElt 16 l := by
  simp [planeWordElt, wordG]

theorem planeWordElt_append (u v : List ℤ) :
    planeWordElt (u ++ v) = planeWordElt u * planeWordElt v :=
  planeWordG_append _ u v

theorem planeWordElt_planeInvWord (w : List ℤ) :
    planeWordElt (planeInvWord w) = (planeWordElt w)⁻¹ :=
  wordG_planeInvWord _ (letterPerm_neg planeLetterElt 16) w

theorem planeGen_thirteen : planeGen 13 = planeU⁻¹ * planeV⁻¹ * planeU * planeV := by
  have e : planeGenWord (planeDWords ()) (planeUWord ()) (planeVWord ()) 13 =
      planeInvWord (planeUWord ()) ++ planeInvWord (planeVWord ()) ++ planeUWord () ++
        planeVWord () := by
    simp [planeGenWord]
  rw [planeGen, e, planeWordElt_append, planeWordElt_append, planeWordElt_append,
    planeWordElt_planeInvWord, planeWordElt_planeInvWord]
  rfl

theorem planeGen_eps {j : ℕ} (hj : j < 11) : planeGen (2 + j) = epsElt ⟨j, hj⟩ := by
  have e : planeGenWord (planeDWords ()) (planeUWord ()) (planeVWord ()) (2 + j) =
      [((2 + j : ℕ) : ℤ) + 1] := by
    unfold planeGenWord
    rw [if_neg (by omega), if_pos (by omega)]
  rw [planeGen, e, planeWordElt_single, ← planeLetterElt_two_add hj]
  have h1 : 0 < ((2 + j : ℕ) : ℤ) + 1 ∧ ((((2 + j : ℕ) : ℤ) + 1) - 1).toNat < 16 := by omega
  have h2 : ((((2 + j : ℕ) : ℤ) + 1) - 1).toNat = 2 + j := by omega
  rw [letterPerm, if_pos h1, h2]

section Rep


theorem rep_planeLetter {l : ℕ} (hl : l < 16) :
    Rep 920808 (planeLetters objTabs)[l]! (planeLetterElt l) := by
  rw [planeLetters_getElem _ hl]
  by_cases h0 : l = 0
  · subst h0
    rw [planeLetterElt_zero]
    exact rep_aElt
  by_cases h1 : l = 1
  · subst h1
    rw [planeLetterElt_one]
    exact rep_bElt
  by_cases h13 : l < 13
  · obtain ⟨j, rfl⟩ : ∃ j, l = 2 + j := ⟨l - 2, by omega⟩
    rw [planeLetterElt_two_add (by omega)]
    have e : planeLetterRegs.getD (2 + j) 0 = epsReg j := by
      have hj : j < 11 := by omega
      interval_cases j <;> rfl
    rw [e]
    exact rep_epsElt ⟨j, by omega⟩
  · have e : planeLetterElt l = objElt (planeLetterRegs.getD l 0) := by
      simp only [planeLetterElt, if_neg h0, if_neg h1, dif_neg h13]
    rw [e]
    exact rep_objElt (planeLetterRegs_getD_lt hl)

theorem rep_planeWordTab (w : List ℤ) :
    Rep 920808 (planeGenTab (planeLetters objTabs) ((planeLetters objTabs).map (invT degree)) w)
      (planeWordElt w) := by
  have hF := planesFacts
  have h := rep_wordT_letters (n := 920808) (by norm_num) (gs := planeLetters objTabs)
    (π := planeLetterElt) (fun l hl => rep_planeLetter (by rwa [hF.lettersSize] at hl))
    (fun l hl => hF.lettersInv l (by rwa [hF.lettersSize] at hl)) w
  rw [hF.lettersSize] at h
  exact h

theorem rep_planeGen (s : ℕ) :
    Rep 920808 (planeGenTabAt objTabs (planeDWords ()) (planeUWord ()) (planeVWord ()) s)
      (planeGen s) :=
  rep_planeWordTab _

theorem planeWordElt_fix {w : List ℤ}
    (h : ap (planeGenTab (planeLetters objTabs) ((planeLetters objTabs).map (invT degree)) w)
          0 = 0 ∧
      ap (planeGenTab (planeLetters objTabs) ((planeLetters objTabs).map (invT degree)) w)
          1479 = 1479 ∧
      ap (planeGenTab (planeLetters objTabs) ((planeLetters objTabs).map (invT degree)) w)
          99705 = 99705) :
    planeWordElt w • x0 = x0 ∧ planeWordElt w • x1 = x1 ∧ planeWordElt w • x2 = x2 := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩
  · rw [smul_val_of_rep (rep_planeWordTab w) x0, x0_val]
    exact h0
  · rw [smul_val_of_rep (rep_planeWordTab w) x1, x1_val]
    exact h1
  · rw [smul_val_of_rep (rep_planeWordTab w) x2, x2_val]
    exact h2

theorem planeGen_fix {s : ℕ} (hs : s < 14) :
    planeGen s • x0 = x0 ∧ planeGen s • x1 = x1 ∧ planeGen s • x2 = x2 :=
  planeWordElt_fix (planesFacts.fixGen s hs)

theorem planeU_fix : planeU • x0 = x0 ∧ planeU • x1 = x1 ∧ planeU • x2 = x2 :=
  planeWordElt_fix planesFacts.fixU

theorem planeV_fix : planeV • x0 = x0 ∧ planeV • x1 = x1 ∧ planeV • x2 = x2 :=
  planeWordElt_fix planesFacts.fixV

end Rep

theorem planeWordElt_mem_Zq {w : List ℤ} (hw : ∀ l ∈ w, 1 ≤ l.natAbs ∧ l.natAbs ≤ 13) :
    planeWordElt w ∈ Zq := by
  have hlet : ∀ l : ℕ, l < 13 → planeLetterElt l ∈ Zq := by
    intro l hl
    by_cases h2 : 2 ≤ l
    · obtain ⟨j, rfl⟩ : ∃ j, l = 2 + j := ⟨l - 2, by omega⟩
      rw [planeLetterElt_two_add (by omega)]
      exact epsElt_mem_Zq _
    · interval_cases l
      · rw [planeLetterElt_zero]
        exact aElt_mem_Zq
      · rw [planeLetterElt_one]
        exact bElt_mem_Zq
  induction w with
  | nil => rw [planeWordElt_nil]; exact Zq.one_mem
  | cons l w ih =>
    rw [planeWordElt_cons]
    refine Zq.mul_mem ?_ (ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨h1, h2⟩ := hw l List.mem_cons_self
    rcases lt_trichotomy l 0 with hneg | hzero | hpos
    · have hc : -l - 1 + 1 = -l := by omega
      have hlt : (-l - 1).toNat < 13 := by omega
      have hcond : ¬ (0 < l ∧ (l - 1).toNat < 16) := by omega
      have hcond' : l < 0 ∧ (-l - 1).toNat < 16 := by omega
      rw [letterPerm, if_neg hcond, if_pos hcond']
      exact Zq.inv_mem (hlet _ hlt)
    · omega
    · have hlt : (l - 1).toNat < 13 := by omega
      have hcond : 0 < l ∧ (l - 1).toNat < 16 := by omega
      rw [letterPerm, if_pos hcond]
      exact hlet _ hlt

section Mem


theorem planeGen_mem_Zq {s : ℕ} (hs : s < 13) : planeGen s ∈ Zq := by
  by_cases h2 : s < 2
  · have e : planeGenWord (planeDWords ()) (planeUWord ()) (planeVWord ()) s =
        (planeDWords ())[s]! := by
      unfold planeGenWord
      rw [if_pos h2]
    rw [planeGen, e]
    exact planeWordElt_mem_Zq fun l hl => planesFacts.dwsLetters s h2 l hl
  · obtain ⟨j, rfl⟩ : ∃ j, s = 2 + j := ⟨s - 2, by omega⟩
    rw [planeGen_eps (by omega)]
    exact epsElt_mem_Zq _


theorem planeGen_mem_Q0 {s : ℕ} (hs : s < 14) : planeGen s ∈ Q0 :=
  mem_Q0_iff_of_fix.2 (planeGen_fix hs)

theorem planeGen_mem_D0 {s : ℕ} (hs : s < 13) : planeGen s ∈ D0 :=
  mem_D0_iff.2 ⟨planeGen_mem_Q0 (by omega), planeGen_mem_Zq hs⟩

theorem planeU_mem_Q0 : planeU ∈ Q0 := mem_Q0_iff_of_fix.2 planeU_fix

theorem planeV_mem_Q0 : planeV ∈ Q0 := mem_Q0_iff_of_fix.2 planeV_fix

theorem planeGen_thirteen_mem_commutator :
    (⟨planeGen 13, planeGen_mem_Q0 (by norm_num)⟩ : ↥Q0) ∈ commutator ↥Q0 := by
  set u : ↥Q0 := ⟨planeU, planeU_mem_Q0⟩ with hu
  set v : ↥Q0 := ⟨planeV, planeV_mem_Q0⟩ with hv
  have h : u⁻¹ * v⁻¹ * u⁻¹⁻¹ * v⁻¹⁻¹ ∈ commutator ↥Q0 :=
    Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ (Subgroup.mem_top u))
      (Subgroup.inv_mem _ (Subgroup.mem_top v))
  have e : (⟨planeGen 13, planeGen_mem_Q0 (by norm_num)⟩ : ↥Q0) = u⁻¹ * v⁻¹ * u⁻¹⁻¹ * v⁻¹⁻¹ := by
    apply Subtype.ext
    change planeGen 13 = ((u⁻¹ * v⁻¹ * u⁻¹⁻¹ * v⁻¹⁻¹ : ↥Q0) : Q3)
    rw [planeGen_thirteen]
    simp [hu, hv]
  rw [e]
  exact h

end Mem

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
