module

public import Certificates.Certificate450215
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Bridge

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open Equiv CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

theorem allIn_zero_iff {n : ℕ} {p : ℕ → Bool} :
    allIn 0 n p = true ↔ ∀ i < n, p i = true := by
  rw [allIn_eq_true]
  exact ⟨fun h i hi => h i (Nat.zero_le _) hi, fun h i _ hi => h i hi⟩

theorem allIn_one_iff {n : ℕ} {p : ℕ → Bool} :
    allIn 1 n p = true ↔ ∀ i, 0 < i → i < n → p i = true := by
  rw [allIn_eq_true]
  exact ⟨fun h i hi hin => h i hi hin, fun h i hi hin => h i hi hin⟩

theorem instrRegsLt_of_progOK {r : ℕ} {prog : List Instr} (h : progOK r prog = true) :
    ∀ ins ∈ prog, instrRegsLt r ins := by
  intro ins hins
  have := List.all_eq_true.1 h ins hins
  cases ins <;> simp_all [instrRegsLt]

structure ObjFacts (run : Array Table × Bool) (gs : Array Table) : Prop where
  flag : run.2 = true
  size : run.1.size = 59
  prog : progOK 59 (objProg ()) = true
  data : dataOK () = true
  tau : tauOK run.1 = true
  epsInv : epsInvOK run.1 = true
  epsComm : epsCommOK run.1 = true
  epsPlane : epsPlaneOK run.1 = true
  abPlane : abPlaneOK run.1 = true
  epsTree : epsTreeOK run.1 = true
  gsSize : gs.size = 22
  zpTree : zpTreeOK gs = true
  triple : tripleCheck () = true

theorem ObjFacts.of_objOKAt {run : Array Table × Bool} {gs : Array Table}
    (h : objOKAt run gs = true) : ObjFacts run gs := by
  unfold objOKAt at h
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem objOK_eq_true : objOK () = true :=
  Certificates.certificate450215

theorem objFacts : ObjFacts (objRun ()) (genTabs ()) :=
  ObjFacts.of_objOKAt objOK_eq_true

abbrev objTabs : Array Table := (objRun ()).1

@[expose] def x1 : Ω := ⟨1479, by norm_num⟩

@[expose] def x2 : Ω := ⟨99705, by norm_num⟩

theorem x1_val : x1.val = 1479 := rfl

theorem x2_val : x2.val = 99705 := rfl

theorem planeArr_lt : ∀ i : Fin 24, planeArr[i.val]! < 920808 := by decide

@[expose] def planePt (i : Fin 24) : Ω := ⟨planeArr[i.val]!, planeArr_lt i⟩

theorem planePt_val (i : Fin 24) : (planePt i).val = planeArr[i.val]! := rfl

theorem planePt_injective : Function.Injective planePt := by
  intro i j h
  have hv : planeArr[i.val]! = planeArr[j.val]! := congrArg Fin.val h
  have key : Function.Injective (fun i : Fin 24 => planeArr[i.val]!) := by decide
  exact key hv

theorem planePt_zero : planePt 0 = x0 := Fin.ext (by decide)

theorem planePt_one : planePt 1 = x1 := Fin.ext (by decide)

theorem planePt_two : planePt 2 = x2 := Fin.ext (by decide)

@[expose] def plane : Finset Ω := Finset.univ.image planePt

theorem mem_plane_iff {p : Ω} : p ∈ plane ↔ ∃ i, planePt i = p := by
  simp [plane]

theorem planePt_mem (i : Fin 24) : planePt i ∈ plane := mem_plane_iff.2 ⟨i, rfl⟩

theorem card_plane : plane.card = 24 := by
  rw [plane, Finset.card_image_of_injective _ planePt_injective]
  simp

theorem x0_mem_plane : x0 ∈ plane := planePt_zero ▸ planePt_mem 0

theorem x1_mem_plane : x1 ∈ plane := planePt_one ▸ planePt_mem 1

theorem x2_mem_plane : x2 ∈ plane := planePt_two ▸ planePt_mem 2

theorem x0_ne_x1 : x0 ≠ x1 := by
  intro h
  have := congrArg Fin.val h
  simp [x0, x1] at this

theorem x0_ne_x2 : x0 ≠ x2 := by
  intro h
  have := congrArg Fin.val h
  simp [x0, x2] at this

theorem x1_ne_x2 : x1 ≠ x2 := by
  intro h
  have := congrArg Fin.val h
  simp [x1, x2] at this

theorem planeAArr_lt : ∀ i : Fin 24, planeAArr[i.val]! < 24 := by decide

theorem planeBArr_lt : ∀ i : Fin 24, planeBArr[i.val]! < 24 := by decide

@[expose] noncomputable def PA : Perm (Fin 24) :=
  Equiv.ofBijective (fun i => ⟨planeAArr[i.val]!, planeAArr_lt i⟩) (by decide)

@[expose] noncomputable def PB : Perm (Fin 24) :=
  Equiv.ofBijective (fun i => ⟨planeBArr[i.val]!, planeBArr_lt i⟩) (by decide)

theorem PA_val (i : Fin 24) : (PA i).val = planeAArr[i.val]! := rfl

theorem PB_val (i : Fin 24) : (PB i).val = planeBArr[i.val]! := rfl

noncomputable def objElt (r : ℕ) : Q3 := runSLPG (objProg ()) mQ r

noncomputable def tauElt : Q3 := objElt tauReg

noncomputable def epsElt (j : Fin 11) : Q3 := objElt (epsReg j.val)

noncomputable def aElt : Q3 := objElt aReg

noncomputable def bElt : Q3 := objElt bReg

theorem rep_objElt {r : ℕ}
    (hr : r < 59) : Rep 920808 objTabs[r]! (objElt r) := by
  have hprog : ∀ ins ∈ objProg (), instrRegsLt (2 + 57) ins :=
    instrRegsLt_of_progOK objFacts.prog
  have hok : (runSLP 920808 (objProg ()) (mTabs () ++ Array.replicate 57 (idT 920808))).2 =
      true := objFacts.flag
  exact rep_runSLP_m (objProg ()) 57 hprog hok r (by omega)

theorem rep_tauElt :
    Rep 920808 objTabs[tauReg]! tauElt :=
  rep_objElt (by decide)

theorem rep_epsElt (j : Fin 11) :
    Rep 920808 objTabs[epsReg j.val]! (epsElt j) :=
  rep_objElt (by have := j.isLt; simp only [epsReg]; omega)

theorem rep_aElt :
    Rep 920808 objTabs[aReg]! aElt :=
  rep_objElt (by decide)

theorem rep_bElt :
    Rep 920808 objTabs[bReg]! bElt :=
  rep_objElt (by decide)

theorem tauElt_smul_x0 :
    tauElt • x0 = x1 := by
  apply Fin.ext
  rw [smul_val_of_rep rep_tauElt x0, x0_val, x1_val]
  have := objFacts.tau
  simp only [tauOK, Bool.and_eq_true, beq_iff_eq] at this
  exact this.1

theorem tauElt_smul_x1 :
    tauElt • x1 = x0 := by
  apply Fin.ext
  rw [smul_val_of_rep rep_tauElt x1, x1_val, x0_val]
  have := objFacts.tau
  simp only [tauOK, Bool.and_eq_true, beq_iff_eq] at this
  exact this.2

theorem aElt_smul_planePt
    (i : Fin 24) : aElt • planePt i = planePt (PA i) := by
  apply Fin.ext
  rw [smul_val_of_rep rep_aElt (planePt i), planePt_val, planePt_val, PA_val]
  have := objFacts.abPlane
  simp only [abPlaneOK] at this
  have h := (allIn_zero_iff.1 this) i.val i.isLt
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem bElt_smul_planePt
    (i : Fin 24) : bElt • planePt i = planePt (PB i) := by
  apply Fin.ext
  rw [smul_val_of_rep rep_bElt (planePt i), planePt_val, planePt_val, PB_val]
  have := objFacts.abPlane
  simp only [abPlaneOK] at this
  have h := (allIn_zero_iff.1 this) i.val i.isLt
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

theorem epsElt_smul_planePt
    (j : Fin 11) (i : Fin 24) : epsElt j • planePt i = planePt i := by
  apply Fin.ext
  rw [smul_val_of_rep (rep_epsElt j) (planePt i), planePt_val]
  have := objFacts.epsPlane
  simp only [epsPlaneOK] at this
  have h := (allIn_zero_iff.1 ((allIn_zero_iff.1 this) j.val j.isLt)) i.val i.isLt
  simp only [beq_iff_eq] at h
  exact h

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
