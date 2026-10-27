module

public import Certificates.Certificate22226
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverBase
public import CFSG.Sporadic.HeldB.CertPChain
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23L34

open CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.ComponentClassification.GrSLit.L34Facts

structure HjParts : Prop where
  commA : hjComm hjA.1 (heGen 0) = true
  commB : hjComm hjB.1 (heGen 0) = true
  rels : ∀ w ∈ coverWs ++ [zThree], eqA 8330 (hjWord hjA hjB w).1 (idA 8330) = true
  zTwo : eqA 8330 (hjWord hjA hjB zTwo).1 (heGen 0) = true
  zOneSq : eqA 8330 (compA 8330 hjZ1.1 hjZ1.1) (idA 8330) = true
  zOneNe : eqA 8330 hjZ1.1 (idA 8330) = false
  zOneNeT : eqA 8330 hjZ1.1 (heGen 0) = false
  abNe : hjComm hjA.1 hjB.1 = false
  commG : hjComm hjG.1 (heGen 0) = true
  gNe : hjComm hjG.1 hjZ1.1 = false
  labels : ∀ l ∈ hjLabels, hjLabelOK l = true

theorem hjParts : HjParts := by
  have h := Certificates.certificate22226
  simp only [hjFusOK, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

section Regs

theorem pRep_pair {a b : Array ℕ} {g : Equiv.Perm (Fin 8330)} (ha : Rep 8330 a g)
    (hb : Rep 8330 b g⁻¹) : PRep 8330 (a, b) g :=
  ⟨ha, hb⟩

theorem pRep_heGenPair {k : ℕ} (hk : k < 2) :
    PRep 8330 (heGen k, invCand 8330 (heGen k)) (heGenPerm k) :=
  pRep_pair (rep_heGen hk) (rep_heGen_inv hk)

theorem regIn_hjGens : RegIn 8330 heP hjGens := by
  intro r hr
  simp only [hjGens, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨heGenPerm 0, heGenPerm_mem (by norm_num), pRep_heGenPair (k := 0) (by norm_num)⟩
  · exact ⟨heGenPerm 1, heGenPerm_mem (by norm_num), pRep_heGenPair (k := 1) (by norm_num)⟩

theorem regIn_hjRegs : RegIn 8330 heP hjRegs := RegIn.run hjProg regIn_hjGens

@[expose] def hjPerm (z : ℤ) : Equiv.Perm (Fin 8330) := (regIn_hjRegs.letter z).choose

theorem hjPerm_mem (z : ℤ) : hjPerm z ∈ heP := (regIn_hjRegs.letter z).choose_spec.1

theorem pRep_hjPerm (z : ℤ) : PRep 8330 (pLetter 8330 hjRegs z) (hjPerm z) :=
  (regIn_hjRegs.letter z).choose_spec.2

@[expose] def hjAP : Equiv.Perm (Fin 8330) := hjPerm hjLetA

@[expose] def hjBP : Equiv.Perm (Fin 8330) := hjPerm hjLetB

@[expose] def hjGP : Equiv.Perm (Fin 8330) := hjPerm hjLetG

@[expose] def hjSel (i : Fin 2) : Equiv.Perm (Fin 8330) := if i.val = 0 then hjAP else hjBP

end Regs

section Words

variable {x y : PArr} {g h : Equiv.Perm (Fin 8330)}

theorem pRep_hjLet (hx : PRep 8330 x g) (hy : PRep 8330 y h) (l : Fin 2 × Bool) :
    PRep 8330 (hjLet x y l) (cond l.2 (if l.1.val = 0 then g else h)
      (if l.1.val = 0 then g else h)⁻¹) := by
  obtain ⟨i, b⟩ := l
  by_cases hi : i.val = 0
  · cases b
    · simpa [hjLet, hi] using hx.inv
    · simpa [hjLet, hi] using hx
  · cases b
    · simpa [hjLet, hi] using hy.inv
    · simpa [hjLet, hi] using hy

theorem pRep_hjWord (hx : PRep 8330 x g) (hy : PRep 8330 y h) :
    ∀ w : List (Fin 2 × Bool), PRep 8330 (hjWord x y w)
      (FreeGroup.lift (fun i : Fin 2 => if i.val = 0 then g else h) (FreeGroup.mk w))
  | [] => by simpa [hjWord] using (pRep_id (n := 8330))
  | l :: w => by
    have e : FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w := by
      rw [FreeGroup.mul_mk]
      rfl
    rw [hjWord, e, map_mul]
    have := (pRep_hjLet hx hy l).mul (pRep_hjWord hx hy w)
    convert this using 2
    rw [FreeGroup.lift_mk]
    simp

end Words

theorem comm_of_hjComm {x y : Array ℕ} {g h : Equiv.Perm (Fin 8330)} (hx : Rep 8330 x g)
    (hy : Rep 8330 y h) (hc : hjComm x y = true) : g * h = h * g :=
  eq_of_eqA (rep_compA hx hy) (rep_compA hy hx) hc

theorem not_comm_of_hjComm {x y : Array ℕ} {g h : Equiv.Perm (Fin 8330)} (hx : Rep 8330 x g)
    (hy : Rep 8330 y h) (hc : hjComm x y = false) : g * h ≠ h * g := fun e => by
  have := (eqA_iff (rep_compA hx hy) (rep_compA hy hx)).2 e
  rw [show hjComm x y = eqA 8330 (compA 8330 x y) (compA 8330 y x) from rfl] at hc
  rw [hc] at this
  exact Bool.false_ne_true this

section Lam

theorem pRep_hjA : PRep 8330 hjA hjAP := pRep_hjPerm hjLetA

theorem pRep_hjB : PRep 8330 hjB hjBP := pRep_hjPerm hjLetB

theorem pRep_word (w : List (Fin 2 × Bool)) :
    PRep 8330 (hjWord hjA hjB w) (FreeGroup.lift hjSel (FreeGroup.mk w)) :=
  pRep_hjWord pRep_hjA pRep_hjB w

theorem lift_hjSel_eq_one {w : List (Fin 2 × Bool)} (hw : w ∈ coverWs ++ [zThree]) :
    FreeGroup.lift hjSel (FreeGroup.mk w) = 1 :=
  eq_of_eqA (pRep_word w).1 rep_idA (hjParts.rels w hw)

theorem lift_hjSel_coverWs : ∀ r ∈ wordSet coverWs, FreeGroup.lift hjSel r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  exact lift_hjSel_eq_one (List.mem_append_left _ hw)

@[expose] def hjLam : Cover →* Equiv.Perm (Fin 8330) := PresentedGroup.toGroup lift_hjSel_coverWs

theorem rep_hjLam_cv (w : List (Fin 2 × Bool)) : Rep 8330 (hjWord hjA hjB w).1 (hjLam (cv w)) :=
  (pRep_word w).1

theorem hjLam_of (i : Fin 2) : hjLam (PresentedGroup.of i) = hjSel i := PresentedGroup.toGroup.of _

theorem hjLam_z₃ : hjLam z₃ = 1 := lift_hjSel_eq_one (by simp)

theorem hjLam_z₂ : hjLam z₂ = heGenPerm 0 :=
  eq_of_eqA (rep_hjLam_cv zTwo) (rep_heGen (by norm_num)) hjParts.zTwo

abbrev hjZP : Equiv.Perm (Fin 8330) := hjLam z₁

theorem rep_hjZP : Rep 8330 hjZ1.1 hjZP := rep_hjLam_cv zOne

theorem hjZP_mul_self : hjZP * hjZP = 1 :=
  eq_of_eqA (rep_compA rep_hjZP rep_hjZP) rep_idA hjParts.zOneSq

theorem hjZP_ne_one : hjZP ≠ 1 := fun h => by
  have := (eqA_iff rep_hjZP rep_idA).2 h
  rw [hjParts.zOneNe] at this
  exact Bool.false_ne_true this

theorem hjZP_ne_t : hjZP ≠ heGenPerm 0 := fun h => by
  have := (eqA_iff rep_hjZP (rep_heGen (by norm_num))).2 h
  rw [hjParts.zOneNeT] at this
  exact Bool.false_ne_true this

theorem hjAP_comm : hjAP * heGenPerm 0 = heGenPerm 0 * hjAP :=
  comm_of_hjComm pRep_hjA.1 (rep_heGen (by norm_num)) hjParts.commA

theorem hjBP_comm : hjBP * heGenPerm 0 = heGenPerm 0 * hjBP :=
  comm_of_hjComm pRep_hjB.1 (rep_heGen (by norm_num)) hjParts.commB

theorem hjAB_ne : hjAP * hjBP ≠ hjBP * hjAP :=
  not_comm_of_hjComm pRep_hjA.1 pRep_hjB.1 hjParts.abNe

abbrev hjJ : Subgroup (Equiv.Perm (Fin 8330)) := hjLam.range

theorem hjSel_mem (i : Fin 2) : hjSel i ∈ centralizerIn heP (heGenPerm 0) := by
  rw [mem_centralizerIn]
  fin_cases i
  · exact ⟨hjPerm_mem _, hjAP_comm⟩
  · exact ⟨hjPerm_mem _, hjBP_comm⟩

theorem hjJ_le : hjJ ≤ centralizerIn heP (heGenPerm 0) := by
  rw [hjJ, MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    Subgroup.closure_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, hjLam_of]
  exact hjSel_mem i

theorem hjGP_mem : hjGP ∈ centralizerIn heP (heGenPerm 0) :=
  mem_centralizerIn.2 ⟨hjPerm_mem _,
    comm_of_hjComm (pRep_hjPerm hjLetG).1 (rep_heGen (by norm_num)) hjParts.commG⟩

theorem hjGP_not_comm : hjGP * hjZP ≠ hjZP * hjGP :=
  not_comm_of_hjComm (pRep_hjPerm hjLetG).1 rep_hjZP hjParts.gNe

@[expose] def hjNFP (k a b : ℕ) : Equiv.Perm (Fin 8330) :=
  hjLam (cv (tw k)) * (if a = 1 then hjZP else 1) * (if b = 1 then heGenPerm 0 else 1)

theorem rep_hjNF (k a b : ℕ) : Rep 8330 (hjNF k a b) (hjNFP k a b) := by
  unfold hjNF hjNFP
  refine rep_compA (rep_compA (rep_hjLam_cv _) ?_) ?_
  · split_ifs
    · exact rep_hjZP
    · exact rep_idA
  · split_ifs
    · exact rep_heGen (by norm_num)
    · exact rep_idA

theorem hjLabel_conj {l : ℕ × ℕ × ℕ × ℤ} (hl : l ∈ hjLabels) :
    hjPerm l.2.2.2 * heGenPerm 0 * (hjPerm l.2.2.2)⁻¹ =
      heGenPerm 0 * hjNFP l.1 l.2.1 l.2.2.1 :=
  eq_of_eqA (rep_compA (rep_compA (pRep_hjPerm _).1 (rep_heGen (by norm_num)))
    (pRep_hjPerm _).2) (rep_compA (rep_heGen (by norm_num)) (rep_hjNF _ _ _))
    (hjParts.labels l hl)

end Lam

end CFSG.ComponentClassification.GSThmB.CF23L34
