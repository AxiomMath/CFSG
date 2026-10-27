module

public import CFSG.Certificates.Kernel.DceSPDec
public import CFSG.Certificates.Kernel.DceSPPts
public import CFSG.Certificates.Kernel.DceTwCore

public section

namespace CFSG.Certificates.DSP

open CFSG.KC.Loop CFSG.KC.HNA.DceS CFSG.Certificates.DceLoop
open scoped Classical

set_option exponentiation.threshold 400

theorem isN_iff {TL VL NL c : ℕ} : isN TL VL NL c = true ↔ c < NL ∧ c ≠ TL ∧ c ≠ VL := by
  unfold isN
  rw [andL_iff, andL_iff, notL_eq, notL_eq, Nat.blt_eq]
  refine and_congr_right fun _ => and_congr ⟨fun h e => ?_, fun h => ?_⟩ ⟨fun h e => ?_, fun h => ?_⟩
  · rw [e] at h
    exact absurd h (by simp)
  · exact Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)
  · rw [e] at h
    exact absurd h (by simp)
  · exact Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)

structure LetOK (LT LI TL VL NL : ℕ) : Prop where
  nl : NL < 255
  tl : TL < NL
  vl : VL < NL
  inv : ∀ c < NL, byte LI (byte LI c) = c ∧ byte LI c < NL
  tli : byte LI TL = VL
  nval : ∀ c, isN TL VL NL c = true → validP (letP LT c) = true ∧
    mulP (letP LT c) (letP LT (byte LI c)) = ONEP

theorem lettersOK_spec {LT LI TL VL NL : ℕ} (h : lettersOK LT LI TL VL NL = true) :
    LetOK LT LI TL VL NL := by
  unfold lettersOK at h
  obtain ⟨h1, r⟩ := andL_iff.1 h
  obtain ⟨h2, r⟩ := andL_iff.1 r
  obtain ⟨h3, h5⟩ := andL_iff.1 r
  have hall := (allL_iff (fun c => letterOK LT LI TL VL NL c) NL).1 h5
  have hc : ∀ c < NL, byte LI (byte LI c) = c ∧ byte LI c < NL ∧
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) true (Nat.beq (byte LI c) VL) (Nat.beq c TL))
        (andB (validP (letP LT c)) (Nat.beq (mulP (letP LT c) (letP LT (byte LI c))) ONEP))
        (isN TL VL NL c) = true := by
    intro c hc
    have e := hall c hc
    unfold letterOK at e
    obtain ⟨e1, r⟩ := andL_iff.1 e
    obtain ⟨e2, e3⟩ := andL_iff.1 r
    exact ⟨Nat.eq_of_beq_eq_true e1, Nat.blt_eq.mp e2, e3⟩
  have hTL : TL < NL := Nat.blt_eq.mp h2
  refine ⟨Nat.blt_eq.mp h1, hTL, Nat.blt_eq.mp h3,
    fun c hc' => ⟨(hc c hc').1, (hc c hc').2.1⟩, ?_, fun c hN => ?_⟩
  · have e := (hc TL hTL).2.2
    have hN : isN TL VL NL TL = false := by
      cases e2 : isN TL VL NL TL
      · rfl
      · exact absurd rfl (isN_iff.1 e2).2.1
    rw [hN] at e
    change Bool.rec (motive := fun _ => Bool) true (Nat.beq (byte LI TL) VL) (Nat.beq TL TL) = true at e
    rw [show Nat.beq TL TL = true from Nat.beq_refl TL] at e
    exact Nat.eq_of_beq_eq_true e
  · have e := (hc c (isN_iff.1 hN).1).2.2
    rw [hN] at e
    obtain ⟨e1, e2⟩ := andL_iff.1 e
    exact ⟨e1, Nat.eq_of_beq_eq_true e2⟩

section Letters

variable {LT LI TL VL NL : ℕ} (hL : LetOK LT LI TL VL NL)
include hL

theorem LetOK.vli : byte LI VL = TL := by
  rw [← hL.tli]
  exact (hL.inv TL hL.tl).1

theorem LetOK.isN_inv {c : ℕ} (hc : isN TL VL NL c = true) : isN TL VL NL (byte LI c) = true := by
  obtain ⟨h1, h2, h3⟩ := isN_iff.1 hc
  refine isN_iff.2 ⟨(hL.inv c h1).2, fun e => h3 ?_, fun e => h2 ?_⟩
  · rw [← (hL.inv c h1).1, e, hL.tli]
  · rw [← (hL.inv c h1).1, e, hL.vli]

end Letters

@[expose] noncomputable def Lm (LT TL VL NL c : ℕ) : Equiv.Perm (Fin 55) :=
  if isN TL VL NL c = true then mP (letP LT c) else 1

@[expose] def Nset (TL VL NL : ℕ) : Set ℕ := {c | c < NL ∧ isN TL VL NL c = true}

@[expose] noncomputable def Mg (LT TL VL NL : ℕ) : Subgroup (Equiv.Perm (Fin 55)) :=
  Subgroup.closure (Lm LT TL VL NL '' Nset TL VL NL)

@[expose] def InM (LT TL VL NL A : ℕ) : Prop := PV A ∧ mP A ∈ Mg LT TL VL NL

@[expose] noncomputable def mEl (LT TL VL NL A : ℕ) : Mg LT TL VL NL :=
  if h : InM LT TL VL NL A then ⟨mP A, h.2⟩ else 1

section Model

variable {LT LI TL VL NL : ℕ}

theorem mEl_val {A : ℕ} (h : InM LT TL VL NL A) :
    ((mEl LT TL VL NL A : Mg LT TL VL NL) : Equiv.Perm (Fin 55)) = mP A := by
  unfold mEl
  rw [dite_eq_left h]

theorem InM_one : InM LT TL VL NL ONEP :=
  ⟨one_PV, by rw [mP_one]; exact Subgroup.one_mem _⟩

theorem InM_mul {A B : ℕ} (hA : InM LT TL VL NL A) (hB : InM LT TL VL NL B) :
    InM LT TL VL NL (mulP A B) :=
  ⟨mulP_PV hA.1 hB.1, by rw [mP_mul hA.1 hB.1]; exact Subgroup.mul_mem _ hA.2 hB.2⟩

theorem mP_inv {A B : ℕ} (hA : PV A) (hB : PV B) (h : mulP A B = ONEP) : mP B = (mP A)⁻¹ := by
  have e := mP_mul hA hB
  rw [h, mP_one] at e
  exact (inv_eq_of_mul_eq_one_right e.symm).symm

theorem InM_invR {A B : ℕ} (hA : InM LT TL VL NL A) (hB : PV B) (h : mulP A B = ONEP) :
    InM LT TL VL NL B :=
  ⟨hB, by rw [mP_inv hA.1 hB h]; exact Subgroup.inv_mem _ hA.2⟩

theorem InM_invL {A B : ℕ} (hB : InM LT TL VL NL B) (hA : PV A) (h : mulP A B = ONEP) :
    InM LT TL VL NL A := by
  refine ⟨hA, ?_⟩
  have e := mP_inv hA hB.1 h
  rw [← inv_inv (mP A), ← e]
  exact Subgroup.inv_mem _ hB.2

variable (hL : LetOK LT LI TL VL NL)
include hL

theorem letter_PV {c : ℕ} (hN : isN TL VL NL c = true) : PV (letP LT c) :=
  validP_spec (hL.nval c hN).1

omit hL in
theorem Lm_val {c : ℕ} (hN : isN TL VL NL c = true) : Lm LT TL VL NL c = mP (letP LT c) := by
  unfold Lm
  rw [ite_eq_left hN]

omit hL in
theorem Lm_mem {c : ℕ} (hN : isN TL VL NL c = true) : Lm LT TL VL NL c ∈ Mg LT TL VL NL :=
  Subgroup.subset_closure ⟨c, ⟨(isN_iff.1 hN).1, hN⟩, rfl⟩

theorem InM_letter {c : ℕ} (hN : isN TL VL NL c = true) : InM LT TL VL NL (letP LT c) :=
  ⟨letter_PV hL hN, Lm_val hN ▸ Lm_mem hN⟩

theorem letter_inv {c : ℕ} (hN : isN TL VL NL c = true) :
    mP (letP LT c) * mP (letP LT (byte LI c)) = 1 := by
  rw [mP_inv (letter_PV hL hN) (letter_PV hL (hL.isN_inv hN)) (hL.nval c hN).2, mul_inv_cancel]

theorem segProd_spec (Wd o : ℕ) : ∀ m, Cst (segProd LT TL VL NL Wd o m) ∨
    ((∀ k < m, isN TL VL NL (byte Wd (o + k)) = true) ∧ InM LT TL VL NL (segProd LT TL VL NL Wd o m) ∧
      mP (segProd LT TL VL NL Wd o m) = ((List.range m).map fun k => mP (letP LT (byte Wd (o + k)))).prod)
  | 0 => Or.inr ⟨fun k hk => absurd hk (Nat.not_lt_zero k), InM_one, by
      change mP ONEP = _
      rw [mP_one]
      rfl⟩
  | m + 1 => by
    have hs : segProd LT TL VL NL Wd o (m + 1) = Bool.rec (motive := fun _ => ℕ) 0
        (mulP (segProd LT TL VL NL Wd o m) (letP LT (byte Wd (o + m))))
        (isN TL VL NL (byte Wd (o + m))) := rfl
    rw [hs]
    cases hN : isN TL VL NL (byte Wd (o + m))
    · exact Or.inl cst_zero
    · dsimp only
      rcases segProd_spec Wd o m with h0 | ⟨h1, h2, h3⟩
      · exact Or.inl (cst_mul_left _ h0)
      · right
        refine ⟨fun k hk => ?_, InM_mul h2 (InM_letter hL hN), ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
          · exact h1 k hk
          · exact hN
        · rw [mP_mul h2.1 (letter_PV hL hN), h3, List.range_succ, List.map_append,
            List.prod_append, List.map_singleton, List.prod_singleton]

end Model

theorem hdrOK_spec {HB : ℕ → ℕ} {LT TL VL NL h d : ℕ} (hh : hdrOK HB LT TL VL NL h d = true) :
    mat HB h = ONEP ∨ (∃ a, isN TL VL NL a = true ∧ mat HB h = letP LT a) ∨
      (∃ a b, a < h ∧ b < h ∧ mat HB h = mulP (mat HB a) (mat HB b)) ∨
      (∃ a, a < h ∧ validP (mat HB h) = true ∧ mulP (mat HB h) (mat HB a) = ONEP) := by
  unfold hdrOK at hh
  beta_reduce at hh
  generalize mat HB h = H at hh ⊢
  generalize Nat.land d 7 = k at hh
  generalize bits d 3 20 = a at hh
  generalize bits d 23 20 = b at hh
  revert hh
  cases Nat.beq k 0
  · cases Nat.beq k 1
    · cases Nat.beq k 2
      · cases Nat.beq k 3
        · intro hh
          exact absurd hh Bool.false_ne_true
        · intro hh
          change andB (Nat.blt a h) (andB (validP H) (Nat.beq (mulP H (mat HB a)) ONEP)) = true at hh
          obtain ⟨e1, r⟩ := andL_iff.1 hh
          obtain ⟨e2, e3⟩ := andL_iff.1 r
          exact Or.inr (Or.inr (Or.inr ⟨a, Nat.blt_eq.mp e1, e2, Nat.eq_of_beq_eq_true e3⟩))
      · intro hh
        change andB (Nat.blt a h) (andB (Nat.blt b h)
          (Nat.beq H (mulP (mat HB a) (mat HB b)))) = true at hh
        obtain ⟨e1, r⟩ := andL_iff.1 hh
        obtain ⟨e2, e3⟩ := andL_iff.1 r
        exact Or.inr (Or.inr (Or.inl ⟨a, b, Nat.blt_eq.mp e1, Nat.blt_eq.mp e2,
          Nat.eq_of_beq_eq_true e3⟩))
    · intro hh
      change andB (isN TL VL NL a) (Nat.beq H (letP LT a)) = true at hh
      obtain ⟨e1, e2⟩ := andL_iff.1 hh
      exact Or.inr (Or.inl ⟨a, e1, Nat.eq_of_beq_eq_true e2⟩)
  · intro hh
    change Nat.beq H ONEP = true at hh
    exact Or.inl (Nat.eq_of_beq_eq_true hh)

section Header

variable {LT LI TL VL NL : ℕ} (hL : LetOK LT LI TL VL NL)
include hL

theorem hdr_mem {HB : ℕ → ℕ} {Ch : List ℕ} {nH : ℕ}
    (hhdr : runHdr HB LT TL VL NL Ch 1 = nH + 1) : ∀ h < nH, InM LT TL VL NL (mat HB h) := by
  rw [runHdr_eq] at hhdr
  have hi := cntRun_spec (a := 0) hhdr
  intro h
  induction h using Nat.strong_induction_on with
  | _ h ih =>
    intro hh
    obtain ⟨J, hd⟩ := hi h (Nat.zero_le _) hh
    rcases hdrOK_spec hd with e | ⟨a, ha, e⟩ | ⟨a, b, ha, hb, e⟩ | ⟨a, ha, hv, e⟩
    · rw [e]
      exact InM_one
    · rw [e]
      exact InM_letter hL ha
    · rw [e]
      exact InM_mul (ih a ha (by omega)) (ih b hb (by omega))
    · exact InM_invL (ih a ha (by omega)) (validP_spec hv) e

@[expose] noncomputable def gm (HB GB : ℕ → ℕ) (j : ℕ) : ℕ := mat HB (lo20 (e40 GB j))
@[expose] noncomputable def gi (HB GB : ℕ → ℕ) (j : ℕ) : ℕ := mat HB (hi20 (e40 GB j))

omit hL in
theorem gomOK_spec {HB GB OB : ℕ → ℕ} {I0 nH j : ℕ} (hg : gomOK HB GB OB I0 nH j = true) :
    lo20 (e40 GB j) < nH ∧ hi20 (e40 GB j) < nH ∧ actOK (pt OB I0) (gm HB GB j) (pt OB j) = true ∧
      mulP (gm HB GB j) (gi HB GB j) = ONEP ∧ canonP (pt OB j) = true := by
  unfold gomOK at hg
  obtain ⟨e1, r⟩ := andL_iff.1 hg
  obtain ⟨e2, r⟩ := andL_iff.1 r
  obtain ⟨e3, r⟩ := andL_iff.1 r
  obtain ⟨e4, e5⟩ := andL_iff.1 r
  exact ⟨Nat.blt_eq.mp e1, Nat.blt_eq.mp e2, e3, Nat.eq_of_beq_eq_true e4, e5⟩

theorem gom_spec {HB GB OB : ℕ → ℕ} {Ch Cg : List ℕ} {nH NO I0 : ℕ}
    (hhdr : runHdr HB LT TL VL NL Ch 1 = nH + 1) (hgom : runGom HB GB OB I0 nH Cg 1 = NO + 1) :
    ∀ j < NO, InM LT TL VL NL (gm HB GB j) ∧ InM LT TL VL NL (gi HB GB j) ∧
      mulP (gm HB GB j) (gi HB GB j) = ONEP ∧ canonP (pt OB j) = true ∧
      actOK (pt OB I0) (gm HB GB j) (pt OB j) = true := by
  rw [runGom_eq] at hgom
  have hi := gomRun_spec hgom
  have hm := hdr_mem hL hhdr
  intro j hj
  obtain ⟨h1, h2, h3, h4, h5⟩ := gomOK_spec (hi j hj)
  exact ⟨hm _ h1, hm _ h2, h4, h5, h3⟩

end Header

theorem tOK_spec {TB OB RR : ℕ → ℕ} {LT TL VL NL NR nT I0 e d : ℕ}
    (ht : tOK TB OB RR LT TL VL NL NR nT I0 e d = true) :
    validP (tS TB e) = true ∧ validP (tP TB e) = true ∧ (∃ ep < nT, tP TB e = tS TB ep) ∧
      ((∃ a b, a < e ∧ b < e ∧ tS TB e = mulP (tS TB a) (tS TB b) ∧
          tP TB e = mulP (tP TB a) (tP TB b)) ∨
        (∃ r s ns, relVisOK RR LT TL VL NL NR (tS TB e) (tP TB e) r s ns = true ∧
          actOK (pt OB I0) (tS TB e) (pt OB I0) = true)) := by
  unfold tOK at ht
  beta_reduce at ht
  obtain ⟨e1, r⟩ := andL_iff.1 ht
  obtain ⟨e2, r⟩ := andL_iff.1 r
  obtain ⟨e3, r⟩ := andL_iff.1 r
  obtain ⟨e4, e5⟩ := andL_iff.1 r
  refine ⟨e1, e2, ⟨_, Nat.blt_eq.mp e3, Nat.eq_of_beq_eq_true e4⟩, ?_⟩
  revert e5
  cases Nat.beq (Nat.land d 3) 0
  · cases Nat.beq (Nat.land d 3) 1
    · intro e5
      exact absurd e5 Bool.false_ne_true
    · intro e5
      obtain ⟨f1, f2⟩ := andL_iff.1 e5
      exact Or.inr ⟨_, _, _, f1, f2⟩
  · intro e5
    obtain ⟨f1, r⟩ := andL_iff.1 e5
    obtain ⟨f2, r⟩ := andL_iff.1 r
    obtain ⟨f3, f4⟩ := andL_iff.1 r
    exact Or.inl ⟨_, _, Nat.blt_eq.mp f1, Nat.blt_eq.mp f2, Nat.eq_of_beq_eq_true f3,
      Nat.eq_of_beq_eq_true f4⟩

theorem relVisOK_S {RR : ℕ → ℕ} {LT TL VL NL NR S P r s ns : ℕ}
    (hr : relVisOK RR LT TL VL NL NR S P r s ns = true) :
    S = segProd LT TL VL NL (CFSG.KC.Th.rot (Nat.shiftRight (RR r) 12) (bits (RR r) 2 10) s) 1 ns := by
  unfold relVisOK at hr
  beta_reduce at hr
  obtain ⟨-, r⟩ := andL_iff.1 hr
  obtain ⟨-, r⟩ := andL_iff.1 r
  obtain ⟨-, r⟩ := andL_iff.1 r
  obtain ⟨-, r⟩ := andL_iff.1 r
  obtain ⟨-, r⟩ := andL_iff.1 r
  obtain ⟨e, -⟩ := andL_iff.1 r
  exact Nat.eq_of_beq_eq_true e

section Table

variable {LT LI TL VL NL : ℕ} (hL : LetOK LT LI TL VL NL)
include hL

theorem tab_mem {TB OB RR : ℕ → ℕ} {NR nT I0 : ℕ} {Ct : List ℕ}
    (hT : runT TB OB RR LT TL VL NL NR nT I0 Ct 1 = nT + 1) (hθ : canonP (pt OB I0) = true) :
    ∀ e < nT, InM LT TL VL NL (tS TB e) ∧ actP (ptS (pt OB I0)) (mP (tS TB e)) = ptS (pt OB I0) := by
  rw [runT_eq] at hT
  have hi := cntRun_spec (a := 0) hT
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro he
    obtain ⟨J, ht⟩ := hi e (Nat.zero_le _) he
    obtain ⟨hS, -, -, hk⟩ := tOK_spec ht
    rcases hk with ⟨a, b, ha, hb, eS, -⟩ | ⟨r, s, ns, hr, hact⟩
    · obtain ⟨ma, sa⟩ := ih a ha (by omega)
      obtain ⟨mb, sb⟩ := ih b hb (by omega)
      refine ⟨eS ▸ InM_mul ma mb, ?_⟩
      rw [eS, mP_mul ma.1 mb.1, ← actP_mul, sa, sb]
    · refine ⟨?_, actOK_sound hact hθ hθ (validP_spec hS)⟩
      have eS := relVisOK_S hr
      rcases segProd_spec hL _ 1 ns with h0 | ⟨-, hm, -⟩
      · exact absurd (eS ▸ h0) (not_cst (validP_spec hS))
      · rw [eS]
        exact hm

end Table

section Orbit

variable {LT LI TL VL NL : ℕ} (hL : LetOK LT LI TL VL NL)
include hL

theorem orb {HB GB OB TB RR : ℕ → ℕ} {Ch Cg Ct Os TSs : List ℕ} {nH NO I0 NR nT NORD qO qT O1 T1 : ℕ}
    (hfin : Finite (Mg LT TL VL NL)) (hcard : Nat.card (Mg LT TL VL NL) ≤ NORD)
    (hhdr : runHdr HB LT TL VL NL Ch 1 = nH + 1) (hgom : runGom HB GB OB I0 nH Cg 1 = NO + 1)
    (hT : runT TB OB RR LT TL VL NL NR nT I0 Ct 1 = nT + 1) (hI0 : I0 < NO)
    (hO : runSorted (pt OB) qO NO Os 1 = O1) (hO1 : sortedCount O1 = NO)
    (hTs : runSorted (tS TB) qT nT TSs 1 = T1) (hT1 : sortedCount T1 = nT) (hnord : nT * NO = NORD) :
    DceTw.Orb (Mg LT TL VL NL) NORD Pt actP (ptS (pt OB I0)) (fun j => ptS (pt OB j))
      (fun j => mEl LT TL VL NL (gm HB GB j)) NO I0 (fun e => mEl LT TL VL NL (tS TB e)) nT := by
  have hg := gom_spec hL hhdr hgom
  have hθ : canonP (pt OB I0) = true := (hg I0 hI0).2.2.2.1
  have htab := tab_mem hL hT hθ
  obtain ⟨-, injO⟩ := sortRun_spec (runSorted_eq _ _ _ _ _ ▸ hO) hO1
  obtain ⟨-, injT⟩ := sortRun_spec (runSorted_eq _ _ _ _ _ ▸ hTs) hT1
  refine ⟨hfin, hcard, actP_one, actP_mul, fun j hj => ?_, fun j hj j' hj' e => ?_, hI0, rfl,
    fun e he => ?_, fun e he e' he' h => ?_, hnord⟩
  · obtain ⟨hm, -, -, hcan, hact⟩ := hg j hj
    rw [mEl_val hm]
    exact actOK_sound hact hθ hcan hm.1
  · exact injO j hj j' hj' (ptS_inj (hg j hj).2.2.2.1 (hg j' hj').2.2.2.1 e)
  · rw [mEl_val (htab e he).1]
    exact (htab e he).2
  · have h2 : ((mEl LT TL VL NL (tS TB e) : Mg LT TL VL NL) : Equiv.Perm (Fin 55)) =
        ((mEl LT TL VL NL (tS TB e') : Mg LT TL VL NL) : Equiv.Perm (Fin 55)) := by rw [h]
    rw [mEl_val (htab e he).1, mEl_val (htab e' he').1] at h2
    exact injT e he e' he' (mP_inj (htab e he).1.1 (htab e' he').1.1 h2)

end Orbit

end CFSG.Certificates.DSP

end
