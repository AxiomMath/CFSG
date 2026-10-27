module

public import CFSG.Certificates.Kernel.DceS5Dec
public import CFSG.Certificates.Kernel.DceS5Pts
public import CFSG.Certificates.Kernel.DceTwCore

public section

namespace CFSG.Certificates.DS5

open CFSG.KC.Loop CFSG.KC.LL.Ly7 CFSG.KC.LyA.DceS CFSG.Certificates.DceLoop
open scoped Classical

set_option exponentiation.threshold 400

theorem notL_eq (b : Bool) : notB b = true ↔ b = false := by
  cases b <;> decide

theorem orL_iff {a b : Bool} : CFSG.KC.LyA.DceS.orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

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
  tv : TL ≠ VL
  inv : ∀ c < NL, byte LI (byte LI c) = c ∧ byte LI c < NL
  tli : byte LI TL = VL
  nval : ∀ c, isN TL VL NL c = true → validM7 (let7 LT c) = true ∧
    mul7 (let7 LT c) (let7 LT (byte LI c)) = ONE7

theorem lettersOK_spec {LT LI TL VL NL : ℕ} (h : lettersOK LT LI TL VL NL = true) :
    LetOK LT LI TL VL NL := by
  unfold lettersOK at h
  obtain ⟨h1, r⟩ := andL_iff.1 h
  obtain ⟨h2, r⟩ := andL_iff.1 r
  obtain ⟨h3, r⟩ := andL_iff.1 r
  obtain ⟨h4, h5⟩ := andL_iff.1 r
  have hall := (allL_iff (fun c => letterOK LT LI TL VL NL c) NL).1 h5
  have hc : ∀ c < NL, byte LI (byte LI c) = c ∧ byte LI c < NL ∧
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) true (Nat.beq (byte LI c) VL) (Nat.beq c TL))
        (andB (validM7 (let7 LT c)) (Nat.beq (mul7 (let7 LT c) (let7 LT (byte LI c))) ONE7))
        (isN TL VL NL c) = true := by
    intro c hc
    have e := hall c hc
    unfold letterOK at e
    obtain ⟨e1, r⟩ := andL_iff.1 e
    obtain ⟨e2, e3⟩ := andL_iff.1 r
    exact ⟨Nat.eq_of_beq_eq_true e1, Nat.blt_eq.mp e2, e3⟩
  have hTL : TL < NL := Nat.blt_eq.mp h2
  refine ⟨Nat.blt_eq.mp h1, hTL, Nat.blt_eq.mp h3, Nat.ne_of_beq_eq_false ((notL_eq _).1 h4),
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

@[expose] noncomputable def Lm (LT LI TL VL NL c : ℕ) : Mat7ˣ :=
  if h : isN TL VL NL c = true ∧ m7 (let7 LT c) * m7 (let7 LT (byte LI c)) = 1 then
    ⟨m7 (let7 LT c), m7 (let7 LT (byte LI c)), h.2, mul_eq_one_comm.1 h.2⟩
  else 1

@[expose] def Nset (TL VL NL : ℕ) : Set ℕ := {c | c < NL ∧ isN TL VL NL c = true}

@[expose] noncomputable def Mg (LT LI TL VL NL : ℕ) : Subgroup Mat7ˣ :=
  Subgroup.closure (Lm LT LI TL VL NL '' Nset TL VL NL)

@[expose] def InM (LT LI TL VL NL A : ℕ) : Prop :=
  C7 A ∧ ∃ y ∈ Mg LT LI TL VL NL, ((y : Mat7ˣ) : Mat7) = m7 A

@[expose] noncomputable def mEl (LT LI TL VL NL A : ℕ) : Mg LT LI TL VL NL :=
  if h : InM LT LI TL VL NL A then ⟨Classical.choose h.2, (Classical.choose_spec h.2).1⟩ else 1

section Model

variable {LT LI TL VL NL : ℕ}

theorem mEl_val {A : ℕ} (h : InM LT LI TL VL NL A) :
    (((mEl LT LI TL VL NL A : Mg LT LI TL VL NL) : Mat7ˣ) : Mat7) = m7 A := by
  unfold mEl
  rw [dite_eq_left h]
  exact (Classical.choose_spec h.2).2

variable (hc : constsOK7 = true)
include hc

theorem one7_ne_zero : ONE7 ≠ 0 := by
  intro h
  have e := (one7 hc).2
  rw [h, zero7.2] at e
  have h1 : (1 : Mat7) 0 0 = 0 := by rw [← e]; rfl
  exact absurd h1 (by decide)

theorem mul7_zero_left {X : ℕ} (hX : C7 X) : mul7 0 X = 0 := by
  obtain ⟨h1, h2⟩ := mul7_sound hc zero7.1 hX
  rw [zero7.2, zero_mul] at h2
  exact m7_inj h1 zero7.1 (h2.trans zero7.2.symm)

theorem mul7_zero_right {X : ℕ} (hX : C7 X) : mul7 X 0 = 0 := by
  obtain ⟨h1, h2⟩ := mul7_sound hc hX zero7.1
  rw [zero7.2, mul_zero] at h2
  exact m7_inj h1 zero7.1 (h2.trans zero7.2.symm)

theorem InM_one : InM LT LI TL VL NL ONE7 :=
  ⟨(one7 hc).1, 1, Subgroup.one_mem _, by rw [(one7 hc).2, Units.val_one]⟩

theorem InM_mul {A B : ℕ} (hA : InM LT LI TL VL NL A) (hB : InM LT LI TL VL NL B) :
    InM LT LI TL VL NL (mul7 A B) := by
  obtain ⟨cA, u, hu, eu⟩ := hA
  obtain ⟨cB, v, hv, ev⟩ := hB
  obtain ⟨h1, h2⟩ := mul7_sound hc cA cB
  exact ⟨h1, u * v, Subgroup.mul_mem _ hu hv, by rw [Units.val_mul, eu, ev, h2]⟩

theorem InM_invR {A B : ℕ} (hA : InM LT LI TL VL NL A) (hB : C7 B) (h : mul7 A B = ONE7) :
    InM LT LI TL VL NL B := by
  obtain ⟨cA, u, hu, eu⟩ := hA
  have e : m7 A * m7 B = 1 := by rw [← (mul7_sound hc cA hB).2, h, (one7 hc).2]
  refine ⟨hB, u⁻¹, Subgroup.inv_mem _ hu, ?_⟩
  rw [← mul_one ((u⁻¹ : Mat7ˣ) : Mat7), ← e, ← mul_assoc, ← eu, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_mul]

theorem InM_invL {A B : ℕ} (hB : InM LT LI TL VL NL B) (hA : C7 A) (h : mul7 A B = ONE7) :
    InM LT LI TL VL NL A := by
  obtain ⟨cB, v, hv, ev⟩ := hB
  have e : m7 A * m7 B = 1 := by rw [← (mul7_sound hc hA cB).2, h, (one7 hc).2]
  refine ⟨hA, v⁻¹, Subgroup.inv_mem _ hv, ?_⟩
  rw [← one_mul ((v⁻¹ : Mat7ˣ) : Mat7), ← e, mul_assoc, ← ev, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, mul_one]

variable (hL : LetOK LT LI TL VL NL)
include hL

theorem letter_C7 {c : ℕ} (hN : isN TL VL NL c = true) : C7 (let7 LT c) :=
  valid7 hc (hL.nval c hN).1

theorem letter_inv {c : ℕ} (hN : isN TL VL NL c = true) :
    m7 (let7 LT c) * m7 (let7 LT (byte LI c)) = 1 := by
  rw [← (mul7_sound hc (letter_C7 hc hL hN) (letter_C7 hc hL (hL.isN_inv hN))).2,
    (hL.nval c hN).2, (one7 hc).2]

theorem Lm_val {c : ℕ} (hN : isN TL VL NL c = true) :
    ((Lm LT LI TL VL NL c : Mat7ˣ) : Mat7) = m7 (let7 LT c) := by
  unfold Lm
  rw [dite_eq_left ⟨hN, letter_inv hc hL hN⟩]

omit hc hL in
theorem Lm_mem {c : ℕ} (hN : isN TL VL NL c = true) : Lm LT LI TL VL NL c ∈ Mg LT LI TL VL NL :=
  Subgroup.subset_closure ⟨c, ⟨(isN_iff.1 hN).1, hN⟩, rfl⟩

theorem InM_letter {c : ℕ} (hN : isN TL VL NL c = true) : InM LT LI TL VL NL (let7 LT c) :=
  ⟨letter_C7 hc hL hN, _, Lm_mem hN, Lm_val hc hL hN⟩

theorem segProd_spec (Wd o : ℕ) : ∀ m, segProd LT TL VL NL Wd o m = 0 ∨
    ((∀ k < m, isN TL VL NL (byte Wd (o + k)) = true) ∧ InM LT LI TL VL NL (segProd LT TL VL NL Wd o m) ∧
      m7 (segProd LT TL VL NL Wd o m) = ((List.range m).map fun k => m7 (let7 LT (byte Wd (o + k)))).prod)
  | 0 => Or.inr ⟨fun k hk => absurd hk (Nat.not_lt_zero k), InM_one hc, by
      change m7 ONE7 = _
      rw [(one7 hc).2]
      rfl⟩
  | m + 1 => by
    have hs : segProd LT TL VL NL Wd o (m + 1) = Bool.rec (motive := fun _ => ℕ) 0
        (mul7 (segProd LT TL VL NL Wd o m) (let7 LT (byte Wd (o + m))))
        (isN TL VL NL (byte Wd (o + m))) := rfl
    rw [hs]
    cases hN : isN TL VL NL (byte Wd (o + m))
    · exact Or.inl rfl
    · dsimp only
      rcases segProd_spec Wd o m with h0 | ⟨h1, h2, h3⟩
      · left
        rw [h0, mul7_zero_left hc (letter_C7 hc hL hN)]
      · right
        refine ⟨fun k hk => ?_, InM_mul hc h2 (InM_letter hc hL hN), ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
          · exact h1 k hk
          · exact hN
        · rw [(mul7_sound hc h2.1 (letter_C7 hc hL hN)).2, h3, List.range_succ, List.map_append,
            List.prod_append, List.map_singleton, List.prod_singleton]

end Model

theorem hdrOK_spec {HB : ℕ → ℕ} {LT TL VL NL h d : ℕ} (hh : hdrOK HB LT TL VL NL h d = true) :
    mat HB h = ONE7 ∨ (∃ a, isN TL VL NL a = true ∧ mat HB h = let7 LT a) ∨
      (∃ a b, a < h ∧ b < h ∧ mat HB h = mul7 (mat HB a) (mat HB b)) ∨
      (∃ a, a < h ∧ validM7 (mat HB h) = true ∧ mul7 (mat HB h) (mat HB a) = ONE7) := by
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
          change andB (Nat.blt a h) (andB (validM7 H) (Nat.beq (mul7 H (mat HB a)) ONE7)) = true at hh
          obtain ⟨e1, r⟩ := andL_iff.1 hh
          obtain ⟨e2, e3⟩ := andL_iff.1 r
          exact Or.inr (Or.inr (Or.inr ⟨a, Nat.blt_eq.mp e1, e2, Nat.eq_of_beq_eq_true e3⟩))
      · intro hh
        change andB (Nat.blt a h) (andB (Nat.blt b h)
          (Nat.beq H (mul7 (mat HB a) (mat HB b)))) = true at hh
        obtain ⟨e1, r⟩ := andL_iff.1 hh
        obtain ⟨e2, e3⟩ := andL_iff.1 r
        exact Or.inr (Or.inr (Or.inl ⟨a, b, Nat.blt_eq.mp e1, Nat.blt_eq.mp e2,
          Nat.eq_of_beq_eq_true e3⟩))
    · intro hh
      change andB (isN TL VL NL a) (Nat.beq H (let7 LT a)) = true at hh
      obtain ⟨e1, e2⟩ := andL_iff.1 hh
      exact Or.inr (Or.inl ⟨a, e1, Nat.eq_of_beq_eq_true e2⟩)
  · intro hh
    change Nat.beq H ONE7 = true at hh
    exact Or.inl (Nat.eq_of_beq_eq_true hh)

section Header

variable {LT LI TL VL NL : ℕ} (hc : constsOK7 = true) (hL : LetOK LT LI TL VL NL)
include hc hL

theorem hdr_mem {HB : ℕ → ℕ} {Ch : List ℕ} {nH : ℕ}
    (hhdr : runHdr HB LT TL VL NL Ch 1 = nH + 1) : ∀ h < nH, InM LT LI TL VL NL (mat HB h) := by
  rw [runHdr_eq] at hhdr
  have hi := cntRun_spec (a := 0) hhdr
  intro h
  induction h using Nat.strong_induction_on with
  | _ h ih =>
    intro hh
    obtain ⟨J, hd⟩ := hi h (Nat.zero_le _) hh
    rcases hdrOK_spec hd with e | ⟨a, ha, e⟩ | ⟨a, b, ha, hb, e⟩ | ⟨a, ha, hv, e⟩
    · rw [e]
      exact InM_one hc
    · rw [e]
      exact InM_letter hc hL ha
    · rw [e]
      exact InM_mul hc (ih a ha (by omega)) (ih b hb (by omega))
    · exact InM_invL hc (ih a ha (by omega)) (valid7 hc hv) e

@[expose] noncomputable def gm (HB GB : ℕ → ℕ) (j : ℕ) : ℕ := mat HB (lo20 (e40 GB j))
@[expose] noncomputable def gi (HB GB : ℕ → ℕ) (j : ℕ) : ℕ := mat HB (hi20 (e40 GB j))

omit hc hL in
theorem gomOK_spec {HB GB OB : ℕ → ℕ} {I0 nH j h : ℕ} (hg : gomOK HB GB OB I0 nH j h = true) :
    lo20 (e40 GB j) < nH ∧ hi20 (e40 GB j) < nH ∧ actOK (pt OB I0) (gm HB GB j) (pt OB j) h = true ∧
      mul7 (gm HB GB j) (gi HB GB j) = ONE7 ∧ canonP (pt OB j) = true := by
  unfold gomOK at hg
  obtain ⟨e1, r⟩ := andL_iff.1 hg
  obtain ⟨e2, r⟩ := andL_iff.1 r
  obtain ⟨e3, r⟩ := andL_iff.1 r
  obtain ⟨e4, e5⟩ := andL_iff.1 r
  exact ⟨Nat.blt_eq.mp e1, Nat.blt_eq.mp e2, e3, Nat.eq_of_beq_eq_true e4, e5⟩

theorem gom_spec {HB GB OB : ℕ → ℕ} {Ch Cg : List ℕ} {nH NO I0 : ℕ}
    (hhdr : runHdr HB LT TL VL NL Ch 1 = nH + 1) (hgom : runGom HB GB OB I0 nH Cg 1 = NO + 1) :
    ∀ j < NO, InM LT LI TL VL NL (gm HB GB j) ∧ InM LT LI TL VL NL (gi HB GB j) ∧
      mul7 (gm HB GB j) (gi HB GB j) = ONE7 ∧ canonP (pt OB j) = true ∧
      ∃ h, actOK (pt OB I0) (gm HB GB j) (pt OB j) h = true := by
  rw [runGom_eq] at hgom
  have hi := cntRun_spec (a := 0) hgom
  have hm := hdr_mem hc hL hhdr
  intro j hj
  obtain ⟨J, hg⟩ := hi j (Nat.zero_le _) hj
  obtain ⟨h1, h2, h3, h4, h5⟩ := gomOK_spec hg
  refine ⟨hm _ h1, hm _ h2, h4, h5, _, h3⟩

end Header

theorem tOK_spec {TB OB RR : ℕ → ℕ} {LT TL VL NL NR nT I0 e d h : ℕ}
    (ht : tOK TB OB RR LT TL VL NL NR nT I0 e d h = true) :
    validM7 (tS TB e) = true ∧ validM7 (tP TB e) = true ∧ (∃ ep < nT, tP TB e = tS TB ep) ∧
      ((∃ a b, a < e ∧ b < e ∧ tS TB e = mul7 (tS TB a) (tS TB b) ∧
          tP TB e = mul7 (tP TB a) (tP TB b)) ∨
        (∃ r s ns, relVisOK RR LT TL VL NL NR (tS TB e) (tP TB e) r s ns = true ∧
          actOK (pt OB I0) (tS TB e) (pt OB I0) h = true)) := by
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

variable {LT LI TL VL NL : ℕ} (hc : constsOK7 = true) (hL : LetOK LT LI TL VL NL)
include hc hL

theorem tab_mem {TB OB RR : ℕ → ℕ} {NR nT I0 : ℕ} {Ct : List ℕ}
    (hT : runT TB OB RR LT TL VL NL NR nT I0 Ct 1 = nT + 1) (hθ : canonP (pt OB I0) = true) :
    ∀ e < nT, InM LT LI TL VL NL (tS TB e) ∧
      ∀ y : Mat7ˣ, (y : Mat7) = m7 (tS TB e) → actP (ptS (pt OB I0)) y = ptS (pt OB I0) := by
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
      refine ⟨eS ▸ InM_mul hc ma mb, fun y hy => ?_⟩
      obtain ⟨ya, -, eya⟩ := ma.2
      obtain ⟨yb, -, eyb⟩ := mb.2
      have e2 : y = ya * yb := by
        apply Units.ext
        rw [hy, eS, (mul7_sound hc ma.1 mb.1).2, Units.val_mul, eya, eyb]
      rw [e2, ← actP_mul, sa ya eya, sb yb eyb]
    · refine ⟨?_, fun y hy => actOK_sound hc hact hθ hθ (valid7 hc hS) hy⟩
      have eS := relVisOK_S hr
      rcases segProd_spec hc hL _ 1 ns with h0 | ⟨-, hm, -⟩
      · exact absurd (actOK_zero hc (eS.trans h0 ▸ hact) hθ hθ) id
      · rw [eS]
        exact hm

end Table

section Orbit

variable {LT LI TL VL NL : ℕ} (hc : constsOK7 = true) (hL : LetOK LT LI TL VL NL)
include hc hL

theorem orb {HB GB OB TB RR : ℕ → ℕ} {Ch Cg Ct Os TSs : List ℕ} {nH NO I0 NR nT NORD qO qT O1 T1 : ℕ}
    (hfin : Finite (Mg LT LI TL VL NL)) (hcard : Nat.card (Mg LT LI TL VL NL) ≤ NORD)
    (hhdr : runHdr HB LT TL VL NL Ch 1 = nH + 1) (hgom : runGom HB GB OB I0 nH Cg 1 = NO + 1)
    (hT : runT TB OB RR LT TL VL NL NR nT I0 Ct 1 = nT + 1) (hI0 : I0 < NO)
    (hO : runSorted (pt OB) qO NO Os 1 = O1) (hO1 : sortedCount O1 = NO)
    (hTs : runSorted (tS TB) qT nT TSs 1 = T1) (hT1 : sortedCount T1 = nT) (hnord : nT * NO = NORD) :
    DceTw.Orb (Mg LT LI TL VL NL) NORD Pt actP (ptS (pt OB I0)) (fun j => ptS (pt OB j))
      (fun j => mEl LT LI TL VL NL (gm HB GB j)) NO I0 (fun e => mEl LT LI TL VL NL (tS TB e)) nT := by
  have hg := gom_spec hc hL hhdr hgom
  have hθ : canonP (pt OB I0) = true := (hg I0 hI0).2.2.2.1
  have htab := tab_mem hc hL hT hθ
  have hpt : ∀ w, pt OB w < 2 ^ 336 := fun w => by
    unfold pt
    change rec OB 6 336 w &&& M336 < 2 ^ 336
    rw [show M336 = 2 ^ 336 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨-, injO⟩ := sortRun_spec (runSorted_eq _ _ _ _ _ ▸ hO) hO1
  obtain ⟨-, injT⟩ := sortRun_spec (runSorted_eq _ _ _ _ _ ▸ hTs) hT1
  refine ⟨hfin, hcard, actP_one, actP_mul, fun j hj => ?_, fun j hj j' hj' e => ?_, hI0, rfl,
    fun e he => ?_, fun e he e' he' h => ?_, hnord⟩
  · obtain ⟨hm, -, -, hcan, h, hact⟩ := hg j hj
    exact actOK_sound hc hact hθ hcan hm.1 (mEl_val hm)
  · exact injO j hj j' hj' (ptS_inj hc (hg j hj).2.2.2.1 (hg j' hj').2.2.2.1 (hpt j) (hpt j') e)
  · exact (htab e he).2 _ (mEl_val (htab e he).1)
  · have h2 : (((mEl LT LI TL VL NL (tS TB e) : Mg LT LI TL VL NL) : Mat7ˣ) : Mat7) =
        (((mEl LT LI TL VL NL (tS TB e') : Mg LT LI TL VL NL) : Mat7ˣ) : Mat7) := by rw [h]
    rw [mEl_val (htab e he).1, mEl_val (htab e' he').1] at h2
    exact injT e he e' he' (m7_inj (htab e he).1.1 (htab e' he').1.1 h2)

end Orbit

end CFSG.Certificates.DS5

end
