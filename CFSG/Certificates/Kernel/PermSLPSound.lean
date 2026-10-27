module

public import Certificates.Data.Kernel.PermSLP
public import CFSG.Certificates.Kernel.PermToolSound
public import CFSG.Certificates.Kernel.Spor.MulHCaySound
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KC.PermSLP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.MulHCay

variable {n w : Nat} {S SI : Nat → Nat}

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

@[expose] noncomputable def letV (S SI : Nat → Nat) (z : Int) : Nat :=
  nIf(Nat.beq (Nat.land (CFSG.KS.Mathieu.icode z) (nat_lit 1)) (nat_lit 0),
    S (Nat.sub (Nat.shiftRight (CFSG.KS.Mathieu.icode z) (nat_lit 1)) (nat_lit 1)),
    SI (Nat.sub (Nat.shiftRight (CFSG.KS.Mathieu.icode z) (nat_lit 1)) (nat_lit 1)))

theorem wordK_cons' {m idn : Nat} (z : Int) (l : List Int) :
    wordK n w m idn S SI (z :: l) = pcomp n w m (letV S SI z) (wordK n w m idn S SI l) := by
  rw [CFSG.KC.PermTool.wordK_cons, strictN_eq', strictN_eq']
  rfl

theorem canonK_letV (hS : ∀ j, canonK n w (mask w) (n * w) (S j) = true)
    (hSI : ∀ j, canonK n w (mask w) (n * w) (SI j) = true) (z : Int) :
    canonK n w (mask w) (n * w) (letV S SI z) = true := by
  unfold letV
  cases Nat.beq (Nat.land (CFSG.KS.Mathieu.icode z) 1) 0
  · exact hSI _
  · exact hS _

theorem canonK_wordK (hS : ∀ j, canonK n w (mask w) (n * w) (S j) = true)
    (hSI : ∀ j, canonK n w (mask w) (n * w) (SI j) = true) {acc : Nat}
    (hacc : canonK n w (mask w) (n * w) acc = true) :
    ∀ u : List Int, canonK n w (mask w) (n * w) (wordK n w (mask w) acc S SI u) = true
  | [] => hacc
  | z :: u => by
    rw [wordK_cons']
    exact canonK_pcomp (canonK_letV hS hSI z) (canonK_wordK hS hSI hacc u)

theorem wordK_acc (hS : ∀ j, canonK n w (mask w) (n * w) (S j) = true)
    (hSI : ∀ j, canonK n w (mask w) (n * w) (SI j) = true) {acc : Nat}
    (hacc : canonK n w (mask w) (n * w) acc = true) :
    ∀ u : List Int, wordK n w (mask w) acc S SI u =
      pcomp n w (mask w) (wordK n w (mask w) (pidn n w) S SI u) acc
  | [] => (pcomp_id_c hacc).2.symm
  | z :: u => by
    rw [wordK_cons', wordK_cons', wordK_acc hS hSI hacc u,
      pcomp_assoc_c (canonK_letV hS hSI z) hacc]

theorem appK_eq (a b : List Int) : appK a b = a ++ b := by
  induction a with
  | nil => rfl
  | cons x a ih =>
    change x :: appK a b = _
    rw [ih, List.cons_append]

theorem symE_sound {nL R : Nat} {V G : Nat → Nat}
    (hS : ∀ j, canonK n w (mask w) (n * w) (S j) = true)
    (hSI : ∀ j, canonK n w (mask w) (n * w) (SI j) = true)
    (hid : canonK n w (mask w) (n * w) (pidn n w) = true)
    (hl : ∀ s < nL, letK n w nL S SI V s = true)
    (hr : ∀ k < R, ruleK n w nL S SI V G k = true) :
    ∀ f s, s < f → s < nL + R →
      wordK n w (mask w) (pidn n w) S SI (symE nL G f s) = symV nL S SI V s := by
  intro f
  induction f with
  | zero => intro s hs; exact absurd hs (Nat.not_lt_zero s)
  | succ f ih =>
    intro s hs hsR
    have e : symE nL G (f + 1) s = Bool.rec (motive := fun _ => List Int)
        (appK (symE nL G f (lo (G (Nat.sub s nL)))) (symE nL G f (hi (G (Nat.sub s nL)))))
        [letZ s] (Nat.blt s nL) := rfl
    rw [e]
    cases hb : Nat.blt s nL
    · have hge : nL ≤ s := by
        rcases Nat.lt_or_ge s nL with h | h
        · rw [Nat.blt_eq.mpr h] at hb
          exact Bool.noConfusion hb
        · exact h
      have hk : Nat.sub s nL < R := by
        change s - nL < R
        omega
      have hrk := hr (Nat.sub s nL) hk
      unfold ruleK at hrk
      rw [bAnd_iff, bAnd_iff] at hrk
      obtain ⟨ha, hb', hv⟩ := hrk
      have es : Nat.add nL (Nat.sub s nL) = s := Nat.add_sub_cancel' hge
      have ha' := Nat.blt_eq.mp ha
      have hb'' := Nat.blt_eq.mp hb'
      rw [es] at ha' hb''
      have hfs : s ≤ f := Nat.lt_succ_iff.mp hs
      have hsv : symV nL S SI V s = V (Nat.sub s nL) := by
        unfold symV
        rw [hb]
      change wordK n w (mask w) (pidn n w) S SI
        (appK (symE nL G f (lo (G (Nat.sub s nL)))) (symE nL G f (hi (G (Nat.sub s nL))))) = _
      rw [appK_eq, CFSG.KC.PermTool.wordK_append,
        wordK_acc hS hSI (canonK_wordK hS hSI hid _),
        ih (lo (G (Nat.sub s nL))) (Nat.lt_of_lt_of_le ha' hfs) (Nat.lt_trans ha' hsR),
        ih (hi (G (Nat.sub s nL))) (Nat.lt_of_lt_of_le hb'' hfs) (Nat.lt_trans hb'' hsR), hsv]
      exact Nat.eq_of_beq_eq_true hv
    · exact Nat.eq_of_beq_eq_true (hl s (Nat.blt_eq.mp hb))

theorem slp_word {nL R f t : Nat} {V G : Nat → Nat} {wd : List Int}
    (hS : ∀ j, canonK n w (mask w) (n * w) (S j) = true)
    (hSI : ∀ j, canonK n w (mask w) (n * w) (SI j) = true)
    (hid : canonK n w (mask w) (n * w) (pidn n w) = true)
    (hl : ∀ s < nL, letK n w nL S SI V s = true)
    (hr : ∀ k < R, ruleK n w nL S SI V G k = true) (hf : nL + R ≤ f)
    (ht : topK nL R f G t wd = true) :
    wordK n w (mask w) (pidn n w) S SI wd = symV nL S SI V t := by
  unfold topK at ht
  rw [bAnd_iff] at ht
  obtain ⟨h1, h2⟩ := ht
  have h1' : t < nL + R := Nat.blt_eq.mp h1
  rw [← eq_of_beq h2]
  exact symE_sound hS hSI hid hl hr f t (Nat.lt_of_lt_of_le h1' hf) h1'

end CFSG.KC.PermSLP

end
