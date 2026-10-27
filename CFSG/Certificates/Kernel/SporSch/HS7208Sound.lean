module

public import Certificates.Data.Kernel.SporSch.HS7208K
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound

public section

namespace CFSG.KS.HS7208

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch

theorem bIf_then {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true)
    (hc : c = true) : t = true := by
  subst hc
  exact h

theorem bIf_other {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true)
    (hc : c = false) : e = true := by
  subst hc
  exact h

theorem memN_iff (i : Nat) : ∀ l : List Nat, memN i l = true ↔ i ∈ l
  | [] => by simp [memN]
  | a :: l => by
    have e : memN i (a :: l) = bIf(Nat.beq a i, true, memN i l) := rfl
    rw [e, List.mem_cons, ← memN_iff i l]
    cases h : Nat.beq a i
    · have hne : i ≠ a := fun he => by
        have h2 : Nat.beq a i = true := Nat.beq_eq.mpr he.symm
        rw [h] at h2
        exact Bool.noConfusion h2
      change memN i l = true ↔ i = a ∨ memN i l = true
      simp [hne]
    · change true = true ↔ i = a ∨ memN i l = true
      simp [(Nat.eq_of_beq_eq_true h).symm]

theorem ncW_spec {n : Nat} {f g : Nat → Nat} {p : Nat} (h : ncW n f g p = true)
    {x y : Equiv.Perm (Fin n)} (hf : RepF n f x) (hg : RepF n g y) : x * y ≠ y * x := by
  have h' : bAnd(Nat.blt p n, bIf(Nat.beq (f (g p)) (g (f p)), false, true)) = true := h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
  have hp : p < n := Nat.blt_eq.mp h1
  intro e
  have e1 : f (g p) = g (f p) := by
    have r1 := (hf.comp hg) p hp
    have r2 := (hg.comp hf) p hp
    rw [e] at r1
    exact r1.trans r2.symm
  rw [Nat.beq_eq.mpr e1] at h2
  exact Bool.noConfusion h2

theorem ordK_lt {n : Nat} {K : Nat → Nat} (h : ∀ i < n, ordK n K i = true) :
    ∀ i j, i < j → j < n → K i < K j := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    have hs : K j < K (j + 1) := by
      have h1 : bIf(Nat.blt (Nat.succ j) n, Nat.blt (K j) (K (Nat.succ j)), true) = true :=
        h j (by omega)
      have e : Nat.blt (Nat.succ j) n = true := Nat.blt_eq.mpr hj
      exact Nat.blt_eq.mp (bIf_then h1 e)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hij | rfl
    · exact lt_trans (ih hij (by omega)) hs
    · exact hs

theorem ordK_inj {n : Nat} {K : Nat → Nat} (h : ∀ i < n, ordK n K i = true) :
    ∀ i < n, ∀ j < n, K i = K j → i = j := by
  intro i hi j hj e
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact absurd e (ne_of_lt (ordK_lt h i j hlt hj))
  · exact heq
  · exact absurd e.symm (ne_of_lt (ordK_lt h j i hgt hi))

end CFSG.KS.HS7208

end
