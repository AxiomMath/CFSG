module

public import Certificates.Data.Kernel.CycTabW
public import CFSG.Certificates.Kernel.CycTabSound

public section

namespace CFSG.KC.CycTabW

open Equiv CFSG.KC.CycTab

@[expose] def LetterOKW {n k : Nat} (w TT : Nat) (G : Fin k → Perm (Fin n)) : Prop :=
  ∀ (l : Fin k × Bool) (x : Fin n), (letter G l x).val = fgW w TT (codeW l * n + x.val)

variable {n : Nat}

theorem tabOKW_spec {w TT i : Nat} {F : Nat → Nat} (h : tabOKW n w TT i F = true)
    {g : Perm (Fin n)} (hg : ∀ x : Fin n, (g x).val = F x.val) (x : Fin n) :
    (g x).val = fgW w TT (2 * i * n + x.val) ∧
      (g⁻¹ x).val = fgW w TT ((2 * i + 1) * n + x.val) := by
  have H := (allLtK_iff _ n).1 h
  have hp : ∀ y : Fin n, fgW w TT (2 * i * n + y.val) = F y.val ∧
      fgW w TT ((2 * i + 1) * n + y.val) < n ∧
      fgW w TT (2 * i * n + fgW w TT ((2 * i + 1) * n + y.val)) = y.val := by
    intro y
    have := H y.val y.isLt
    rw [brec_and, brec_and] at this
    simp only [Nat.beq_eq, Nat.blt_eq] at this
    exact ⟨this.1, this.2.1, this.2.2⟩
  refine ⟨?_, ?_⟩
  · rw [hg, (hp x).1]
  · obtain ⟨-, hlt, hfix⟩ := hp x
    have hy : g ⟨_, hlt⟩ = x := by
      apply Fin.ext
      rw [hg, ← (hp ⟨_, hlt⟩).1]
      exact hfix
    rw [Perm.inv_eq_iff_eq.2 hy.symm]

theorem tabsW_sound {w TT k : Nat} {F : Nat → Nat → Nat} (h : tabsOKW n w TT F k = true)
    {G : Fin k → Perm (Fin n)} (hG : ∀ (i : Fin k) (x : Fin n), (G i x).val = F i.val x.val) :
    LetterOKW w TT G := by
  rintro ⟨i, b⟩ x
  have hi := (allLtK_iff _ k).1 h i.val i.isLt
  have := tabOKW_spec hi (hG i) x
  cases b
  · simp only [letter, Bool.cond_false, codeW]
    exact this.2
  · simp only [letter, Bool.cond_true, codeW, Nat.add_zero]
    exact this.1

theorem wordW_val {w TT k : Nat} {G : Fin k → Perm (Fin n)} (hL : LetterOKW w TT G) (x : Fin n) :
    ∀ ws : List (Fin k × Bool),
      ((ws.map (letter G)).prod x).val = wordW n w TT (ws.map codeW) x.val
  | [] => by simp [wordW]
  | l :: ws => by
    rw [List.map_cons, List.prod_cons, Perm.mul_apply, hL, wordW_val hL x ws]
    rfl

theorem eqOKW_sound {w TT k : Nat} {G : Fin k → Perm (Fin n)} (hL : LetterOKW w TT G)
    {ws : List (Fin k × Bool)} {F : Nat → Nat} (h : eqOKW n w TT (ws.map codeW) F = true)
    (x : Fin n) : ((ws.map (letter G)).prod x).val = F x.val := by
  rw [wordW_val hL]
  exact Nat.eq_of_beq_eq_true ((allLtK_iff _ n).1 h x.val x.isLt)

theorem onesOKW_spec {w TT : Nat} : ∀ {RS : List (List Nat)}, onesOKW n w TT RS = true →
    ∀ v ∈ RS, eqOKW n w TT v (fun x => x) = true
  | [], _ => by simp
  | v :: RS, h => by
    change Bool.rec (motive := fun _ => Bool) false (onesOKW n w TT RS)
      (eqOKW n w TT v fun x => x) = true at h
    rw [brec_and] at h
    intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact h.1
    · exact onesOKW_spec h.2 u hu

theorem onesOKW_sound {w TT k : Nat} {G : Fin k → Perm (Fin n)} (hL : LetterOKW w TT G)
    {RS : List (List Nat)} (h : onesOKW n w TT RS = true) (ws : List (Fin k × Bool))
    (hw : ws.map codeW ∈ RS) : (ws.map (letter G)).prod = 1 := by
  ext x
  rw [eqOKW_sound hL (onesOKW_spec h _ hw) x]
  rfl

theorem ne_one_of_eqOKW {w TT k : Nat} {G : Fin k → Perm (Fin n)} (hL : LetterOKW w TT G)
    {ws : List (Fin k × Bool)} (h : eqOKW n w TT (ws.map codeW) (fun x => x) = false) :
    (ws.map (letter G)).prod ≠ 1 := by
  intro h1
  have : eqOKW n w TT (ws.map codeW) (fun x => x) = true := by
    refine (allLtK_iff _ n).2 fun x hx => ?_
    have hv := wordW_val hL ⟨x, hx⟩ ws
    rw [h1] at hv
    rw [← hv]
    exact Nat.beq_refl x
  rw [this] at h
  exact absurd h (by decide)

end CFSG.KC.CycTabW

end
