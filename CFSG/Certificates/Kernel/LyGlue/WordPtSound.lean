module

public import Certificates.Data.Kernel.LyGlue.Defs
public import CFSG.Sporadic.Recognition.LyonsModelPerm

public section

namespace CFSG.KC.LyGlue

open CFSG.Sporadic.Recognition.LyonsSims Equiv

@[expose] noncomputable def letPt (cF dF : Nat → Nat) (l : Int) (a : Nat) : Nat :=
  letE cF dF (lcode l) a

theorem lcode_lt (l : Int) : lcode l < 4 := by
  cases l with
  | ofNat k =>
    change Bool.rec (motive := fun _ => Nat) 2 0 (Nat.beq k 1) < 4
    cases Nat.beq k 1 <;> decide
  | negSucc k =>
    change Bool.rec (motive := fun _ => Nat) 3 1 (Nat.beq k 0) < 4
    cases Nat.beq k 0 <;> decide

theorem encW_append (ws : List Int) (l : Int) : encW (ws ++ [l]) = encW ws * 4 + lcode l := by
  unfold encW
  rw [List.foldl_append]
  rfl

theorem wptE_succ (cF dF : Nat → Nat) (n c a : Nat) :
    wptE cF dF (n + 1) c a = wptE cF dF n (Nat.shiftRight c 2) (letE cF dF (Nat.land c 3) a) :=
  rfl

theorem wptE_eq (cF dF : Nat → Nat) (ws : List Int) (a : Nat) :
    wptE cF dF ws.length (encW ws) a = ws.foldr (fun l b => letPt cF dF l b) a := by
  induction ws using List.reverseRecOn generalizing a with
  | nil => rfl
  | append_singleton ws l ih =>
    rw [List.length_append, List.length_singleton, wptE_succ, encW_append, List.foldr_append,
      List.foldr_cons, List.foldr_nil]
    have h1 : Nat.shiftRight (encW ws * 4 + lcode l) 2 = encW ws := by
      change (encW ws * 4 + lcode l) >>> 2 = encW ws
      rw [Nat.shiftRight_eq_div_pow]
      have := lcode_lt l
      omega
    have h2 : Nat.land (encW ws * 4 + lcode l) 3 = lcode l := by
      change (encW ws * 4 + lcode l) &&& (2 ^ 2 - 1) = lcode l
      rw [Nat.and_two_pow_sub_one_eq_mod]
      have := lcode_lt l
      omega
    rw [h1, h2, ih]
    rfl

theorem wptE_wG {cF dF : Nat → Nat} (hcF : ∀ a : Fin Ly0.deg, cF a = (Ly0.cG a : Nat))
    (hdF : ∀ a : Fin Ly0.deg, dF a = (Ly0.dG a : Nat)) (hc2 : Ly0.cG * Ly0.cG = 1)
    (hd3 : Ly0.dG ^ 3 = 1) (ws : List Int) (hws : ∀ l ∈ ws, l ≠ 0 ∧ l.natAbs ≤ 2)
    (a : Fin Ly0.deg) : wptE cF dF ws.length (encW ws) a = (Ly0.wG Ly0.gens0 ws a : Nat) := by
  rw [wptE_eq]
  induction ws with
  | nil => rw [List.foldr_nil, Ly0.wG_nil]; rfl
  | cons l ws ih =>
    have hl := hws l List.mem_cons_self
    have ih' := ih (fun l' hl' => hws l' (List.mem_cons_of_mem _ hl'))
    rw [List.foldr_cons, ih', Ly0.wG_cons, Perm.mul_apply]
    set b := Ly0.wG Ly0.gens0 ws a
    have hci : Ly0.cG⁻¹ = Ly0.cG := inv_eq_of_mul_eq_one_right hc2
    have hdi : Ly0.dG⁻¹ = Ly0.dG * Ly0.dG := by
      rw [inv_eq_iff_mul_eq_one, pow_three] at *
      rw [← mul_assoc]
      exact hd3
    have hcases : l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · change cF b = _
      rw [hcF, Ly0.letterG_pos _ (by norm_num), show ((1 : ℤ) - 1).toNat = 0 from rfl,
        Ly0.gens0_zero]
    · change cF b = _
      rw [hcF, Ly0.letterG_neg_of _ (by norm_num)]
      change _ = ((Ly0.gens0 0)⁻¹ b : Nat)
      rw [Ly0.gens0_zero, hci]
    · change dF b = _
      rw [hdF, Ly0.letterG_pos _ (by norm_num), show ((2 : ℤ) - 1).toNat = 1 from rfl,
        Ly0.gens0_one]
    · change dF (dF b) = _
      rw [hdF, hdF, Ly0.letterG_neg_of _ (by norm_num)]
      change _ = ((Ly0.gens0 1)⁻¹ b : Nat)
      rw [Ly0.gens0_one, hdi, Perm.mul_apply]

end CFSG.KC.LyGlue

end
