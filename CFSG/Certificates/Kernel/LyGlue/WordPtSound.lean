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

theorem letPt_c1 {cF dF : Nat → Nat} (hcF : ∀ a : Fin Ly0.deg, cF a = (Ly0.cG a : Nat))
    (b : Fin Ly0.deg) : letPt cF dF 1 b = (Ly0.letterG Ly0.gens0 1 b : Nat) := by
  have e : letPt cF dF 1 b = cF b := rfl
  rw [e, hcF, Ly0.letterG_pos _ (by norm_num), show ((1 : ℤ) - 1).toNat = 0 from rfl,
    Ly0.gens0_zero]

theorem letPt_cm1 {cF dF : Nat → Nat} (hcF : ∀ a : Fin Ly0.deg, cF a = (Ly0.cG a : Nat))
    (hci : Ly0.cG⁻¹ = Ly0.cG) (b : Fin Ly0.deg) :
    letPt cF dF (-1) b = (Ly0.letterG Ly0.gens0 (-1) b : Nat) := by
  have e : letPt cF dF (-1) b = cF b := rfl
  rw [e, hcF, Ly0.letterG_neg_of _ (by norm_num), show (-(-1 : ℤ) - 1).toNat = 0 from rfl,
    Ly0.gens0_zero, hci]

theorem letPt_d1 {cF dF : Nat → Nat} (hdF : ∀ a : Fin Ly0.deg, dF a = (Ly0.dG a : Nat))
    (b : Fin Ly0.deg) : letPt cF dF 2 b = (Ly0.letterG Ly0.gens0 2 b : Nat) := by
  have e : letPt cF dF 2 b = dF b := rfl
  rw [e, hdF, Ly0.letterG_pos _ (by norm_num), show ((2 : ℤ) - 1).toNat = 1 from rfl,
    Ly0.gens0_one]

theorem letPt_dm1 {cF dF : Nat → Nat} (hdF : ∀ a : Fin Ly0.deg, dF a = (Ly0.dG a : Nat))
    (hdi : Ly0.dG⁻¹ = Ly0.dG * Ly0.dG) (b : Fin Ly0.deg) :
    letPt cF dF (-2) b = (Ly0.letterG Ly0.gens0 (-2) b : Nat) := by
  have e : letPt cF dF (-2) b = dF (dF b) := rfl
  rw [e, hdF, hdF, Ly0.letterG_neg_of _ (by norm_num), show (-(-2 : ℤ) - 1).toNat = 1 from rfl,
    Ly0.gens0_one, hdi, Perm.mul_apply]

theorem ly_dinv (hd3 : Ly0.dG ^ 3 = 1) : Ly0.dG⁻¹ = Ly0.dG * Ly0.dG := by
  rw [inv_eq_iff_mul_eq_one, ← mul_assoc]
  rw [pow_three, ← mul_assoc] at hd3
  exact hd3

theorem wptE_nil (cF dF : Nat → Nat) (a : Fin Ly0.deg) :
    ([] : List Int).foldr (fun l b => letPt cF dF l b) (a : Nat) = (Ly0.wG Ly0.gens0 [] a : Nat) := by
  rw [List.foldr_nil, Ly0.wG_nil, Perm.one_apply]

theorem wptE_cons {cF dF : Nat → Nat} (hcF : ∀ a : Fin Ly0.deg, cF a = (Ly0.cG a : Nat))
    (hdF : ∀ a : Fin Ly0.deg, dF a = (Ly0.dG a : Nat)) (hci : Ly0.cG⁻¹ = Ly0.cG)
    (hdi : Ly0.dG⁻¹ = Ly0.dG * Ly0.dG) (l : Int) (ws : List Int) (hl : l ≠ 0 ∧ l.natAbs ≤ 2)
    (a : Fin Ly0.deg)
    (ih : ws.foldr (fun l b => letPt cF dF l b) (a : Nat) = (Ly0.wG Ly0.gens0 ws a : Nat)) :
    (l :: ws).foldr (fun l b => letPt cF dF l b) (a : Nat) =
      (Ly0.wG Ly0.gens0 (l :: ws) a : Nat) := by
  rw [List.foldr_cons, ih, Ly0.wG_cons, Perm.mul_apply]
  have hcases : l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · exact letPt_c1 hcF _
  · exact letPt_cm1 hcF hci _
  · exact letPt_d1 hdF _
  · exact letPt_dm1 hdF hdi _

theorem wptE_wG {cF dF : Nat → Nat} (hcF : ∀ a : Fin Ly0.deg, cF a = (Ly0.cG a : Nat))
    (hdF : ∀ a : Fin Ly0.deg, dF a = (Ly0.dG a : Nat)) (hc2 : Ly0.cG * Ly0.cG = 1)
    (hd3 : Ly0.dG ^ 3 = 1) (ws : List Int) (hws : ∀ l ∈ ws, l ≠ 0 ∧ l.natAbs ≤ 2)
    (a : Fin Ly0.deg) : wptE cF dF ws.length (encW ws) a = (Ly0.wG Ly0.gens0 ws a : Nat) := by
  have hci : Ly0.cG⁻¹ = Ly0.cG := inv_eq_of_mul_eq_one_right hc2
  have hdi := ly_dinv hd3
  rw [wptE_eq]
  induction ws with
  | nil => exact wptE_nil cF dF a
  | cons l ws ih =>
    exact wptE_cons hcF hdF hci hdi l ws (hws l List.mem_cons_self) a
      (ih fun l' hl' => hws l' (List.mem_cons_of_mem _ hl'))

end CFSG.KC.LyGlue

end
