module

public import CFSG.CGT.L5R.R3Inputs
public import CFSG.CGT.M24R.L2Enum

public section

namespace CFSG.CGT.L5R.R3

open CFSG.CGT.M24R CFSG.Sporadic.Th.Native

theorem identCheck_spec (h : identCheck = true) :
    tEq (thExp uD) (dExp uD) = true ∧ tEq (nW ++ dExp uD ++ inv10 nW) bW = true ∧
      tEq (dExp bD) bW = true ∧ tEq (thExp bD) dAW = true ∧ tEq dAW [] = false ∧
      ∀ j, tEq (dExp (yD j)) (yW j) = true ∧
        tEq (inv10 nW ++ thExp (yD j) ++ nW) (dExp (a1D j)) = true ∧
        tEq (nW ++ thExp (a1D j) ++ inv10 nW) (dExp (b1D j)) = true ∧
        tEq (thExp (b1D j)) (fW j) = true ∧ tEq (inv10 wW ++ yW j ++ wW) (fW j) = true := by
  simpa only [identCheck, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
    List.mem_finRange, true_implies, and_assoc] using h

section Tab


theorem n8_eq_of_tEq (hcard : Nat.card N8 = 322560) {w w' : N0Word} (h : tEq w w' = true) :
    n8 w = n8 w' :=
  (isTab_wTab w).eq_of_eq hcard (by rw [beq_iff_eq.1 h]; exact isTab_wTab w')

theorem n8_ne_of_tEq {w w' : N0Word} (h : tEq w w' = false) : n8 w ≠ n8 w' := by
  intro e
  have h1 := isTab_wTab w
  rw [e] at h1
  have := table_eq_of_rep h1 (isTab_wTab w') (wTab_size w) (wTab_size w')
  simp [tEq, this] at h

theorem eq_one_of_commute (hc : centCheck (mkCtx ()) = true) (hcard : Nat.card N8 = 322560)
    {z : N8} (h₁ : z * n8 (yW 0) = n8 (yW 0) * z) (h₂ : z * n8 (yW 1) = n8 (yW 1) * z) :
    z = 1 := by
  obtain ⟨c, hcm, rfl⟩ := el_surj hcard z
  have hX : IsTab ((mkCtx ()).tab c) (el c) := isTab_tab (mem_codes.1 hcm).1
  have e₁ := (hX.commT_iff hcard (isTab_wTab (yW 0))).2 h₁
  have e₂ := (hX.commT_iff hcard (isTab_wTab (yW 1))).2 h₂
  simp only [centCheck, List.all_eq_true] at hc
  have h := hc c hcm
  rw [e₁, e₂, Bool.and_self, Bool.not_true, Bool.false_or, beq_iff_eq] at h
  rw [h] at hX
  exact hX.eq_of_eq hcard IsTab.one

end Tab

end CFSG.CGT.L5R.R3
