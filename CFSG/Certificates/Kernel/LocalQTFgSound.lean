module

public import Certificates.Data.Kernel.LocalQT.SylL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22TCheckInputs

import CFSG.Certificates.Kernel.LocalQTSylProved
public import CFSG.Certificates.Kernel.LocalQTWordSound

public section

namespace CFSG.KC.LQT.Syl

open Equiv CFSG.QuasithinUnique.Setup.X1 CFSG.KC.LQT.W CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.Blueprint

open CFSG.KC.LQT.Syl.Pf CFSG.KC.Ord in
private theorem fg_aux {cA cB : ℕ} (hA : codeP ((m22a : _) : Perm (Fin 22)) = cA)
    (hB : codeP ((m22b : _) : Perm (Fin 22)) = cB) :
    ∀ FG : List (ℕ × ℕ × List ℤ × List ℤ × List ℤ),
    fgK 22 cA cB (m22rl.map (cH NativeSporadic.M22)) FG = true → fgOK FG = true
  | [] => fun _ => rfl
  | f :: FG => fun h => by
    have hn : (22 : ℕ) ≤ 32 := by decide
    change andB (CFSG.KC.LQT.P.letB _ _) (fgK 22 cA cB _ FG) = true at h
    rw [P.andB_iff] at h
    obtain ⟨h1, h2⟩ := h
    have ih := fg_aux hA hB FG h2
    rw [P.letB_eq, zk_eq m22a m22b hn hA hB, P.andB_iff, getK_H, getK_H] at h1
    obtain ⟨h3, h4⟩ := h1
    rw [cH_conj hn, cH_conj hn] at h3 h4
    have hL : [cH NativeSporadic.M22 (m22rl.getD f.1 1), cH NativeSporadic.M22 (m22rl.getD f.2.1 1),
        cH NativeSporadic.M22 (evalN NativeSporadic.M22 [m22a, m22b] f.2.2.1 * m22rl.getD f.1 1 *
          (evalN NativeSporadic.M22 [m22a, m22b] f.2.2.1)⁻¹),
        cH NativeSporadic.M22 (evalN NativeSporadic.M22 [m22a, m22b] f.2.2.1 * m22rl.getD f.2.1 1 *
          (evalN NativeSporadic.M22 [m22a, m22b] f.2.2.1)⁻¹)] = [m22rl.getD f.1 1, m22rl.getD f.2.1 1,
        evalN NativeSporadic.M22 [m22a, m22b] f.2.2.1 * m22rl.getD f.1 1 *
          (evalN NativeSporadic.M22 [m22a, m22b] f.2.2.1)⁻¹,
        evalN NativeSporadic.M22 [m22a, m22b] f.2.2.1 * m22rl.getD f.2.1 1 *
          (evalN NativeSporadic.M22 [m22a, m22b] f.2.2.1)⁻¹].map (cH NativeSporadic.M22) := rfl
    rw [hL, evalZK_H hn] at h3 h4
    have e1 : cA = cH NativeSporadic.M22 m22a := hA.symm
    have e2 : cB = cH NativeSporadic.M22 m22b := hB.symm
    rw [e1, beq_cH hn] at h3
    rw [e2, beq_cH hn] at h4
    unfold fgOK
    rw [List.all_cons, Bool.and_eq_true]
    refine ⟨?_, ih⟩
    rw [Bool.and_eq_true]
    exact ⟨beq_iff_eq.2 h3, beq_iff_eq.2 h4⟩

theorem fg_sound {cA cB : ℕ} (hA : codeP ((m22a : _) : Perm (Fin 22)) = cA)
    (hB : codeP ((m22b : _) : Perm (Fin 22)) = cB)
    (FG : List (ℕ × ℕ × List ℤ × List ℤ × List ℤ))
    (h : fgK 22 cA cB (rlK 22 cA cB m22RGens m22RWords) FG = true) : fgOK FG = true := by
  have hn : (22 : ℕ) ≤ 32 := by decide
  have hr : rlK 22 cA cB m22RGens m22RWords = m22rl.map (Pf.cH NativeSporadic.M22) :=
    Pf.rlK_eq m22a m22b hn hA hB m22RGens m22RWords
  rw [hr] at h
  exact fg_aux hA hB FG h

end CFSG.KC.LQT.Syl

end
